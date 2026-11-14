import Jihoo.NativeCodeKinds

/-! Abstract representation information starts at an actual local lookup and
follows only its authenticated first-order U64 kind telescope. In particular,
inferring Type0 for an arbitrary term does not classify it as an abstract type. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds

inductive Spine (env : Environment) (ctx : Context) : Term → Kind → Prop where
  | var : LookupKind env ctx index kind → Spine env ctx (.var index) kind
  | app : Spine env ctx function (.index erased result) →
      Checker.check fuel env ctx true argument .u64 = true →
      Spine env ctx (.app function argument) result

def spine : Nat → Environment → Context → Term → Option Kind
  | 0, _, _, _ => none
  | fuel + 1, env, ctx, term => match term with
      | .var index => lookupKind fuel env ctx index
      | .app function argument => do
          let kind ← spine fuel env ctx function
          match kind with
          | .index _ result =>
              if Checker.check fuel env ctx true argument .u64 then some result else none
          | _ => none
      | _ => none

theorem spine_sound (h : spine fuel env ctx term = some kind) : Spine env ctx term kind := by
  induction fuel generalizing term kind with
  | zero => simp [spine] at h
  | succ fuel ih =>
      simp only [spine] at h
      split at h
      · exact .var (lookupKind_sound h)
      · rename_i function argument
        cases first : spine fuel env ctx function with
        | none => simp [first] at h
        | some headKind =>
            simp only [first, Bind.bind, Option.bind] at h
            cases headKind with
            | type => contradiction
            | index erased result =>
                simp only at h
                split at h
                · rename_i checked
                  cases h
                  exact .app (ih first) checked
                · contradiction
      · contradiction

theorem Spine.typed (h : Spine env ctx term kind) : HasType env ctx true term kind.term := by
  induction h with
  | var found => exact found.choose_spec.2.2
  | @app function erased result fuel argument head checked ih =>
      have resultType : result.term.subst (fun | 0 => argument | n + 1 => .var n) = result.term :=
        Kind.subst _ _
      exact resultType ▸ HasType.app ih (by simpa using Checker.check_sound checked) (Or.inl rfl)

/-- Zero remaining indices means the term denotes an abstract type, rather
than a function value or an unresolved higher-order family. -/
def abstractType (fuel : Nat) (env : Environment) (ctx : Context) (term : Term) : Bool :=
  match spine fuel env ctx term with
  | some (.type _) => true
  | _ => false

theorem abstractType_sound (h : abstractType fuel env ctx term = true) :
    ∃ level, Spine env ctx term (.type level) ∧ HasType env ctx true term (.univ level) := by
  unfold abstractType at h
  cases found : spine fuel env ctx term with
  | none => simp [found] at h
  | some kind =>
      cases kind with
      | type level => exact ⟨level, spine_sound found, (spine_sound found).typed⟩
      | index => simp [found] at h

end Jihoo.NativeKernel.Environment.CodeKinds
