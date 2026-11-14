import Jihoo.NativeEnvironmentTyping
import Jihoo.NativeEnvironmentExtension
import Jihoo.NativeOwnership
import Jihoo.NativeFamilyEnvironment

/-! Resource projection derived from the actual checked family table.
Constructors retain exactly their relevant fields; family binder annotations
retain their derived ownership mode. The resulting safety statement concerns
the projected control tree and does not assert a native heap semantics. -/
namespace Jihoo.NativeKernel.EnvironmentQuantity

open Environment

def relevantFields (data : Bool) : List Field → List Term → Option (List Term)
  | [], [] => some []
  | field :: fields, argument :: arguments => do
      let rest ← relevantFields data fields arguments
      pure (if data && !field.erased then argument :: rest else rest)
  | _, _ => none

def ordinary : Op → Bool
  | .global _ | .ind _ _ | .con _ _ _ | .elim _ _ | .caseOf _ _ | .view _ _ _ | .lend => false
  | _ => true

inductive Skeleton (env : Environment) : Term → Term → Prop where
  | var (x : Nat) : Skeleton env (.var x) (.var x)
  | node : ordinary op = true → Conversion.ListRel (Skeleton env) arguments projected →
      Skeleton env (.node op arguments) (.node op projected)
  | familyType : env.families[family]? = some entry →
      Skeleton env (.node (.ind family count) indices)
        (if entry.boxed then .buffer (.natural 0) else .u64)
  | constructor : env.families[family]? = some entry → entry.signatures[constructor]? = some signature →
      count = arguments.length → relevantFields entry.declaration.data signature.fields arguments = some relevant →
      Conversion.ListRel (Skeleton env) relevant projected →
      Skeleton env (.node (.con family constructor count) arguments) (.elements projected.length projected)
  | propositionElimination : env.families[family]? = some entry → entry.declaration.data = false →
      Skeleton env (.node (.elim family count) arguments) (.natural 0)

def skeleton : Nat → Environment → Term → Option Term
  | 0, _, _ => none
  | fuel + 1, env, term =>
      match term with
      | .var x => some (.var x)
      | .node op arguments =>
          match op with
          | .ind family _ => do
              let entry ← env.families[family]?
              pure (if entry.boxed then .buffer (.natural 0) else .u64)
          | .con family constructor count => do
              let entry ← env.families[family]?
              let signature ← entry.signatures[constructor]?
              if count = arguments.length then
                let relevant ← relevantFields entry.declaration.data signature.fields arguments
                let projected ← FamilyEnvironment.mapChecked (skeleton fuel env) relevant
                pure (.elements projected.length projected)
              else none
          | .elim family _ => do
              let entry ← env.families[family]?
              if entry.declaration.data = false then some (.natural 0) else none
          | _ =>
              if ordinary op then do
                let projected ← FamilyEnvironment.mapChecked (skeleton fuel env) arguments
                pure (.node op projected)
              else none

private theorem map_sound {f : Term → Option Term}
    (sound : ∀ term projected, f term = some projected → Skeleton env term projected)
    (h : FamilyEnvironment.mapChecked f terms = some projected) :
    Conversion.ListRel (Skeleton env) terms projected := by
  induction terms generalizing projected with
  | nil => simp only [FamilyEnvironment.mapChecked, Option.some.injEq] at h; cases h; exact .nil
  | cons term rest ih =>
      simp only [FamilyEnvironment.mapChecked] at h
      cases head : f term with
      | none => simp [head] at h
      | some value =>
          simp only [head, Bind.bind, Option.bind] at h
          cases tail : FamilyEnvironment.mapChecked f rest with
          | none => simp [tail] at h
          | some values =>
              simp only [tail] at h
              cases h
              exact .cons (sound _ _ head) (ih tail)

theorem skeleton_sound (h : skeleton fuel env term = some projected) : Skeleton env term projected := by
  induction fuel generalizing term projected with
  | zero => simp [skeleton] at h
  | succ fuel ih =>
      cases term with
      | var x => simp only [skeleton, Option.some.injEq] at h; cases h; exact .var x
      | node op arguments =>
          simp only [skeleton] at h
          split at h
          · rename_i family count
            cases found : env.families[family]? with
            | none => simp [found] at h
            | some entry =>
                simp only [found, Bind.bind, Option.bind] at h
                cases h
                exact .familyType found
          · rename_i family constructor count
            cases found : env.families[family]? with
            | none => simp [found] at h
            | some entry =>
                simp only [found, Bind.bind, Option.bind] at h
                cases signatureFound : entry.signatures[constructor]? with
                | none => simp [signatureFound] at h
                | some signature =>
                    simp only [signatureFound] at h
                    split at h
                    · rename_i countOK
                      cases relevant : relevantFields entry.declaration.data signature.fields arguments with
                      | none => simp [relevant] at h
                      | some fields =>
                          simp only [relevant] at h
                          cases mapped : FamilyEnvironment.mapChecked (skeleton fuel env) fields with
                          | none => simp [mapped] at h
                          | some values =>
                              simp only [mapped] at h
                              cases h
                              exact .constructor found signatureFound countOK relevant (map_sound (fun _ _ h => ih h) mapped)
                    · contradiction
          · rename_i family count
            cases found : env.families[family]? with
            | none => simp [found] at h
            | some entry =>
                simp only [found, Bind.bind, Option.bind] at h
                split at h
                · rename_i proof
                  cases h
                  exact .propositionElimination found proof
                · contradiction
          · split at h
            · rename_i ordinaryOp
              cases mapped : FamilyEnvironment.mapChecked (skeleton fuel env) arguments with
              | none => simp [mapped] at h
              | some values =>
                  simp only [mapped, Bind.bind, Option.bind] at h
                  cases h
                  exact .node ordinaryOp (map_sound (fun _ _ h => ih h) mapped)
            · contradiction

def check (fuel : Nat) (env : Environment) (term : Term) : Bool :=
  match skeleton fuel env term with
  | none => false
  | some projected => NativeOwnership.checkClosed fuel projected

def Safe (env : Environment) (term : Term) : Prop :=
  ∃ projected, Skeleton env term projected ∧ NativeOwnership.ClosedSafe projected

theorem check_sound (h : check fuel env term = true) : Safe env term := by
  cases projected : skeleton fuel env term with
  | none => simp [check, projected] at h
  | some result =>
      exact ⟨result, skeleton_sound projected, fuel, by simpa only [check, projected] using h⟩

theorem Skeleton.extend (extension : Environment.Extends before after)
    (projected : Skeleton before source target) : Skeleton after source target := by
  induction projected using Skeleton.rec
    (motive_2 := fun terms projected _ => Conversion.ListRel (Skeleton after) terms projected) with
  | var index => exact .var index
  | node ordinary terms ih => exact .node ordinary ih
  | familyType found => exact .familyType (extension.families _ _ found)
  | constructor found signature count relevant terms ih =>
      exact .constructor (extension.families _ _ found) signature count relevant ih
  | propositionElimination found proof => exact .propositionElimination (extension.families _ _ found) proof
  | nil => exact .nil
  | cons head tail ih iht => exact .cons ih iht

theorem Safe.extend (extension : Environment.Extends before after) (safe : Safe before term) : Safe after term := by
  obtain ⟨target, projected, closed⟩ := safe
  exact ⟨target, projected.extend extension, closed⟩

end Jihoo.NativeKernel.EnvironmentQuantity
