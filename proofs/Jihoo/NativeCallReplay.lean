import Jihoo.NativeKindNormalization
import Jihoo.NativeKindSpine

/-! Replay a call from its inferred signature. Every dependent domain is exposed
by the certified normalizer and every argument is checked before instantiation.
No external signature, erasure list, or ownership list is accepted. -/
namespace Jihoo.NativeKernel.Environment.CallReplay
open CodeKinds

structure Argument where
  erased : Bool
  domain : Term
  value : Term
  deriving Repr, DecidableEq

def runtimeArguments (arguments : List Argument) : List Term :=
  arguments.filterMap fun argument => if argument.erased then none else some argument.value

inductive Steps (env : Environment) (ctx : Context) (ghost : Bool) :
    Term → List Term → List Argument → Term → Prop where
  | nil : Steps env ctx ghost signature [] [] signature
  | cons : Conversion.normalize? env fuel signature = some (.pi erased domain codomain) →
      Checker.check fuel env ctx (ghost || erased) argument domain = true →
      Checker.applicationOK fuel env ghost domain argument = true →
      Conversion.substitutionSafe codomain argument = true →
      Steps env ctx ghost (codomain.subst (fun | 0 => argument | n + 1 => .var n))
        rest entries result →
      Steps env ctx ghost signature (argument :: rest)
        (⟨erased, domain, argument⟩ :: entries) result

/-- Argument order is source order. Erased arguments remain in the trace but
are absent from runtimeArguments. -/
def replay : Nat → Environment → Context → Bool → Term → List Term →
    Option (List Argument × Term)
  | 0, _, _, _, _, _ => none
  | _ + 1, _, _, _, signature, [] => some ([], signature)
  | fuel + 1, env, ctx, ghost, signature, argument :: rest => do
      let normal ← Conversion.normalize? env fuel signature
      match normal with
      | .pi erased domain codomain =>
          if Checker.check fuel env ctx (ghost || erased) argument domain &&
              Checker.applicationOK fuel env ghost domain argument &&
              Conversion.substitutionSafe codomain argument then
            let (entries, result) ← replay fuel env ctx ghost
              (codomain.subst (fun | 0 => argument | n + 1 => .var n)) rest
            pure (⟨erased, domain, argument⟩ :: entries, result)
          else none
      | _ => none

theorem replay_sound (h : replay fuel env ctx ghost signature arguments = some (entries, result)) :
    Steps env ctx ghost signature arguments entries result := by
  induction fuel generalizing signature arguments entries result with
  | zero => simp [replay] at h
  | succ fuel ih =>
      cases arguments with
      | nil => simp only [replay, Option.some.injEq, Prod.mk.injEq] at h
               obtain ⟨rfl, rfl⟩ := h; exact .nil
      | cons argument rest =>
          simp only [replay] at h
          cases normalized : Conversion.normalize? env fuel signature with
          | none => simp [normalized] at h
          | some normal =>
              simp only [normalized, Bind.bind, Option.bind] at h
              split at h
              · rename_i erased domain codomain
                split at h
                · rename_i accepted
                  have checks := Bool.and_eq_true_iff.mp accepted
                  have termChecks := Bool.and_eq_true_iff.mp checks.1
                  cases next : replay fuel env ctx ghost
                      (codomain.subst (fun | 0 => argument | n + 1 => .var n)) rest with
                  | none => simp [next] at h
                  | some pair =>
                      rcases pair with ⟨tail, final⟩
                      simp only [next] at h
                      cases h
                      exact .cons normalized termChecks.1 termChecks.2 checks.2 (ih next)
                · contradiction
              · contradiction

theorem Steps.apply (steps : Steps env ctx ghost signature arguments entries result)
    (typed : HasType env ctx ghost head signature) :
    HasType env ctx ghost (applications head arguments) result := by
  induction steps generalizing head with
  | nil => exact typed
  | cons normalized checked allowed _ rest ih =>
      exact ih (.app (.convert typed (Conversion.normalize?_sound normalized))
        (Checker.check_sound checked) (Checker.applicationOK_sound allowed))

theorem Steps.values (steps : Steps env ctx ghost signature arguments entries result) :
    entries.map Argument.value = arguments := by
  induction steps with
  | nil => rfl
  | cons _ _ _ _ _ ih => exact congrArg (List.cons _) ih

/-- Signature inference is part of this function, never a caller certificate. -/
def infer (fuel : Nat) (env : Environment) (ctx : Context) (ghost : Bool)
    (head : Term) (arguments : List Term) : Option (List Argument × Term) := do
  let signature ← Checker.infer fuel env ctx ghost head
  replay fuel env ctx ghost signature arguments

theorem infer_sound (h : infer fuel env ctx ghost head arguments = some (entries, result)) :
    ∃ signature, HasType env ctx ghost head signature ∧
      Steps env ctx ghost signature arguments entries result ∧
      HasType env ctx ghost (applications head arguments) result := by
  unfold infer at h
  cases found : Checker.infer fuel env ctx ghost head with
  | none => simp [found] at h
  | some signature =>
      simp only [found, Bind.bind, Option.bind] at h
      have steps := replay_sound h
      have typed := Checker.infer_sound found
      exact ⟨signature, typed, steps, steps.apply typed⟩

/-- Normalized kind domains force the actual code application plainness gate.
This theorem does not rely on raw kindOf of a beta-hidden annotation. -/
theorem kindArgument_normal_plain {kind : Kind}
    (checked : Checker.applicationOK fuel env false kind.term argument = true) :
    plain env (Conversion.normalize env fuel argument) = true := by
  cases normalized : Conversion.normalize? env fuel kind.term with
  | none => simp [Checker.applicationOK, normalized] at checked
  | some normal =>
      have fixed := kind.normalize?_fixed normalized
      subst normal
      have gate : globalFree kind.term = true ∧
          plain env (Conversion.normalize env fuel argument) = true := by
        simpa only [Checker.applicationOK, normalized, Bool.false_or, Kind.kindOf,
          Bool.not_true, Bool.false_or, Kind.firstOrder, Bool.true_and, Bool.and_eq_true] using checked
      exact gate.2

theorem kindArgument_plain {kind : Kind}
    (checked : Checker.applicationOK fuel env false kind.term argument = true) :
    ∃ normal, Conversion.Conv env argument normal ∧ plain env normal = true :=
  ⟨_,Conversion.normalize_sound env fuel argument,kindArgument_normal_plain checked⟩

/-- Back values and actual boxed/buffer domains are runtime owners. The
annotations here are precisely the normalized domains in Steps. -/
def linearDomain (env : Environment) : Term → Bool
  | .back _ _ _ => true
  | domain => Checker.ownedHead env domain

def ownsArgument (env : Environment) (entry : Argument) : Bool :=
  !entry.erased && linearDomain env entry.domain

/-- A result has either a known nonfunction head or an authenticated abstract
first-order type spine. In particular, a neutral variable is never accepted
merely because its spelling is a variable. -/
inductive ResultShape (env : Environment) (ctx : Context) (result : Term) : Prop where
  | rigid : Conversion.Conv env result (.node op children) →
      EnvironmentDelta.Basis.nonFunctionOp op = true → ResultShape env ctx result
  | abstract : Conversion.Conv env result normal → Spine env ctx normal (.type level) →
      ResultShape env ctx result

def rigidResultHead : Term → Bool
  | .var _ => false
  | term@(.node _ _) => Checker.takeNonFunctionHead term

theorem rigidResultHead_sound (accepted : rigidResultHead term = true) :
    ∃ op children, term = .node op children ∧ EnvironmentDelta.Basis.nonFunctionOp op = true := by
  cases term with
  | var index => contradiction
  | node op children =>
      refine ⟨op,children,rfl,?_⟩
      cases op <;> simp_all [rigidResultHead, Checker.takeNonFunctionHead,
        NativeKernel.nonFunctionHead, Checker.resourceNonFunctionHead,
        EnvironmentDelta.Basis.nonFunctionOp]

/-- A consumed runtime owner cannot be retained by a returned function.
Abstract results use the actual context kind spine, including its U64 checks. -/
def partialOK (fuel : Nat) (env : Environment) (ctx : Context)
    (entries : List Argument) (result : Term) : Bool :=
  !(entries.any (ownsArgument env)) ||
    (rigidResultHead (Conversion.normalize env fuel result) ||
      abstractType fuel env ctx (Conversion.normalize env fuel result))

theorem partialOK_sound (h : partialOK fuel env ctx entries result = true) :
    entries.any (ownsArgument env) = false ∨ ResultShape env ctx result := by
  rcases Bool.or_eq_true_iff.mp h with noOwner | represented
  · exact Or.inl (by cases found : entries.any (ownsArgument env) <;> simp_all)
  · apply Or.inr
    rcases Bool.or_eq_true_iff.mp represented with rigid | abstracted
    · obtain ⟨op,children,same,head⟩ := rigidResultHead_sound rigid
      exact .rigid (by rw [← same]; exact Conversion.normalize_sound env fuel result) head
    · obtain ⟨level,spine,_⟩ := abstractType_sound abstracted
      exact .abstract (Conversion.normalize_sound env fuel result) spine

/-- Erased entries never enter the runtime argument list. Every non-erased
entry is retained once, in source argument order. -/
theorem runtimeArguments_cons (entry : Argument) (entries : List Argument) :
    runtimeArguments (entry :: entries) =
      if entry.erased then runtimeArguments entries else entry.value :: runtimeArguments entries := by
  cases entry with
  | mk erased domain value => cases erased <;> rfl

/-- Authenticate the whole context before exposing any local signature. -/
def checked (fuel : Nat) (env : Environment) (ctx : Context) (ghost : Bool)
    (head : Term) (arguments : List Term) : Option (List Argument × Term) :=
  if contextOK fuel env ctx then infer fuel env ctx ghost head arguments else none

theorem checked_origin (h : checked fuel env ctx ghost head arguments = some (entries,result)) :
    contextOK fuel env ctx = true ∧ infer fuel env ctx ghost head arguments = some (entries,result) := by
  unfold checked at h
  split at h
  · rename_i formed; exact ⟨formed,h⟩
  · contradiction

theorem checked_sound (h : checked fuel env ctx ghost head arguments = some (entries, result)) :
    ContextFormed env ctx ∧ HasType env ctx ghost (applications head arguments) result := by
  unfold checked at h
  split at h
  · rename_i formed
    exact ⟨contextOK_sound formed, (infer_sound h).choose_spec.2.2⟩
  · contradiction

end Jihoo.NativeKernel.Environment.CallReplay
