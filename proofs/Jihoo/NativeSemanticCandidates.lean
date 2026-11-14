import Jihoo.NativeEnvironmentTypeUniqueness

/-! First semantic layer for the actual unified native judgment. Candidates
are saturated under the proved full ACU relation. Dependent functions and
refinements use actual native application/projection syntax and beta equations.
This module does not assert a fundamental lemma for every typing rule, nor
identify raw proof terms through a proof-irrelevance conversion axiom. -/
namespace Jihoo.NativeKernel.Environment.Semantics
open Jihoo.NativeKernel.Environment.Conversion

variable {env : Environment}

structure Candidate (env : Environment) where
  holds : Term → Prop
  saturated : ∀ {a b}, Conv env a b → (holds a ↔ holds b)

instance : CoeFun (Candidate env) (fun _ => Term → Prop) := ⟨Candidate.holds⟩

theorem Candidate.transport (candidate : Candidate env) (converted : Conv env a b) : candidate a → candidate b :=
  (candidate.saturated converted).mp

def proposition (truth : Prop) : Candidate env := ⟨fun _ => truth,fun _ => Iff.rfl⟩

def equality (left right : Term) : Candidate env := proposition (Conv env left right)

theorem equality_refl (term : Term) : equality (env := env) term term (.refl term) := .refl _

theorem equality_numerals (wf : UnifiedProgram.EnvWellFormed env) (realized : equality (env := env) (.natural m) (.natural n) evidence) : m = n :=
  realized.natural_injective wf.admissible

theorem false_equality_empty (wf : UnifiedProgram.EnvWellFormed env) (different : m ≠ n) :
    ¬ equality (env := env) (.natural m) (.natural n) evidence := fun realized => different (equality_numerals wf realized)

/-- A family respects conversion of its argument; this is a property to be
proved for a concrete interpretation, not a typed-equality oracle. -/
structure Family (env : Environment) where
  fiber : Term → Candidate env
  respects : ∀ {a b}, Conv env a b → ∀ term, fiber a term ↔ fiber b term

variable {domain base owner : Candidate env} {codomain predicate : Family env}

def constant (candidate : Candidate env) : Family env := ⟨fun _ => candidate,fun _ _ => Iff.rfl⟩

def pi (domain : Candidate env) (codomain : Family env) : Candidate env where
  holds function := ∀ argument, domain argument → codomain.fiber argument (.app function argument)
  saturated := by
    intro function replacement converted
    constructor <;> intro realizes argument admitted
    · exact (codomain.fiber argument).transport
        (.node .app (.cons converted (.cons (.refl _) .nil))) (realizes argument admitted)
    · exact (codomain.fiber argument).transport
        (.node .app (.cons (.symm converted) (.cons (.refl _) .nil))) (realizes argument admitted)

theorem pi_application (function : pi domain codomain f) (argument : domain a) :
    codomain.fiber a (.app f a) := function a argument

/-- The introduction proof uses the actual unrestricted native beta equation;
no normalization or logical-relation fundamental theorem is supplied as input. -/
theorem pi_lambda (body : ∀ argument, domain argument →
    codomain.fiber argument (term.subst (single argument))) :
    pi domain codomain (.lam erased annotation term) := by
  intro argument admitted
  exact (codomain.fiber argument).transport (.symm (.legacy (.beta erased annotation term argument)))
    (body argument admitted)

def refinement (base : Candidate env) (predicate : Family env) : Candidate env where
  holds value := base (.witness value) ∧ predicate.fiber (.witness value) (.proof value)
  saturated := by
    intro value replacement converted
    have witness : Conv env (.witness value) (.witness replacement) := .node .witness (.cons converted .nil)
    have proof : Conv env (.proof value) (.proof replacement) := .node .proof (.cons converted .nil)
    constructor
    · intro realized
      exact ⟨base.transport witness realized.1,
        (predicate.fiber (.witness replacement)).transport proof
          ((predicate.respects witness _).mp realized.2)⟩
    · intro realized
      exact ⟨base.transport (.symm witness) realized.1,
        (predicate.fiber (.witness value)).transport (.symm proof)
          ((predicate.respects witness _).mpr realized.2)⟩

theorem refinement_pack (value : base a) (evidence : predicate.fiber a proof) :
    refinement base predicate (.pack annotation a proof) := by
  have projects : Conv env (.witness (.pack annotation a proof)) a := .legacy (.witnessPack annotation a proof)
  have proves : Conv env (.proof (.pack annotation a proof)) proof := .legacy (.proofPack annotation a proof)
  exact ⟨base.transport (.symm projects) value,
    (predicate.respects projects _).mpr ((predicate.fiber a).transport (.symm proves) evidence)⟩

theorem refinement_witness (realized : refinement base predicate value) : base (.witness value) := realized.1

theorem refinement_proof (realized : refinement base predicate value) :
    predicate.fiber (.witness value) (.proof value) := realized.2

def reference (owner : Candidate env) : Candidate env where
  holds value := owner (.deref value)
  saturated := fun converted => owner.saturated (.node .deref (.cons converted .nil))

theorem reference_borrow (realized : owner value) : reference owner (.borrow value) :=
  owner.transport (.symm (.legacy (.derefBorrow value))) realized

theorem reference_deref (realized : reference owner value) : owner (.deref value) := realized

/-- A semantic impredicative proposition is an ordinary Lean proposition,
regardless of the universe level of its quantified domain. -/
def impredicativePi {α : Sort u} (predicate : α → Prop) : Prop := ∀ value, predicate value

theorem impredicativePi_intro {α : Sort u} {predicate : α → Prop} (proof : ∀ value, predicate value) :
    impredicativePi (α := α) predicate := proof

theorem impredicativePi_elim {α : Sort u} {predicate : α → Prop} (proof : impredicativePi predicate) (value : α) :
    predicate value := proof value

/-- The actual sort operation keeps proposition codomains impredicative. -/
theorem proposition_pi_sort (domain : SortTag) : domain.pi .prop = .prop := by cases domain <;> rfl

theorem universe_pi_sort (domain codomain : Nat) :
    (SortTag.type domain).pi (.type codomain) = .type (max domain codomain) := rfl

theorem universe_successor_boundary
    (wf : UnifiedProgram.EnvWellFormed env) (typed : HasType env ctx mode (.univ n) (.univ level)) : level = n + 1 := typed.universe_successor wf

end Jihoo.NativeKernel.Environment.Semantics
