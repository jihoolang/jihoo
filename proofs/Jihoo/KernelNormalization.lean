import Jihoo.KernelConversion
import Jihoo.CoreBridgeComputation

/-! Forward computational adequacy of the executable Raw normalizer. The
normalizer computes from syntax alone; every residual is reachable by the
independently defined contextual computation relation. Consequently the exact
original type and type formation survive bounded normalization. This does not
assert that a bounded residual is a full normal form. -/
namespace Jihoo.KernelNormalization

open CoreBridge CoreBridge.Raw KernelConversion
open Computation (Step Steps)

/-- Every actual root contraction is a forward step, not only an equation in
the symmetric conversion relation. -/
theorem contract_step {t u : Raw} (h : contract t = some u) : Step t u := by
  cases t <;> simp only [contract] at h
  all_goals first | contradiction | skip
  case app f a =>
    cases f <;> try dsimp only at h
    all_goals first | contradiction | skip
    case lam e A body =>
      split at h
      · cases h
        exact .beta e A body a
      · contradiction
  case uadd a b =>
    cases a <;> try dsimp only at h
    all_goals first | contradiction | skip
    case natural a =>
      cases b <;> try dsimp only at h
      all_goals first | contradiction | skip
      case natural b =>
        split at h
        · rename_i bound
          cases h
          exact .add a b bound
        · contradiction
  case usub a b p =>
    cases a <;> try dsimp only at h
    all_goals first | contradiction | skip
    case natural a =>
      cases b <;> try dsimp only at h
      all_goals first | contradiction | skip
      case natural b =>
        split at h
        · rename_i bound
          cases h
          exact .subLiteral a b p bound.1 bound.2
        · contradiction
  case index a i p =>
    cases a <;> try dsimp only at h
    all_goals first | contradiction | skip
    case elements xs =>
      cases i <;> try dsimp only at h
      all_goals first | contradiction | skip
      case natural k => exact .read xs k p u h

private theorem binary (F : Raw → Raw → Raw)
    (left : ∀ {a a' b}, Step a a' → Step (F a b) (F a' b))
    (right : ∀ {a b b'}, Step b b' → Step (F a b) (F a b'))
    (ha : Steps a a') (hb : Steps b b') : Steps (F a b) (F a' b') :=
  (ha.map (fun x => F x b) (fun hs => left hs)).trans
    (hb.map (fun x => F a' x) (fun hs => right hs))

private theorem ternary (F : Raw → Raw → Raw → Raw)
    (first : ∀ {a a' b c}, Step a a' → Step (F a b c) (F a' b c))
    (second : ∀ {a b b' c}, Step b b' → Step (F a b c) (F a b' c))
    (third : ∀ {a b c c'}, Step c c' → Step (F a b c) (F a b c'))
    (ha : Steps a a') (hb : Steps b b') (hc : Steps c c') :
    Steps (F a b c) (F a' b' c') :=
  (ha.map (fun x => F x b c) (fun hs => first hs)).trans
    ((hb.map (fun x => F a' x c) (fun hs => second hs)).trans
      (hc.map (fun x => F a' b' x) (fun hs => third hs)))

private theorem elements_prefix (f : Raw → Raw) (h : ∀ t, Steps t (f t))
    (xs : List Raw) (pre : List Raw) :
    Steps (.elements (pre ++ xs)) (.elements (pre ++ xs.map f)) := by
  induction xs generalizing pre with
  | nil => exact .refl
  | cons x xs ih =>
      have head := (h x).map (fun y => .elements (pre ++ y :: xs))
        (fun hs => Step.elements pre xs hs)
      have tail := ih (pre ++ [f x])
      simp only [List.append_assoc, List.singleton_append] at tail
      exact head.trans tail

/-- Independently reduce every immediate child in sequence, including all
array entries, evidence fields, annotations and dependent binder bodies. -/
theorem children_steps (t : Raw) (f : Raw → Raw) (h : ∀ t, Steps t (f t)) :
    Steps t (children f t) := by
  cases t with
  | var | natural | integer | u64 | i64 => exact .refl
  | array n => exact (h n).map Raw.array (fun hs => .array hs)
  | lt a b => exact binary Raw.lt (fun hs => .ltLeft hs) (fun hs => .ltRight hs) (h a) (h b)
  | eq a b => exact binary Raw.eq (fun hs => .eqLeft hs) (fun hs => .eqRight hs) (h a) (h b)
  | pi e A B =>
      exact binary (Raw.pi e) (fun hs => .piDomain hs) (fun hs => .piCodomain hs) (h A) (h B)
  | lam e A body =>
      exact binary (Raw.lam e) (fun hs => .lamDomain hs) (fun hs => .lamBody hs) (h A) (h body)
  | app g a =>
      exact binary Raw.app (fun hs => .appFunction hs) (fun hs => .appArgument hs) (h g) (h a)
  | elements xs => exact elements_prefix f h xs []
  | index a i p =>
      exact ternary Raw.index (fun hs => .indexArray hs) (fun hs => .indexIndex hs)
        (fun hs => .indexProof hs) (h a) (h i) (h p)
  | refl a => exact (h a).map Raw.refl (fun hs => .reflTerm hs)
  | zeroLe a => exact (h a).map Raw.zeroLe (fun hs => .zeroLe hs)
  | decide a b =>
      exact binary Raw.decide (fun hs => .decideLeft hs) (fun hs => .decideRight hs) (h a) (h b)
  | uadd a b =>
      exact binary Raw.uadd (fun hs => .uaddLeft hs) (fun hs => .uaddRight hs) (h a) (h b)
  | usub a b p =>
      exact ternary Raw.usub (fun hs => .usubLeft hs) (fun hs => .usubRight hs)
        (fun hs => .usubProof hs) (h a) (h b) (h p)

/-- The exact executable result is reachable by a finite sequence of forward
beta, bounded arithmetic and local-array-read steps, for every Raw input. -/
theorem normalize_steps (fuel : Nat) (t : Raw) : Steps t (normalize fuel t) := by
  induction fuel generalizing t with
  | zero => exact .refl
  | succ fuel ih =>
      have hc := children_steps t (normalize fuel) ih
      simp only [normalize]
      split
      · rename_i u hu
        exact hc.trans (.next (contract_step hu) (ih u))
      · exact hc

/-- Normalize the term while retaining the original raw type, even when that
type contains unreduced dependent indices. -/
theorem normalize_preserves_type {Γ : Context} {t A : Raw}
    (typed : Beta.HasType Γ t A) (fuel : Nat) :
    Beta.HasType Γ (normalize fuel t) A :=
  Computation.preservation_steps typed (normalize_steps fuel t)

/-- Reducing the annotation or a dependent codomain preserves formation. -/
theorem normalize_preserves_formation {Γ : Context} {A : Raw}
    (formed : Beta.IsType Γ A) (fuel : Nat) :
    Beta.IsType Γ (normalize fuel A) :=
  Computation.formation_preservation_steps formed (normalize_steps fuel A)

/-- The checker may normalize both the term and its result type independently. -/
theorem normalize_preserves_both {Γ : Context} {t A : Raw}
    (typed : Beta.HasType Γ t A) (termFuel typeFuel : Nat) :
    Beta.HasType Γ (normalize termFuel t) (normalize typeFuel A) :=
  (normalize_preserves_type typed termFuel).convert (normalize_sound typeFuel A)

/-- A positive comparison supplies a common forward reduct of its two inputs.
This is stronger than merely constructing an undirected conversion chain. -/
theorem equal_common_reduct {fuel : Nat} {a b : Raw} (h : equal fuel a b = true) :
    ∃ u, Steps a u ∧ Steps b u := by
  have he : normalize fuel a = normalize fuel b := of_decide_eq_true h
  exact ⟨normalize fuel b, he ▸ normalize_steps fuel a, normalize_steps fuel b⟩

/-- Formation ensures that normalization retains the proposition classification
used for erased binders. Arbitrary unformed Raw terms need not have this property. -/
theorem normalize_preserves_proposition {Γ : Context} {A : Raw}
    (formed : Beta.IsType Γ A) (fuel : Nat) :
    (normalize fuel A).proposition = A.proposition := by
  have classification : ∀ {B C : Raw}, Steps B C → Beta.IsType Γ B →
      C.proposition = B.proposition := by
    intro B C steps
    induction steps with
    | refl => intro _; rfl
    | next hs _ ih =>
        intro hB
        exact (ih (Computation.formation_preservation hB hs)).trans
          (Computation.formation_proposition_step hB hs)
  exact classification (normalize_steps fuel A) formed

end Jihoo.KernelNormalization
