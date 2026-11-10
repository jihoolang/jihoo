import Jihoo.CoreEvaluation

/-! Runtime-preserving removal of annotations and computed proof payloads.
Binder slots, modes and application structure remain. The output uses Raw as an
untyped carrier; it is not claimed to pass the source checker or be native MIR. -/
namespace Jihoo.CoreBridge.Raw.Beta.PayloadErasure
open Evaluation

def erase : Raw → Raw
  | .var x => .var x
  | .natural n => .natural n
  | .integer n => .integer n
  | .u64 => .u64
  | .i64 => .i64
  | .array _ => .array (.natural 0)
  | .lt _ _ => .lt (.natural 0) (.natural 0)
  | .eq _ _ => .eq (.natural 0) (.natural 0)
  | .pi e _ _ => .pi e .u64 .u64
  | .lam e _ body => .lam e .u64 (erase body)
  | .app f a => .app (erase f) (erase a)
  | .elements xs => .elements (xs.map erase)
  | .index a i _ => .index (erase a) (erase i) (.zeroLe (.natural 0))
  | .refl _ => .refl (.natural 0)
  | .zeroLe _ => .zeroLe (.natural 0)
  | .decide a b => .decide (erase a) (erase b)
  | .uadd a b => .uadd (erase a) (erase b)
  | .usub a b _ => .usub (erase a) (erase b) (.zeroLe (.natural 0))

theorem erase_idempotent (t : Raw) : erase (erase t) = erase t := by
  induction t using Raw.rec
    (motive_2 := fun xs => (xs.map erase).map erase = xs.map erase) <;>
    simp_all [erase]

theorem erase_renaming (t : Raw) (ρ : Nat → Nat) :
    erase (t.rename ρ) = (erase t).rename ρ := by
  induction t using Raw.rec
    (motive_2 := fun xs => ∀ ρ, (xs.map (rename ρ)).map erase = (xs.map erase).map (rename ρ))
    generalizing ρ <;> simp_all [erase, rename]

private theorem erase_lift (σ : Nat → Raw) :
    (fun x => erase (liftSub σ x)) = liftSub (fun x => erase (σ x)) := by
  funext x
  cases x <;> simp [liftSub, erase, erase_renaming]

theorem erase_substitution (t : Raw) (σ : Nat → Raw) :
    erase (t.subst σ) = (erase t).subst (fun x => erase (σ x)) := by
  induction t using Raw.rec
    (motive_2 := fun xs => ∀ σ, (xs.map (subst σ)).map erase =
      (xs.map erase).map (subst (fun x => erase (σ x))))
    generalizing σ <;> simp_all [erase, subst, erase_lift]

theorem erase_instantiate (body a : Raw) :
    erase (body.subst (single a)) = (erase body).subst (single (erase a)) := by
  rw [erase_substitution]
  congr 1
  funext x
  cases x <;> simp [single, erase]

theorem erase_natural_iff : erase t = .natural n ↔ t = .natural n := by
  cases t <;> simp [erase]

theorem erase_integer_iff : erase t = .integer n ↔ t = .integer n := by
  cases t <;> simp [erase]

theorem value_erasure (h : Value t) : Value (erase t) := by
  induction h <;> simp only [erase]
  case natural => exact .natural _
  case integer => exact .integer _
  case lam => exact .lam _ _ _
  case refl => exact .refl _
  case zeroLe => exact .zeroLe _
  case decide => exact .decide _ _
  case elements ready ih =>
    apply Value.elements
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact ih y hy

private theorem decide_shape (h : Value t) :
    ∀ a b, t = .decide a b → ∃ m n, a = .natural m ∧ b = .natural n := by
  cases h <;> intro a b he <;> cases he
  exact ⟨_, _, rfl, rfl⟩

theorem value_reflection (t : Raw) : Value (erase t) → Value t := by
  induction t using Raw.rec
    (motive_2 := fun xs => (∀ x ∈ xs.map erase, Value x) → ∀ x ∈ xs, Value x)
  case natural => intro _; exact .natural _
  case integer => intro _; exact .integer _
  case lam => intro _; exact .lam _ _ _
  case refl => intro _; exact .refl _
  case zeroLe => intro _; exact .zeroLe _
  case elements xs ih =>
    intro hv
    simp only [erase] at hv
    cases hv with | elements ready => exact .elements (ih ready)
  case decide a b _ _ =>
    intro hv
    have shapes := decide_shape hv (erase a) (erase b) (by simp only [erase])
    obtain ⟨m, n, ha, hb⟩ := shapes
    obtain rfl := erase_natural_iff.mp ha
    obtain rfl := erase_natural_iff.mp hb
    exact .decide _ _
  case var | u64 | i64 | array | lt | eq | pi | app | index | uadd | usub =>
    intro hv; simp only [erase] at hv; cases hv
  case nil => rename_i ready x hx; cases hx
  case cons =>
    rename_i x xs ihx ihxs ready y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ihx (ready _ (by simp))
    · exact ihxs (fun z hz => ready z (by simp [hz])) y hy

theorem value_iff : Value (erase t) ↔ Value t := ⟨value_reflection t, value_erasure⟩

private theorem values_map {xs : List Raw} (h : ∀ x ∈ xs, Value x) : ∀ x ∈ xs.map erase, Value x := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact value_erasure (h y hy)

def eraseFrame : Frame → Frame
  | .appFunction a => .appFunction (erase a)
  | .appArgument _ body => .appArgument .u64 (erase body)
  | .uaddLeft b => .uaddLeft (erase b)
  | .uaddRight a => .uaddRight a
  | .usubLeft b _ => .usubLeft (erase b) (.zeroLe (.natural 0))
  | .usubRight a _ => .usubRight a (.zeroLe (.natural 0))
  | .indexArray i _ => .indexArray (erase i) (.zeroLe (.natural 0))
  | .indexIndex xs _ ready => .indexIndex (xs.map erase) (.zeroLe (.natural 0)) (values_map ready)
  | .elements pre post ready => .elements (pre.map erase) (post.map erase) (values_map ready)

theorem erase_fill (f : Frame) (t : Raw) : erase (f.fill t) = (eraseFrame f).fill (erase t) := by
  cases f <;> simp [Frame.fill, eraseFrame, erase, List.map_append]

theorem step_erasure (h : Evaluation.Step t u) : Evaluation.Step (erase t) (erase u) := by
  induction h with
  | betaRuntime ready => simpa only [erase, erase_instantiate] using
      (Evaluation.Step.betaRuntime (A := .u64) (value_erasure ready))
  | betaErased => simpa only [erase, erase_instantiate] using
      (Evaluation.Step.betaErased (A := .u64))
  | add h => simpa only [erase] using Evaluation.Step.add h
  | sub hb ha => simp only [erase]; exact .sub hb ha
  | read ready selected =>
      simp only [erase]
      apply Evaluation.Step.read (values_map ready)
      simp [List.getElem?_map, selected]
  | context f _ ih => simpa only [erase_fill] using Evaluation.Step.context (eraseFrame f) ih

theorem trap_erasure (h : Trap t) : Trap (erase t) := by
  induction h with
  | overflow h => simpa only [erase] using Trap.overflow h
  | context f _ ih => simpa only [erase_fill] using Trap.context (eraseFrame f) ih

theorem steps_erasure (h : Evaluation.Steps t u) : Evaluation.Steps (erase t) (erase u) := by
  induction h with
  | refl => exact .refl
  | next hs _ ih => exact .next (step_erasure hs) ih

theorem outcome_erasure (h : Outcome t) : Outcome (erase t) := by
  rcases h with hv | ⟨u, hs⟩ | ht
  · exact .inl (value_erasure hv)
  · exact .inr (.inl ⟨_, step_erasure hs⟩)
  · exact .inr (.inr (trap_erasure ht))

/-- Erasure introduces no unexplained initial stuck state for a closed typed
source. Target source-level typing is deliberately not asserted. -/
theorem closed_erased_progress (h : HasType (fun _ => none) t A) : Outcome (erase t) :=
  outcome_erasure (Evaluation.progress h)

/-- Every source execution has an exact step-for-step erased execution, preserving
its final value shape or explicit trap and its scalar observations. This does not
assert that all target executions have been reflected back to source executions. -/
theorem execution_erasure (h : HasType (fun _ => none) t A) (hs : Evaluation.Steps t u) :
    Evaluation.Steps (erase t) (erase u) ∧ Outcome (erase u) ∧
      (Value (erase u) ↔ Value u) ∧ (Trap u → Trap (erase u)) :=
  ⟨steps_erasure hs, closed_erased_progress (Evaluation.preservation_steps h hs),
    value_iff, trap_erasure⟩

end Jihoo.CoreBridge.Raw.Beta.PayloadErasure
