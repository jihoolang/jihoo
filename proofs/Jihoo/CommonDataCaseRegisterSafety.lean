import Jihoo.CommonDataRestrictedComposition

/-! Exact uniform register restriction for the existing copied Case ABI.
This module does not supply source typing, ownership, or a body compiler. -/
namespace Jihoo.CommonDataCaseRegisterSafety
open ReferenceCfg ReferenceCalls CommonDataCaseCfg CommonDataCaseRelocation
open CommonDataRestrictedComposition

inductive Branch where
  | node | nil
  deriving DecidableEq

def writes : Branch → List Nat
  | .node => [0,1,2,3,4,5]
  | .nil => [0,1,6]

/-- Retained means needed after this entry; consumed scrutinees are not
necessarily retained. The caller must account for every surviving binding. -/
def Safe (branch : Branch) (live : List Nat) : Prop :=
  ∀ k ∈ live, k ∉ writes branch

instance (branch : Branch) (live : List Nat) : Decidable (Safe branch live) :=
  inferInstanceAs (Decidable (∀ k ∈ live, k ∉ writes branch))

def updated : Branch → Array (Option Value) → Nat → Nat → Nat → Array (Option Value)
  | .node, vs, j, l, r => nodeLocals (vs.set! 0 (some (.pointer j 0))) j l r
  | .nil, vs, j, _, _ => nilLocals (vs.set! 0 (some (.pointer j 0)))

def Agrees (live : List Nat) (before after : Array (Option Value)) : Prop :=
  ∀ k ∈ live, after[k]? = before[k]?

theorem safe_preserves (safe : Safe branch live) :
    Agrees live vs (updated branch vs j l r) := by
  cases branch with
  | node => exact fun _ hk => copied_node_live safe hk
  | nil => exact fun _ hk => copied_nil_live safe hk

/-- Exact maximality among value-independent restrictions on retained slots
for these entry transformers. This quantifies over arrays of size at least
seven, NOT over source-typed reachable states. Accidental value equality may
permit more on a particular state. -/
theorem safe_iff_uniform : Safe branch live ↔
    ∀ (vs : Array (Option Value)) (j l r : Nat), 7 ≤ vs.size →
      Agrees live vs (updated branch vs j l r) := by
  constructor
  · intro hs vs j l r _; exact safe_preserves hs
  · intro uniform k hk written
    have witness := uniform #[none, none, none, none, none, none, none] 0 0 0
      (by decide) k hk
    cases branch <;>
      simp [writes] at written
    · rcases written with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [updated, nodeLocals] at witness
    · rcases written with rfl | rfl | rfl <;>
        simp [updated, nilLocals] at witness

/-- Connect a complete liveness declaration to the frozen entry contract.
For Node, A requires coverage of the entire pre-entry context (including
selected aliases); for Nil, pass removeHead ctx. Coverage is explicit. -/
def Covers (ctx : List RecursiveLexicalFields.Entry) (slots live : List Nat) : Prop :=
  ∀ (k : Nat) e slot, ctx[k]? = some e → slots[k]? = some slot →
    CommonDataTargetContext.Active e → slot ∈ live

theorem safe_reserved (covered : Covers ctx slots live) (safe : Safe branch live) :
    CommonDataCaseEntryContext.Reserved ctx slots (writes branch) := by
  intro k e slot he hs ha
  exact safe slot (covered k e slot he hs ha)

/-- The justified restricted layout: one fixed installation, a complete
retained-context declaration, and the exact uniform slot restriction. It
adds no ownership or source evaluation assumption. -/
structure RestrictedPlacement (p : Program) (f : Fragment) (branch : Branch)
    (ctx : List RecursiveLexicalFields.Entry) (slots : List Nat) where
  placement : Placement p f
  live : List Nat
  covered : Covers ctx slots live
  safe : Safe branch live

theorem RestrictedPlacement.reserved
    (layout : RestrictedPlacement p f branch ctx slots) :
    CommonDataCaseEntryContext.Reserved ctx slots (writes branch) :=
  safe_reserved layout.covered layout.safe

/-- The restricted layout cannot hide a live sibling by omitting it from live. -/
theorem no_node_layout {k : Nat} (entry : ctx[k]? = some e) (slot : slots[k]? = some 5)
    (active : CommonDataTargetContext.Active e) :
    ¬ Nonempty (RestrictedPlacement p f .node ctx slots) := by
  rintro ⟨layout⟩
  exact layout.reserved k e 5 entry slot active (by decide)

/-- State-independent checker at a selected branch boundary. This is a proof
API guard, not a new target instruction or a source type checker. -/
def checkedEntry (branch : Branch) (live : List Nat) (p : Program)
    (limit : Nat) (s : State) : Option (State × List Event) :=
  if Safe branch live then
    CommonDataCaseRelocation.walk p (match branch with | .node => 11 | .nil => 5) limit s
  else none

theorem unsafe_rejected (notSafe : ¬ Safe branch live) :
    checkedEntry branch live p limit s = none := by
  simp [checkedEntry, notSafe]

/-- Installed Node entry plus preservation of all declared retained slots. -/
theorem checked_node (h : Placement p f) (safe : Safe .node live)
    (found : H[j]? = some (ReferenceHeap.node (.object l 0) (.object r 0)))
    (selected : vs[f.src]? = some (some (.pointer j 0)))
    (space : 7 ≤ vs.size) (bound : ks.length ≤ limit) :
    checkedEntry .node live p limit (stateAt H vs (h.pre.size + 6) ks) =
      some (stateAt H (updated .node vs j l r) (h.pre.size + 4) ks, []) ∧
    Agrees live vs (updated .node vs j l r) := by
  constructor
  · simpa [checkedEntry, safe, updated] using h.node_entry found selected space bound
  · exact safe_preserves safe

theorem checked_nil (h : Placement p f) (safe : Safe .nil live)
    (found : H[j]? = some ReferenceHeap.nilObject)
    (selected : vs[f.src]? = some (some (.pointer j 0)))
    (space : 7 ≤ vs.size) (bound : ks.length ≤ limit) :
    checkedEntry .nil live p limit (stateAt H vs (h.pre.size + 6) ks) =
      some (stateAt (CommonDataReference.retired H j ReferenceHeap.nilObject)
        (updated .nil vs j 0 0) (h.pre.size + 3) ks, [.free j]) ∧
    Agrees live vs (updated .nil vs j 0 0) := by
  constructor
  · simpa [checkedEntry, safe, updated] using h.nil_entry found selected space bound
  · exact safe_preserves safe

/-- Agreement composes only when every seam preserves the same retained
observations. It does not discharge a changing lexical liveness analysis. -/
theorem Agrees.trans (ab : Agrees live a b) (bc : Agrees live b c) :
    Agrees live a c := fun k hk => (bc k hk).trans (ab k hk)

/-- A right sibling in slot five forbids another copied Node entry. -/
theorem node_rejects_sibling (liveSibling : 5 ∈ live) : ¬ Safe .node live := by
  intro hs; exact hs 5 liveSibling (by decide)

theorem nil_preserves_sibling : Safe .nil [5] := by decide

end Jihoo.CommonDataCaseRegisterSafety
