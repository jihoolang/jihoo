import Jihoo.CommonDataCaseRegisterSafety
import Jihoo.CommonDataRestrictedCompositionChecks

namespace Jihoo.CommonDataCaseRegisterSafetyChecks
open ReferenceCfg ReferenceCalls CommonDataCaseCfg CommonDataCaseRelocation
open CommonDataRestrictedComposition CommonDataCaseRegisterSafety

def stop : Block := ⟨#[], .ret⟩
def child : Fragment := ⟨stop, stop, 4⟩
def padding : Array Block := #[failure, failure]
def program : Program := nestedProgram padding #[] 6 child

/-- Outer right sibling is object 2; inner right child is object 4. -/
def heap : ReferenceHeap.Heap :=
  #[ReferenceHeap.node (.object 1 0) (.object 2 0),
    ReferenceHeap.node (.object 3 0) (.object 4 0), ReferenceHeap.nilObject,
    ReferenceHeap.nilObject, ReferenceHeap.nilObject]
def locals : Array (Option Value) :=
  #[none, none, none, none, none, none, some (.pointer 0 0)]
def outerLocals := updated .node locals 0 1 2
def innerLocals := updated .node outerLocals 1 3 4

/-- Actual 11+1+11 ticks in ONE installed program, arbitrary suspended callers. -/
theorem collision_run (ks : List Continuation) (bound : ks.length ≤ limit) :
    CommonDataCaseRelocation.walk program 23 limit (stateAt heap locals 8 ks) =
      some (stateAt heap innerLocals 13 ks, []) := by
  have outer := (parentPlacement padding #[] 6 child).node_entry
    (H := heap) (j := 0) (l := 1) (r := 2) (vs := locals)
    (by decide) (by decide) (by decide) bound
  have jump := nested_jump padding #[] 6 child (H := heap)
    (vs := outerLocals) (b := 4) (Or.inr rfl) bound
  have inner := (childPlacement padding #[] 6 child).node_entry
    (H := heap) (j := 1) (l := 3) (r := 4) (vs := outerLocals)
    (by decide) (by decide) (by decide) bound
  simp [parentPlacement, childPlacement, padding] at outer jump inner
  change CommonDataCaseRelocation.walk (nestedProgram padding #[] 6 child)
    (11 + (1 + 11)) limit _ = _
  simp only [padding]
  rw [CommonDataCaseRelocation.walk_add, outer]
  dsimp only [Bind.bind, Option.bind]
  change (do
    let (u, es) ← CommonDataCaseRelocation.walk (nestedProgram padding #[] 6 child)
      (1 + 11) limit (stateAt heap outerLocals 6 ks)
    pure (u, [] ++ es)) = _
  simp only [padding]
  rw [CommonDataCaseRelocation.walk_add, jump]
  dsimp only [Bind.bind, Option.bind]
  rw [inner]
  rfl

/-- The sibling has really been overwritten, despite an unchanged heap. -/
theorem sibling_overwritten :
    outerLocals[5]? = some (some (.pointer 2 0)) ∧
    innerLocals[5]? = some (some (.pointer 4 0)) ∧
    ¬ Agrees [5] outerLocals innerLocals := by
  constructor
  · decide
  constructor
  · decide
  · intro h; have bad := h 5 (by simp); contradiction

/-- Reject the unsafe nested Node before running any entry ticks. -/
theorem collision_prevented (ks : List Continuation) (limit : Nat) :
    checkedEntry .node [5] program limit (stateAt heap outerLocals 15 ks) = none :=
  unsafe_rejected (node_rejects_sibling (by simp))

theorem live_context_rejected :
    ¬ Nonempty (RestrictedPlacement program child .node [.data 1] [5]) :=
  no_node_layout (k := 0) rfl rfl trivial

/-- If only slot six is retained, the same inner Node is allowed and preserves
it. This is a register test, not a claim that the omitted sibling is consumed. -/
theorem safe_node_runs (ks : List Continuation) (bound : ks.length ≤ limit) :
    checkedEntry .node [6] program limit (stateAt heap outerLocals 15 ks) =
      some (stateAt heap innerLocals 13 ks, []) ∧ Agrees [6] outerLocals innerLocals := by
  simpa [childPlacement, padding, program, innerLocals] using
    checked_node (childPlacement padding #[] 6 child) (live := [6]) (by decide)
      (H := heap) (j := 1) (l := 3) (r := 4) (vs := outerLocals)
      (by decide) (by decide) (by decide) bound

/-- The existing Node→Nil regression is admitted with the sibling still live. -/
theorem safe_nil_runs (ks : List Continuation) (bound : ks.length ≤ limit) :
    let H := CommonDataRestrictedCompositionChecks.heap
    checkedEntry .nil [5] program limit (stateAt H outerLocals 15 ks) =
      some (stateAt (CommonDataReference.retired H 1 ReferenceHeap.nilObject)
        (updated .nil outerLocals 1 0 0) 12 ks, [.free 1]) ∧
    Agrees [5] outerLocals (updated .nil outerLocals 1 0 0) := by
  simpa [childPlacement, padding, program] using
    checked_nil (childPlacement padding #[] 6 child) nil_preserves_sibling
      (H := CommonDataRestrictedCompositionChecks.heap) (j := 1) (vs := outerLocals)
      (by decide) (by decide) (by decide) bound

/-- No existential-only execution certificate: export actual machine Steps. -/
theorem collision_steps : ReferenceCalls.Steps program
    (.running (stateAt heap locals 8 [])) []
    (.running (stateAt heap innerLocals 13 [])) :=
  (walk_sound (collision_run [] (limit := 0) (by decide))).steps

#print axioms safe_preserves
#print axioms safe_iff_uniform
#print axioms safe_reserved
#print axioms RestrictedPlacement.reserved
#print axioms no_node_layout
#print axioms live_context_rejected
#print axioms unsafe_rejected
#print axioms checked_node
#print axioms checked_nil
#print axioms Agrees.trans
#print axioms node_rejects_sibling
#print axioms nil_preserves_sibling
#print axioms collision_run
#print axioms sibling_overwritten
#print axioms collision_prevented
#print axioms safe_node_runs
#print axioms safe_nil_runs
#print axioms collision_steps
end Jihoo.CommonDataCaseRegisterSafetyChecks
