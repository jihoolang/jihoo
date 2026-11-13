import Jihoo.CommonDataRestrictedComposition

namespace Jihoo.CommonDataRestrictedCompositionChecks
open ReferenceCfg ReferenceCalls CommonDataCaseCfg CommonDataCaseRelocation
open CommonDataRestrictedComposition

def stop : Block := ⟨#[], .ret⟩
def child : Fragment := ⟨stop, stop, 4⟩
def padding : Array Block := #[failure, failure]
def program : Program := nestedProgram padding #[] 6 child

def heap : ReferenceHeap.Heap :=
  #[ReferenceHeap.node (.object 1 0) (.object 2 0),
    ReferenceHeap.nilObject, ReferenceHeap.nilObject]
def locals : Array (Option Value) :=
  #[none, none, none, none, none, none, some (.pointer 0 0)]

/-- The same nontrivial path preserves any suspended caller stack, with its
explicit bound. This uses the generic installed entry laws, not evaluation
of a closed stack. -/
theorem nested_run_framed (ks : List Continuation) (bound : ks.length ≤ limit) :
    CommonDataCaseRelocation.walk program 17 limit
      (stateAt heap locals 8 ks) =
    some (stateAt (CommonDataReference.retired heap 1 ReferenceHeap.nilObject)
      (nilLocals ((nodeLocals (locals.set! 0 (some (.pointer 0 0))) 0 1 2).set! 0
        (some (.pointer 1 0)))) 12 ks, [.free 1]) := by
  have outer := (parentPlacement padding #[] 6 child).node_entry
    (H := heap) (j := 0) (l := 1) (r := 2) (vs := locals)
    (by decide) (by decide) (by decide) bound
  have jump := nested_jump padding #[] 6 child (H := heap)
    (vs := nodeLocals (locals.set! 0 (some (.pointer 0 0))) 0 1 2)
    (b := 4) (Or.inr rfl) bound
  have inner := (childPlacement padding #[] 6 child).nil_entry
    (H := heap) (j := 1)
    (vs := nodeLocals (locals.set! 0 (some (.pointer 0 0))) 0 1 2)
    (by decide) (by decide) (by decide) bound
  simp [parentPlacement, childPlacement, padding] at outer jump inner
  change CommonDataCaseRelocation.walk (nestedProgram padding #[] 6 child)
    (11 + (1 + 5)) limit _ = _
  simp only [padding, Array.set!]
  rw [CommonDataCaseRelocation.walk_add, outer]
  dsimp only [Bind.bind, Option.bind]
  rw [CommonDataCaseRelocation.walk_add, jump]
  dsimp only [Bind.bind, Option.bind]
  rw [inner]
  rfl

/-- Nonzero relocation, selected root in slot six, Node then left Nil;
exactly 11 + 1 + 5 interpreter ticks in ONE program. -/
theorem nested_run : CommonDataCaseRelocation.walk program 17 0
    (stateAt heap locals 8 []) =
    some (stateAt (CommonDataReference.retired heap 1 ReferenceHeap.nilObject)
      (nilLocals ((nodeLocals (locals.set! 0 (some (.pointer 0 0))) 0 1 2).set! 0
        (some (.pointer 1 0)))) 12 [], [.free 1]) := nested_run_framed [] (by decide)


/-- Installation is inhabited for each of three fragments, with nonempty
prefix and suffix. This checks more than a two-fragment coincidence. -/
theorem three_placements (f : Fragment) (member : f ∈ [parent 6, child, parent 4]) :
    Nonempty (Placement
      (installedProgram (padding ++ assemble padding.size [parent 6, child, parent 4] ++ padding)) f) :=
  assemble_placement _ _ member _ _

/-- The concrete nested interpreter run also exports relational Steps. -/
theorem nested_steps : ReferenceCalls.Steps program
    (.running (stateAt heap locals 8 [])) [.free 1]
    (.running (stateAt (CommonDataReference.retired heap 1 ReferenceHeap.nilObject)
      (nilLocals ((nodeLocals (locals.set! 0 (some (.pointer 0 0))) 0 1 2).set! 0
        (some (.pointer 1 0)))) 12 [])) :=
  (walk_sound nested_run).steps

#print axioms Fragment.size
#print axioms linked_eq
#print axioms Placement.program
#print axioms assemble_size
#print axioms assemble_placement
#print axioms Placement.walk
#print axioms Placement.node_entry
#print axioms Placement.nil_entry
#print axioms nested_jump
#print axioms placed_induction
#print axioms nested_run
#print axioms nested_run_framed
#print axioms three_placements
#print axioms nested_steps
end Jihoo.CommonDataRestrictedCompositionChecks
