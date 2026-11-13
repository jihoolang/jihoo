import Jihoo.TreeCreateCorrectness

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Jihoo.TreeCreateCfg.Checks
open ReferenceCfg ReferenceCalls CommonDataReference
private def continuation : Block := ⟨#[], .ret⟩
private def nilProgram : Program := #[body false #[] continuation none]
private def nodeProgram : Program := #[body true #[] continuation none]

/-- Kernel evaluation of the real machine, independently of nil_prefix. -/
theorem nil_run :
    walk nilProgram 3 (stateAt 0 0 #[] (slots none none none none none #[]) []) =
      some (nilResult 0 #[] none none none none #[] [], [.alloc 0 8]) := by decide

/-- Existing boxed children, arbitrary initial scratch values, caller suffix,
and suspended continuation all survive the actual nine instructions. -/
private def heap : ReferenceHeap.Heap := #[ReferenceHeap.nilObject, ReferenceHeap.nilObject]
private def saved : List Continuation := [⟨19, 21, #[some (.i64 7)], ⟨2, false⟩⟩]
private def suffix : Array (Option Value) := #[some (.i64 42), some .null]
theorem node_run :
    walk nodeProgram 9 (stateAt 0 0 heap
      (slots (some (.pointer 99 5)) (some .null) (some (.i64 123))
        (some (.pointer 0 0)) (some (.pointer 1 0)) suffix) saved) =
      some (nodeResult 0 heap 0 1 suffix saved, [.alloc 2 24]) := by decide

/-- Object budget and word budget are enforced by the executable malloc. -/
theorem object_budget_rejected :
    walk nilProgram 1 (stateAt 0 0 (Array.replicate 512 ReferenceHeap.nilObject)
      (slots none none none none none #[]) []) = none := by decide

theorem word_budget_rejected :
    walk nodeProgram 1 (stateAt 0 0 #[⟨true, Array.replicate 4094 none⟩]
      (slots none none none (some (.pointer 0 0)) (some (.pointer 0 0)) #[]) []) = none := by decide

/-- Putting children only in the result/scratch slots violates the interface:
conversion fails rather than silently using an overwritten child. -/
theorem missing_children_rejected :
    walk nodeProgram 9 (stateAt 0 0 heap
      (slots (some (.pointer 0 0)) (some (.pointer 1 0)) none none none #[]) []) = none := by decide

/-- Equal child values can be transported, but joint ownership/separation in
node_total deliberately forbids interpreting them as two owned subtrees. -/
theorem aliased_children_transport :
    walk nodeProgram 9 (stateAt 0 0 heap
      (slots none none none (some (.pointer 0 0)) (some (.pointer 0 0)) #[]) []) =
      some (nodeResult 0 heap 0 0 #[] [], [.alloc 2 24]) := by decide

end Jihoo.TreeCreateCfg.Checks
