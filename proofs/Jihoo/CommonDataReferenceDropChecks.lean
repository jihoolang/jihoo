import Jihoo.CommonDataReferenceDrop
import Jihoo.CommonDataReferenceChecks

namespace Jihoo.CommonDataReferenceDropChecks
open CommonDataReference CommonDataReferenceChecks

def deadHeap : ReferenceHeap.Heap := heap.mapIdx fun j o =>
  if j = 0 then o else deadObject o

example : drop heap (.object 3 0) 2 = some (deadHeap, [3,1,2]) := by decide
example : drop heap (.object 3 0) 20 = some (deadHeap, [3,1,2]) := by decide
example : drop heap (.object 3 0) 1 = none := by decide
example : drop heap (.object 3 0) 0 = none := by decide
example : drop heap (.object 1 0) 1 =
    some (retired heap 1 ReferenceHeap.nilObject, [1]) := by decide
example : deadHeap[0]? = heap[0]? := by decide
example : drop deadHeap (.object 3 0) 2 = none := by decide
example : drop heap .null 2 = none := by decide
example : drop heap (.object 3 1) 2 = none := by decide
example : drop heap (.object 99 0) 2 = none := by decide
example : drop #[⟨true, #[some (.scalar 2)]⟩] (.object 0 0) 4 = none := by decide
example : drop #[⟨true, #[none]⟩] (.object 0 0) 4 = none := by decide
example : drop #[ReferenceHeap.node (.object 99 0) (.object 1 0), ReferenceHeap.nilObject]
    (.object 0 0) 3 = none := by decide
example : drop #[ReferenceHeap.node (.object 1 0) (.object 1 0), ReferenceHeap.nilObject]
    (.object 0 0) 3 = none := by decide
example : drop #[ReferenceHeap.node (.object 0 0) (.object 0 0)]
    (.object 0 0) 3 = none := by decide
example : drop #[ReferenceHeap.node .null (.object 1 0), ReferenceHeap.nilObject]
    (.object 0 0) 3 = none := by decide

-- Two source nodes, three boxed Nils, non-identity mapping and nontrivial depth.
def nested : ReferenceHeap.Heap := #[ReferenceHeap.nilObject,
  ReferenceHeap.node (.object 0 0) (.object 2 0), ReferenceHeap.nilObject,
  ReferenceHeap.node (.object 1 0) (.object 4 0), ReferenceHeap.nilObject, buffer]
example : (drop nested (.object 3 0) 3).map Prod.snd = some [3,1,0,2,4] := by decide
example : drop nested (.object 3 0) 2 = none := by decide
example : (drop nested (.object 3 0) 3).map (fun p => p.1[5]?) = some (some buffer) := by decide

example : ∃ t K, CommonData.Destroy (RecursiveFieldRuntime.root image.source) source
    (image.source.owners.map HeapLeases.Event.free) t ∧
    drop heap (.object image.target 0) 2 = some (K, image.ids) := by
  obtain ⟨t, K, src, _, _, _, dst, _⟩ := destroy_correspondence related source_valid
    (frame := []) (by simpa using related.owned) (fuel := 2) (by decide)
  exact ⟨t, K, src, dst⟩
end Jihoo.CommonDataReferenceDropChecks
