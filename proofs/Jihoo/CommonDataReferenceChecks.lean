import Jihoo.CommonDataReference

set_option maxRecDepth 20000

namespace Jihoo.CommonDataReferenceChecks
open CommonDataReference

-- Source identity 7 maps to target identity 3; target 1 and 2 are extra Nils.
-- Target 0 is an unrelated retained buffer.
def image : Image := .node 7 3 (.nil 1) (.nil 2)
def buffer : ReferenceHeap.Object := ⟨true, #[some (.scalar 42), some (.scalar 42)]⟩
def heap : ReferenceHeap.Heap :=
  #[buffer, ReferenceHeap.nilObject, ReferenceHeap.nilObject,
    ReferenceHeap.node (.object 1 0) (.object 2 0)]
def source : CommonData.State :=
  ⟨⟨⟨8, 0, fun x => x == 7 || x == 4, fun _ => 42, fun _ => none⟩, fun _ => 2⟩,
    fun x => if x = 7 then some ⟨none,none⟩ else none⟩

theorem related : Related source heap image := by
  constructor
  · simp [source, image, Image.source, RecursiveFieldRuntime.Represents, RecursiveFieldRuntime.root]
  · constructor
    · simp [image, Image.source, RecursiveFieldOwnership.Tree.owners]
    · intro x hx
      simp only [image, Image.source, RecursiveFieldOwnership.Tree.owners, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      subst x
      rfl
    · simp [source, HeapLeases.Unborrowed]
  · simp [Layout, heap, image, Image.target]
  · decide

theorem source_valid : HeapLeases.Valid source.buffers.heap := by
  constructor
  · intro x live
    simp [source] at live ⊢
    omega
  · simp [source]

theorem retained_buffer : BufferRelated source heap 4 0 := by
  constructor <;> decide

theorem finished_buffer :
    BufferRelated (CommonData.finish source 7) (retired heap 3 image.object) 4 0 :=
  retained_buffer.finish (by decide) (by decide)

theorem finished_children :
    Related (CommonData.finish source 7) (retired heap 3 image.object) (.nil 1) ∧
    Related (CommonData.finish source 7) (retired heap 3 image.object) (.nil 2) :=
  (finish_children source_valid related).2

example : image.pairs = [(7,3)] ∧ image.nils = [1,2] := by decide
example : image.source.owners = [7] ∧ image.ids = [3,1,2] := by decide
example : makeNil #[buffer] = some #[buffer, ReferenceHeap.nilObject] := by decide
example : makeNode #[buffer, ReferenceHeap.nilObject, ReferenceHeap.nilObject] 1 2 = some heap := by decide
example : openNode heap 3 = some (.object 1 0, .object 2 0) := by decide
example : RecursiveLexicalFields.enter source.recursive [.data (some 7)] 0 0 =
    some ([.data none, .data none, .data (some 7)], 7) := by decide
example : ReferenceHeap.loadScalar heap (.object 1 0) = some 0 := by decide
example : openNode heap 1 = none := by decide
example : ReferenceHeap.release heap (.object 3 0) = some (retired heap 3 image.object) := by decide
example : ReferenceHeap.loadRef (retired heap 3 image.object) (.object 3 1) = none := by decide
example : ReferenceHeap.loadScalar (retired heap 3 image.object) (.object 0 1) = some 42 := by decide
example : ReferenceHeap.release (retired heap 3 image.object) (.object 3 0) = none := by decide
example : ¬ Layout heap (.node 7 3 (.nil 99) (.nil 2)) := by simp [Layout, heap, Image.target, ReferenceHeap.node, ReferenceHeap.pointerToWord]
example : ¬ (Image.node 7 3 (.nil 1) (.nil 1)).ids.Nodup := by decide
example : makeNil (Array.replicate 512 ReferenceHeap.nilObject) = none := by decide
example : makeNode #[⟨true, Array.replicate 4094 none⟩] 0 0 = none := by decide
example : makeNil #[⟨true, Array.replicate 4096 none⟩] = none := by decide

end Jihoo.CommonDataReferenceChecks
