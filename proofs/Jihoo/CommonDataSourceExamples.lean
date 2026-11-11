import Jihoo.CommonDataSource
import Jihoo.CommonDataApplicationExamples

namespace Jihoo.CommonDataSourceExamples
open CommonDataSource CommonData HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime
open RecursiveLexicalFields

/-- Exact constructor view emitted after the production checker finishes.
All nodes, including checker-appended unused nodes, retain their original IDs. -/
def source : Source := {
  root := 29
  typeRoot := 8
  family := ⟨true,0,0,0,[0,5]⟩
  nodes := #[
    .ind 0 [],
    .ind 0 [],
    .ind 0 [],
    .ind 0 [],
    .core (.pi false 2 3),
    .core (.pi false 1 4),
    .ind 0 [],
    .core (.i64),
    .core (.pi false 6 7),
    .ind 0 [],
    .ind 0 [],
    .core (.var 0),
    .core (.integer 99),
    .drop 0 11 12,
    .core (.lam false 10 13),
    .ind 0 [],
    .ind 0 [],
    .core (.lam false 15 16),
    .con 0 0 [],
    .ind 0 [],
    .ind 0 [],
    .core (.var 1),
    .core (.var 0),
    .con 0 1 [21,22],
    .core (.lam false 20 23),
    .core (.lam false 19 24),
    .core (.var 0),
    .caseOf 0 17 [18,25] 26,
    .core (.app 14 27),
    .core (.lam false 9 28),
    .core (.u64),
    .core (.u64),
    .core (.u64),
    .core (.u64),
    .core (.u64),
    .core (.opaque),
    .core (.opaque),
    .core (.opaque),
    .core (.u64),
    .core (.opaque),
    .core (.u64),
    .core (.opaque),
    .core (.i64),
    .core (.pi false 10 42),
    .core (.u64),
    .core (.opaque),
    .core (.u64),
    .core (.opaque),
    .core (.pi false 15 47),
    .ind 0 [],
    .con 0 0 [],
    .core (.app 17 50),
    .core (.var 1),
    .core (.var 0),
    .con 0 1 [52,53],
    .core (.app 17 54),
    .core (.pi false 2 55),
    .core (.pi false 1 56),
    .core (.u64),
    .core (.opaque),
    .core (.u64),
    .core (.opaque),
    .core (.pi false 20 3),
    .core (.pi false 19 62),
    .core (.pi false 2 16),
    .core (.pi false 1 64),
    .core (.app 17 26),
    .core (.u64),
    .core (.opaque),
    .core (.i64),
    .core (.pi false 10 69),
    .core (.u64),
    .core (.opaque),
    .core (.u64),
    .core (.opaque),
    .core (.pi false 15 74),
    .ind 0 [],
    .con 0 0 [],
    .core (.app 17 77),
    .core (.var 1),
    .core (.var 0),
    .con 0 1 [79,80],
    .core (.app 17 81),
    .core (.pi false 2 82),
    .core (.pi false 1 83),
    .core (.u64),
    .core (.opaque),
    .core (.u64),
    .core (.opaque),
    .core (.pi false 20 3),
    .core (.pi false 19 89),
    .core (.pi false 2 16),
    .core (.pi false 1 91),
    .core (.app 17 26),
    .core (.pi false 9 42)] }

abbrev graph := source.nodes.map (adaptNode source.nodes)

theorem source_valid : valid source = true ∧ familyValid source = true := by decide

theorem entry_decoded : entry source = some (graph,28) := by rfl

theorem target_valid : CommonData.validGraph graph = true := by
  simp only [CommonData.validGraph, Array.size_map, adapted_at]
  decide

local macro "source_shape" : term => `(by first | rfl | (rw [adapted_at]; rfl))

theorem entry_typed : Typing graph [.data 0] 1 [] 28 .scalar :=
  .dataLet source_shape source_shape source_shape
    (.caseTree (count := 0) source_shape source_shape source_shape (.empty source_shape)
      (.construct source_shape source_shape source_shape source_shape source_shape))
    (.drop (count := 0) source_shape source_shape source_shape (.literal source_shape (by decide)))

/-- The checked source fixture's adapted body has a safe terminating execution
for every finitely represented, exclusively owned binary input and frame.
This is abstract target safety, not native execution refinement. -/
theorem entry_total {s : CommonData.State} {tree : Tree} (fields : Represents s.cells tree) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (tree.owners ++ frame)) :
    ∃ value events final, Eval graph [.data (root tree)] 28 s value events final ∧
      Steps s.buffers.heap events final.buffers.heap ∧ Valid final.buffers.heap ∧
      Post .scalar final value frame := by
  apply entry_typed.total (trees := [tree]) (owners := []) rfl
    (.cons ⟨tree,rfl,rfl⟩ .nil) empty_layout valid
    (by simpa [caps,footprint,Capability.owners] using owned)
  intro c member
  simp [caps] at member
  subst c
  exact fields

end Jihoo.CommonDataSourceExamples
