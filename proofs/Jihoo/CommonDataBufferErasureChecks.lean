import Jihoo.CommonDataBufferErasure

namespace Jihoo.CommonDataBufferErasureChecks
open CommonDataBufferErasure RecursiveLexicalFields RecursiveBodyProjection
open CommonDataErasure (Env position)
open CommonData RecursiveFieldOwnership HeapLeases LinearHeapPrograms

/-- The outer scalar is behind a ghost; scalar and Buffer binders then shift it. -/
def nodes (length : Nat) : CommonDataSource.Graph := #[
  .core .i64, .core (.natural length), .core (.buffer 1),
  .core (.var 1), .core (.var 0), .core (.alloc 1 4),
  .core (.var 0), .core (.integer 9), .core (.free 6 7),
  .core (.lam false 2 8), .core (.app 9 5),
  .core (.lam false 0 10), .core (.app 11 3)]

def target (length : Nat) : Term :=
  .scalarLet (.var 0) (.allocate length (.var 0) (.freeBuffer 0 (.literal 9)))

theorem lowered (n : Nat) : Lower (nodes n) [false,true,false] 12 (target n) :=
  .scalarLet rfl rfl rfl (.var rfl rfl)
    (.allocate rfl rfl rfl rfl rfl (.var rfl rfl)
      (.freeBuffer rfl rfl rfl (.literal rfl)))

local macro "shape" : term => `(by simp [CommonData.coreGraph,
  CommonDataSourceRules.graph, CommonData.projectNode, CommonDataSourceRules.adaptNode,
  CommonDataSource.adaptNode, ScopedLend.Graph.nodeAt, nodes])

theorem typed (n : Nat) (bound : n < 2^64) :
    CommonDataSourceRules.Typing (nodes n) [.ghost,.scalar,.ghost] 0 [] 12 .scalar := by
  apply CommonDataSourceRules.Typing.bufferLet rfl rfl rfl
  · exact .scalar (k := 1) shape rfl
  · apply CommonDataSourceRules.Typing.allocate (n := n) rfl rfl rfl
    · exact ⟨1, shape, .literal shape bound⟩
    · rfl
    · exact .literal shape bound
    · exact .var (k := 0) shape rfl
    · exact .freeBuffer (slot := 0) rfl rfl rfl (by simp) (.literal rfl (by decide))

theorem compacted (v : Nat) : Env [false,true,false]
    [.ghost,.scalar v,.ghost] [.scalar v] := .erase (.keep (.erase .nil))

/-- All bounded lengths and all scalar inputs, states and frames; no run premise. -/
theorem total (n v : Nat) (bound : n < 2^64)
    (valid : Valid s.buffers.heap) (owned : Owns s.buffers.heap frame) :
    ∃ result es t, Eval [.scalar v] (target n) s result es t ∧
      Steps s.buffers.heap es t.buffers.heap ∧ Valid t.buffers.heap ∧
      AccountedPost .scalar t result frame [] es := by
  apply total_accounted (typed n bound) (lowered n) (compacted v)
    (trees := []) (owners := []) rfl
  · exact .cons rfl (.cons ⟨v,rfl⟩ (.cons rfl .nil))
  · exact empty_layout
  · exact valid
  · exact owned
  · intro c mem; cases mem

/-- Exact allocation/free trace, full length map and unchanged Data cells. -/
theorem target_run (n v : Nat) (s : CommonData.State) :
    Eval [.scalar v] (target n) s (.scalar 9)
      [.alloc s.buffers.heap.nextObject v, .free s.buffers.heap.nextObject]
      ⟨SizedBufferHeap.release (SizedBufferHeap.allocate s.buffers n v)
        s.buffers.heap.nextObject, s.cells⟩ :=
  .scalarLet (.var rfl) (.allocate (.var rfl) (.freeBuffer rfl .literal))

/-- The same arbitrary input family runs in the existing source semantics. -/
theorem source_run (n v : Nat) (bound : n < 2^64) (s : CommonData.State) :
    CommonDataSourceExecution.Eval (nodes n) [.ghost,.scalar v,.ghost] 12 s (.scalar 9)
      [.alloc s.buffers.heap.nextObject v, .free s.buffers.heap.nextObject]
      ⟨SizedBufferHeap.release (SizedBufferHeap.allocate s.buffers n v)
        s.buffers.heap.nextObject, s.cells⟩ := by
  apply CommonDataSourceExecution.Eval.bufferLet (before := []) rfl rfl rfl
  · exact .var (core_shape (g := nodes n) (term := 3) rfl) rfl
  · apply CommonDataSourceExecution.Eval.allocate
      (before := [.alloc s.buffers.heap.nextObject n v]) rfl rfl rfl
    · exact .allocate (core_shape (g := nodes n) (term := 5) rfl)
        (.literal (core_shape (g := nodes n) (term := 1) rfl) bound)
        (.var (core_shape (g := nodes n) (term := 4) rfl) rfl)
    · exact .freeBuffer rfl rfl rfl (.literal rfl)

theorem target_preserved (n v : Nat) (bound : n < 2^64) (s : CommonData.State) :
    Eval [.scalar v] (target n) s (.scalar 9)
      [.alloc s.buffers.heap.nextObject v, .free s.buffers.heap.nextObject]
      ⟨SizedBufferHeap.release (SizedBufferHeap.allocate s.buffers n v)
        s.buffers.heap.nextObject, s.cells⟩ :=
  (lowered n).preserves (compacted v) (source_run n v bound s)

example : position [true,true,false,true,false] 3 = some 2 := rfl
example : position [false,true,false] 0 = none := rfl
example : ¬ Env [false] [.scalar v] [] := by intro h; cases h

#print axioms CommonDataBufferErasure.core_shape
#print axioms CommonDataBufferErasure.core_lookup
#print axioms CommonDataBufferErasure.ScalarLower.preserves
#print axioms CommonDataBufferErasure.ScalarLower.run
#print axioms CommonDataBufferErasure.natural_value
#print axioms CommonDataBufferErasure.Lower.preserves
#print axioms CommonDataBufferErasure.total_accounted
#print axioms lowered
#print axioms typed
#print axioms compacted
#print axioms total
#print axioms target_run
#print axioms source_run
#print axioms target_preserved
end Jihoo.CommonDataBufferErasureChecks
