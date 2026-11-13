import Jihoo.CommonCaseChildConsumption

/-! Enclosing source Case with explicit child consumption. This hand-written
restricted source graph is not a production compiler export or lowering proof. -/
namespace Jihoo.CommonCaseSourceConsumption
open RecursiveLexicalFields RecursiveFieldOwnership RecursiveFieldRuntime
open CommonData HeapLeases LinearHeapPrograms

/-- IDs 0--4 retain the drop/drop/literal body. The Node branch binds left,
then right; its runtime lexical order is [right,left,outer...], with no ghosts. -/
def graph (n : Nat) : CommonDataSource.Graph := #[
  .core (.var 1), .core (.var 0), .core (.integer n),
  .drop 0 1 2, .drop 0 0 3,
  .ind 0 [], .core .i64, .core (.lam false 5 6),
  .core (.lam false 5 4), .core (.lam false 5 8),
  .caseOf 0 7 [2,9] 1, .core (.lam false 5 10),
  .core (.pi false 5 6), .core (.pi false 5 5), .core (.pi false 5 13)]

/-- Exactly one data capability, no buffer inventory; arbitrary lexical tail
must still satisfy Agrees for totality. Dead aliases are retired by Case. -/
theorem typed (bound : n < 2^63) :
    CommonDataSourceRules.Typing (graph n) (.data 0 :: ctx) 1 [] 10 .scalar :=
  .caseTree rfl rfl rfl rfl rfl (.literal rfl bound)
    (.drop rfl rfl rfl (.drop rfl rfl rfl (.literal rfl bound)))

/-- No source or target execution premise. All tree and ambient ownership is
accounted for; the parent is consumed by Case, its children by explicit drops. -/
theorem total (bound : n < 2^63)
    (agreement : Agrees (caps [tree] []) (.data 0 :: ctx) env)
    (layout : SizedBufferContext.Layout s.buffers [] [])
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps [tree] []) ++ frame))
    (fields : Fields s.cells (caps [tree] [])) :
    ∃ v es t, CommonDataSourceExecution.Eval (graph n) env 10 s v es t ∧
      Steps s.buffers.heap es t.buffers.heap ∧ Valid t.buffers.heap ∧
      AccountedPost .scalar t v frame (footprint (caps [tree] [])) es :=
  CommonDataSourceExecution.total_accounted (typed bound) rfl agreement layout valid owned fields

/-- Every initial tree allocation, including the parent, is freed exactly once. -/
theorem tree_released (bound : n < 2^63)
    (agreement : Agrees (caps [tree] []) (.data 0 :: ctx) env)
    (layout : SizedBufferContext.Layout s.buffers [] [])
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps [tree] []) ++ frame))
    (fields : Fields s.cells (caps [tree] []))
    (run : CommonDataSourceExecution.Eval (graph n) env 10 s (.scalar value) es t)
    (member : x ∈ footprint (caps [tree] [])) :
    (released es).count x = 1 ∧ t.buffers.heap.live x = false :=
  (typed bound).elaborate.other_released rfl agreement layout valid owned fields
    run.to_common rfl (.inl member) (by simp)

/-- Ambient reservations remain live and never occur in the release trace. -/
theorem frame_survives (bound : n < 2^63)
    (agreement : Agrees (caps [tree] []) (.data 0 :: ctx) env)
    (layout : SizedBufferContext.Layout s.buffers [] [])
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps [tree] []) ++ frame))
    (fields : Fields s.cells (caps [tree] []))
    (run : CommonDataSourceExecution.Eval (graph n) env 10 s (.scalar value) es t)
    (member : x ∈ frame) : t.buffers.heap.live x = true ∧ x ∉ released es :=
  (typed bound).elaborate.survivors rfl agreement layout valid owned fields
    run.to_common (output := []) rfl (by simpa using member)

end Jihoo.CommonCaseSourceConsumption
