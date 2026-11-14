import Jihoo.NativeReplacementTransform

/-! Direct substitution/rewrite executions include graph sharing between the
body and argument, binder capture avoidance, lazy reuse, and exact work limits. -/
namespace Jihoo.NativeKernel.NativeTransform.ReplacementExamples

private def arena : NativeArena.Arena := #[
  .var 0, .var 1, .var 4, .node .u64 [], .node (.lam false) [3, 1],
  .node .ifEq [0, 1, 1, 1], .node .lend [0, 1, 2], .node .ifLt [0, 1, 0, 0]]

private def output (operation : Option Result) : Option Term := do
  let result ← operation
  NativeArena.decode 16 result.arena result.root

theorem substitute_shared_argument_and_body : output (substitute 8 64 128 arena 6 2) =
    some (.node .lend [.var 4, .var 0, .var 3]) := by decide +kernel

theorem rewrite_retains_higher_slots : output (rewrite 8 64 128 arena 6 0 2) =
    some (.node .lend [.var 4, .var 1, .var 4]) := by decide +kernel

theorem substitute_under_lambda : output (substitute 8 64 128 arena 4 2) =
    some (.node (.lam false) [.node .u64 [], .var 5]) := by decide +kernel

theorem rewrite_under_lambda : output (rewrite 8 64 128 arena 4 0 2) =
    some (.node (.lam false) [.node .u64 [], .var 5]) := by decide +kernel

theorem substitute_under_true_branch : output (substitute 8 64 128 arena 5 2) =
    some (.node .ifEq [.var 4, .var 0, .var 5, .var 0]) := by decide +kernel

theorem rewrite_under_true_branch : output (rewrite 8 64 128 arena 5 0 2) =
    some (.node .ifEq [.var 4, .var 1, .var 5, .var 1]) := by decide +kernel

theorem substitute_keeps_local_evidence : output (substitute 8 64 128 arena 7 2) =
    some (.node .ifLt [.var 4, .var 0, .var 0, .var 4]) := by decide +kernel

theorem matched_variable_counts_shift_visit :
    (substitute 2 2 128 arena 0 2).map Result.remaining = some 0 := by decide +kernel

theorem matched_variable_work_exhaustion : substitute 8 1 128 arena 0 2 = none := by decide +kernel

theorem matched_variable_depth_exhaustion : substitute 1 64 128 arena 0 2 = none := by decide +kernel

theorem rewrite_unmatched_variable_reuses :
    (rewrite 1 1 8 arena 1 0 2).map (fun result => (result.arena.size, result.root, result.remaining)) =
      some (8, 1, 0) := by decide +kernel

theorem substitute_unmatched_variable_allocates :
    (substitute 1 1 128 arena 1 2).map (fun result => (result.arena.size, result.root, result.remaining)) =
      some (9, 8, 0) := by decide +kernel

theorem substitute_needs_allocation_capacity : substitute 1 1 8 arena 1 2 = none := by decide +kernel

theorem replacement_graph_is_traversed :
    (substitute 3 4 128 arena 0 4).map Result.remaining = some 0 := by decide +kernel

theorem replacement_graph_meaning : output (substitute 3 4 128 arena 0 4) =
    some (.node (.lam false) [.node .u64 [], .var 1]) := by decide +kernel

theorem replacement_graph_work_exhaustion : substitute 8 3 128 arena 0 4 = none := by decide +kernel

theorem invalid_replacement_reference_rejected : substitute 8 64 128 arena 0 99 = none := by decide +kernel

theorem replacement_shift_wrap_rejected : substitute 8 64 128
    #[.var 0, .var 1, .var (2^32 - 1), .node .u64 [], .node (.lam false) [3, 1]] 4 2 =
      none := by decide +kernel

theorem original_body_prefix_preserved :
    ((substitute 8 64 128 arena 6 2).bind fun result => NativeArena.decode 8 result.arena 6) =
      some (.node .lend [.var 0, .var 1, .var 4]) := by decide +kernel

theorem invalid_target_index_rejected : rewrite 8 64 128 arena 0 (2^32) 2 = none := by decide +kernel

end Jihoo.NativeKernel.NativeTransform.ReplacementExamples
