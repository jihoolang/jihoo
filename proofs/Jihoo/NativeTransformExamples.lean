import Jihoo.NativeTransform

/-! Direct arena execution regressions. These functions follow references and
thread work/allocation state, independently of the tree-mediated adapters. -/
namespace Jihoo.NativeKernel.NativeTransform.Examples

private def arena : NativeArena.Arena := #[
  .var 1, .node .u64 [], .node (.lam false) [1, 0], .var 0,
  .node .ifLt [3, 0, 3, 0]]

private def output (depth work limit root : Nat) (delta : Int) (cutoff : Nat) : Option Term := do
  let result ← shift depth work limit arena root delta cutoff
  NativeArena.decode 16 result.arena result.root

theorem negative_shift : output 8 32 64 0 (-1) 0 = some (.var 0) := by decide +kernel

theorem escaping_slot_rejected : shift 8 32 64 arena 3 (-1) 0 = none := by decide +kernel

theorem unchanged_variable_reused :
    (shift 8 32 5 arena 3 1 1).map (fun result => (result.arena.size, result.root, result.remaining)) =
      some (5, 3, 31) := by decide +kernel

theorem zero_delta_still_allocates_above_cutoff :
    (shift 8 32 64 arena 0 0 0).map (fun result => (result.arena.size, result.root)) =
      some (6, 5) := by decide +kernel

theorem lambda_cutoff_increment : output 8 32 64 2 1 0 =
    some (.node (.lam false) [.node .u64 [], .var 2]) := by decide +kernel

theorem lambda_escape_rejected : shift 8 32 64 arena 2 (-1) 0 = none := by decide +kernel

theorem branch_evidence_cutoff_increment : output 8 32 64 4 2 0 =
    some (.node .ifLt [.var 2, .var 3, .var 0, .var 3]) := by decide +kernel

theorem exact_total_work_budget :
    (shift 2 3 64 arena 2 1 0).map Result.remaining = some 0 := by decide +kernel

theorem insufficient_total_work_rejected : shift 8 2 64 arena 2 1 0 = none := by decide +kernel

theorem insufficient_depth_rejected : shift 1 32 64 arena 2 1 0 = none := by decide +kernel

theorem exhausted_allocation_rejected : shift 8 32 5 arena 0 0 0 = none := by decide +kernel

theorem reused_node_needs_no_allocation :
    (shift 8 1 5 arena 3 0 1).map Result.remaining = some 0 := by decide +kernel

theorem u32_output_wrap_rejected :
    shift 8 32 64 #[.var (2^32 - 1)] 0 1 0 = none := by decide +kernel

theorem signed_addition_overflow_guard :
    shift 8 32 64 #[.var 0] 0 (2^63 - 1) 0 = none := by decide +kernel

theorem cutoff_increment_wrap_guard :
    shift 8 32 64 #[.var 0] 0 1 (2^32 - 1) = none := by decide +kernel

theorem original_prefix_unchanged :
    ((shift 8 32 64 arena 2 1 0).bind fun result => NativeArena.decode 8 result.arena 2) =
      some (.node (.lam false) [.node .u64 [], .var 1]) := by decide +kernel

theorem malformed_arity_rejected :
    shift 8 32 64 #[.var 0, .node (.lam false) [0]] 1 1 0 = none := by decide +kernel

theorem cycle_exhausts_depth : shift 8 32 64 #[.node .array [0]] 0 0 0 = none := by decide +kernel

end Jihoo.NativeKernel.NativeTransform.Examples
