import Jihoo.NativeArenaPartial

/-! Kernel-reduced regressions for real scope-removal failure and native
no-removal rewriting, including both evidence-binding branches. -/
namespace Jihoo.NativeKernel.PartialRenaming.Examples

theorem zero_slot_rejected : lower 0 1 (.var 0) = none := by decide +kernel

theorem higher_slot_lowered : lower 0 1 (.var 1) = some (.var 0) := by decide +kernel

theorem removed_block_rejected : lower 2 3 (.var 4) = none := by decide +kernel

theorem removed_block_upper_boundary : lower 2 3 (.var 5) = some (.var 2) := by decide +kernel

theorem signed_shift_success : shift (-2) 1 (.var 3) = some (.var 1) := by decide +kernel

theorem signed_shift_underflow_rejected : shift (-2) 1 (.var 2) = none := by decide +kernel

theorem local_lambda_binder_preserved :
    lower 0 1 (.node (.lam false) [.node .u64 [], .var 0]) =
      some (.node (.lam false) [.node .u64 [], .var 0]) := by decide +kernel

theorem lambda_escape_rejected :
    lower 0 1 (.node (.lam false) [.node .u64 [], .var 1]) = none := by decide +kernel

theorem free_variable_under_lambda_lowered :
    lower 0 1 (.node (.lam false) [.node .u64 [], .var 2]) =
      some (.node (.lam false) [.node .u64 [], .var 1]) := by decide +kernel

theorem branch_local_evidence_preserved :
    lower 0 1 (.node .ifLt [.node (.natural 0) [], .node (.natural 1) [], .var 0, .var 1]) =
      some (.node .ifLt [.node (.natural 0) [], .node (.natural 1) [], .var 0, .var 0]) := by
  decide +kernel

theorem true_branch_escape_rejected :
    lower 0 1 (.node .ifEq [.node (.natural 0) [], .node (.natural 1) [], .var 1, .var 1]) =
      none := by decide +kernel

theorem false_branch_escape_rejected :
    lower 0 1 (.node .ifLt [.node (.natural 0) [], .node (.natural 1) [], .var 0, .var 0]) =
      none := by decide +kernel

theorem rewrite_keeps_higher_slots : rewrite 0 (.var 4)
    (.node .lend [.var 0, .var 1, .var 2]) =
      .node .lend [.var 4, .var 1, .var 2] := by decide +kernel

theorem rewrite_shifts_only_replacement_under_branch : rewrite 0 (.var 4)
    (.node .ifEq [.node (.natural 0) [], .node (.natural 1) [], .var 1, .var 1]) =
      .node .ifEq [.node (.natural 0) [], .node (.natural 1) [], .var 5, .var 1] := by
  decide +kernel

theorem rewrite_preserves_local_evidence : rewrite 0 (.var 4)
    (.node .ifLt [.node (.natural 0) [], .node (.natural 1) [], .var 0, .var 0]) =
      .node .ifLt [.node (.natural 0) [], .node (.natural 1) [], .var 0, .var 4] := by
  decide +kernel

theorem rewrite_shifts_under_lambda : rewrite 0 (.var 4)
    (.node (.lam false) [.node .u64 [], .var 1]) =
      .node (.lam false) [.node .u64 [], .var 5] := by decide +kernel

theorem rewrite_preserves_family_payloads : rewrite 0 (.node (.natural 7) [])
    (.node (.con 0 1 2) [.var 0, .var 3]) =
      .node (.con 0 1 2) [.node (.natural 7) [], .var 3] := by decide +kernel

private def arena : NativeArena.Arena := #[
  .var 0, .var 1, .node .array [0], .node .array [1]]

theorem arena_escape_rejected : NativeArenaPartial.lower 8 arena 2 0 1 = none := by
  decide +kernel

theorem arena_scope_removed :
    ((NativeArenaPartial.lower 8 arena 3 0 1).bind fun result =>
      NativeArena.decode 8 result.1 result.2) = some (.node .array [.var 0]) := by
  decide +kernel

theorem arena_old_prefix_preserved :
    ((NativeArenaPartial.lower 8 arena 3 0 1).bind fun result =>
      NativeArena.decode 8 result.1 3) = some (.node .array [.var 1]) := by
  decide +kernel

theorem arena_signed_shift :
    ((NativeArenaPartial.shift 8 arena 3 (-1) 0).bind fun result =>
      NativeArena.decode 8 result.1 result.2) = some (.node .array [.var 0]) := by
  decide +kernel

theorem arena_rewrite_retains_binder :
    ((NativeArenaPartial.rewrite 8 arena 2 0 1).bind fun result =>
      NativeArena.decode 8 result.1 result.2) = some (.node .array [.var 1]) := by
  decide +kernel

end Jihoo.NativeKernel.PartialRenaming.Examples
