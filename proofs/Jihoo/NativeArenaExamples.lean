import Jihoo.NativeArena

/-! Executable arena regressions cover shared nodes visited at different
binding depths, ownership/vector fields, prefix preservation and rejection. -/
namespace Jihoo.NativeKernel.NativeArena.Examples

/-- The same Var 1 graph node occurs beneath the branch's evidence binder and
in the unbound false branch. Those occurrences must transform differently. -/
private def branches (op : Op) : Arena := #[
  .var 1,
  .node (.natural 0) [],
  .node (.natural 1) [],
  .node op [1, 2, 0, 0],
  .var 0]

private def branchResult (op : Op) : Option Term := do
  let result ← substitute 8 (branches op) 3 4
  decode 8 result.1 result.2

theorem ifLt_capture_avoiding : branchResult .ifLt =
    some (.node .ifLt [.node (.natural 0) [], .node (.natural 1) [], .var 1, .var 0]) := by
  decide +kernel

theorem ifEq_capture_avoiding : branchResult .ifEq =
    some (.node .ifEq [.node (.natural 0) [], .node (.natural 1) [], .var 1, .var 0]) := by
  decide +kernel

theorem original_shared_node_preserved :
    ((substitute 8 (branches .ifLt) 3 4).bind fun result => decode 8 result.1 0) =
      some (.var 1) := by
  decide +kernel

private def instantiateTree (body argument : Term) : Option Term := do
  let encodedBody := emit body #[]
  let encodedArgument := emit argument encodedBody.1
  let result ← substitute 32 encodedArgument.1 encodedBody.2 encodedArgument.2
  decode 32 result.1 result.2

theorem lambda_capture_avoiding : instantiateTree
    (.node (.lam false) [.node .u64 [], .var 1]) (.var 0) =
    some (.node (.lam false) [.node .u64 [], .var 1]) := by
  decide +kernel

theorem ownership_fields_transformed : instantiateTree
    (.node .lend [.var 0, .var 1, .var 2]) (.var 4) =
    some (.node .lend [.var 4, .var 0, .var 1]) := by
  decide +kernel

theorem vector_payload_and_case_binders : instantiateTree
    (.node (.view true 17 1) [.var 0, .node (.lam false) [.node .u64 [], .var 1], .var 1])
    (.node (.natural 7) []) =
    some (.node (.view true 17 1)
      [.node (.natural 7) [], .node (.lam false) [.node .u64 [], .node (.natural 7) []], .var 0]) := by
  decide +kernel

theorem inductive_ids_are_payloads : instantiateTree
    (.node (.con 0 1 2) [.var 0, .var 1]) (.node (.natural 7) []) =
    some (.node (.con 0 1 2) [.node (.natural 7) [], .var 0]) := by
  decide +kernel

theorem malformed_arity_rejected : decode 8 #[.var 0, .node .transport [0, 0]] 1 = none := by
  decide +kernel

theorem missing_root_rejected : decode 8 #[.var 0] 1 = none := by
  decide +kernel

theorem cyclic_graph_exhausts : decode 8 #[.node .array [0]] 0 = none := by
  decide +kernel

theorem zero_fuel_rejects : decode 0 (branches .ifLt) 3 = none := rfl

theorem shift_under_evidence :
    ((shift 8 (branches .ifEq) 3 2 0).bind fun result => decode 8 result.1 result.2) =
      some (.node .ifEq [.node (.natural 0) [], .node (.natural 1) [], .var 3, .var 3]) := by
  decide +kernel

end Jihoo.NativeKernel.NativeArena.Examples
