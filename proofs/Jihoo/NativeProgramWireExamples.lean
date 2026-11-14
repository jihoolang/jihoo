import Jihoo.NativeProgramWire

namespace Jihoo.NativeKernel.NativeProgramWire.Examples

private def base : NativeArena.Arena :=
  #[.node .u64 [], .node (.natural 7) [], .node (.global 0) []]

private def chain : Snapshot := ⟨[⟨0, 1⟩, ⟨0, 2⟩], base⟩

theorem ordered_declarations_decode :
    (decodeDefinitions chain).map List.length = some 2 := by cbv

theorem full_graph_roundtrip : decodeSnapshot (encodeSnapshot chain) = some chain :=
  decodeSnapshot_encode chain

theorem aggregate_expansion_counts_repeated_roots : expansionWork chain = some 4 := by cbv

theorem empty_program : decodeDefinitions ⟨[], #[]⟩ = some [] := by cbv

theorem missing_declaration_root_rejected :
    decodeDefinitions ⟨[⟨0, 99⟩], base⟩ = none := by cbv

theorem unreachable_cycle_rejected : decodeDefinitions
    ⟨[⟨0, 1⟩], base.push (.node .uadd [3, 3])⟩ = none := by cbv

theorem unreachable_malformed_node_rejected : decodeDefinitions
    ⟨[⟨0, 1⟩], base.push (.node .uadd [])⟩ = none := by cbv

theorem declaration_limit_checked_before_expansion :
    decodeDefinitions ⟨List.replicate 1025 ⟨0, 1⟩, base⟩ = none := by
  simp only [decodeDefinitions, structureValid, List.length_replicate,
    show decide (1025 ≤ 1024) = false from rfl, Bool.and_false, Bool.false_and,
    Bool.false_eq_true, ite_false]

theorem old_observation_envelope_rejected : decodeSnapshot
    (NativeWire.encodeSnapshot ⟨true, 1, 0, base⟩) = none := by cbv

theorem invalid_empty_bytes_rejected : decodeSnapshot ByteArray.empty = none := by cbv

end Jihoo.NativeKernel.NativeProgramWire.Examples
