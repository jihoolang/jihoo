import Jihoo.NativeFamilyWire

namespace Jihoo.NativeKernel.NativeFamilyWire.Examples

private def natRoots : FamilyRoots := ⟨true, 0, 0, 0, [0, 1]⟩
private def natGraph : NativeArena.Arena :=
  #[.node (.ind 0 0) [], .node (.pi false) [0, 0]]
private def snapshot : Snapshot := ⟨[], [natRoots], natGraph⟩

theorem recursive_signature_graph_roundtrip :
    decodeSnapshot (encodeSnapshot snapshot) = some snapshot := decodeSnapshot_encode snapshot

theorem recursive_family_graph_has_four_occurrences : expansionWork snapshot = some 4 := by cbv

theorem raw_family_metadata_and_constructor_order : decodeProgram snapshot =
    some ([], [⟨true, 0, 0, 0,
      [.node (.ind 0 0) [], .node (.pi false) [.node (.ind 0 0) [], .node (.ind 0 0) []]]⟩]) := by cbv

theorem raw_family_graph_meaning :
    NativeArena.RepresentsList natGraph [0, 1]
      [.node (.ind 0 0) [], .node (.pi false) [.node (.ind 0 0) [], .node (.ind 0 0) []]] :=
  decodeConstructors_sound (by cbv : [0, 1].mapM (NativeArena.decode 128 natGraph) = some _)

theorem missing_constructor_root_rejected :
    decodeProgram ⟨[], [⟨true, 0, 0, 0, [99]⟩], natGraph⟩ = none := by cbv

theorem unreachable_malformed_node_rejected :
    decodeProgram ⟨[], [natRoots], natGraph.push (.node .uadd [])⟩ = none := by cbv

theorem non_family_envelope_rejected : decodeSnapshot
    (NativeProgramWire.encodeSnapshot ⟨[], #[]⟩) = none := by cbv

theorem empty_mixed_program_decodes : decodeProgram ⟨[], [], #[]⟩ = some ([], []) := by cbv

end Jihoo.NativeKernel.NativeFamilyWire.Examples
