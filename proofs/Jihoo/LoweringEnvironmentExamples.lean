import Jihoo.LoweringEnvironment
namespace Jihoo.LoweringEnvironment.Examples

def mixed : List (Slot Nat) :=
  [.ghost, .value 11, .hypothesis 20 [21, 22], .ghost,
   .hypothesis 30 [], .value 11]

theorem capture_order : pack mixed = [11, 20, 21, 22, 30, 11] := by decide

theorem complete_roundtrip : decode (layout mixed) (pack mixed) = some mixed := by decide

theorem applied_suffix_retained :
    rebuild (layout mixed) (pack mixed ++ [91, 92]) = some (mixed, [91, 92]) :=
  rebuild_pack mixed [91, 92]

theorem truncated_hypothesis_rejected :
    (decode [.hypothesis 2] [20, 21] : Option (List (Slot Nat))) = none := by decide

theorem trailing_operand_rejected : decode (layout mixed) (pack mixed ++ [99]) = none := by decide

theorem missing_node_rejected :
    (decode [.hypothesis 0] [] : Option (List (Slot Nat))) = none := by decide

/-- The oldest and newest equal-valued slots still occupy distinct positions. -/
theorem newest_and_ghost : nativeLookup mixed 0 = some (.value 11) ∧
    nativeLookup mixed 5 = some .ghost := by decide

theorem unguarded_lookup_is_wrong :
    nativeLookup [.value 7] 4 = none ∧
    ([Slot.value 7] : List (Slot Nat))[1 - 1 - 4]? = some (.value 7) := by decide

/-- This counterexample makes descriptor authenticity an explicit obligation. -/
theorem pack_alone_not_injective :
    pack [Slot.value 7, .value 8] = pack [Slot.hypothesis 7 [8]] ∧
    [Slot.value 7, .value 8] ≠ [Slot.hypothesis 7 [8]] := by decide

/-- Same arity does not authenticate the order of operand values. -/
theorem swapped_operands_change_environment :
    decode [.value, .hypothesis 0] [8, 7] = some [Slot.value 8, .hypothesis 7 []] ∧
    [Slot.value 8, .hypothesis 7 []] ≠ [Slot.value 7, .hypothesis 8 []] := by decide

/-- A concrete caller/callee assignment with two separate hypothesis blocks. -/
theorem parameter_interpretation :
    ([Slot.ghost, .value 0, .hypothesis 1 [2, 3], .ghost,
       .hypothesis 4 [], .value 5].map
       (Slot.map (fun i => ([11, 20, 21, 22, 30, 11] : List Nat)[i]!))) = mixed := by decide

end Jihoo.LoweringEnvironment.Examples
