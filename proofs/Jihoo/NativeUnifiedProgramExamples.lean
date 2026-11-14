import Jihoo.NativeUnifiedProgram

namespace Jihoo.NativeKernel.UnifiedProgram.Examples
open Environment

private def ind (family : Nat) (indices : List Term := []) : Term := .node (.ind family indices.length) indices
private def con (family constructor : Nat) (fields : List Term := []) : Term :=
  .node (.con family constructor fields.length) fields
private def global (index : Nat) : Term := .node (.global index) []
private def accepts (definitions : List GlobalDeclaration) (familyDeclarations : List FamilyDeclaration) : Bool :=
  (checkProgram 40 40 definitions familyDeclarations).isSome

private def bits : FamilyDeclaration := ⟨true, 0, 0, [ind 0, .pi false .u64 (ind 0)], 0⟩
private def bitValue : GlobalDeclaration := ⟨ind 0, con 0 1 [.natural 7]⟩
private def boxed : FamilyDeclaration := ⟨true, 0, 0, [.pi false (.buffer (.natural 2)) (ind 0)], 0⟩
private def boxedValue : GlobalDeclaration := ⟨ind 0, con 0 0 [.alloc (.natural 2) (.integer 0)]⟩
private def dependentBuffer : FamilyDeclaration := ⟨true, 1, 1,
  [.pi true .u64 (.pi false (.buffer (.var 0)) (ind 0 [.var 1]))], 0⟩
private def dependentValue : GlobalDeclaration :=
  ⟨ind 0 [.natural 2], con 0 0 [.natural 2, .alloc (.natural 2) (.integer 0)]⟩
private def recursion : FamilyDeclaration := ⟨true, 0, 0, [ind 0, .pi false (ind 0) (ind 0)], 0⟩

theorem empty_program : accepts [] [] = true := by cbv

theorem family_valued_global : accepts [bitValue] [bits] = true := by cbv

theorem later_global_expands_family_value : accepts [bitValue, ⟨ind 0, global 0⟩] [bits] = true := by cbv

theorem earlier_flat_family_field : accepts []
    [bits, ⟨true, 0, 0, [.pi false (ind 0) (ind 1)], 0⟩] = true := by cbv

theorem earlier_flat_constructor_global : accepts
    [⟨ind 1, con 1 0 [con 0 1 [.natural 7]]⟩]
    [bits, ⟨true, 0, 0, [.pi false (ind 0) (ind 1)], 0⟩] = true := by cbv

theorem buffer_field : accepts [] [boxed] = true := by cbv

theorem owned_family_global : accepts [boxedValue] [boxed] = true := by cbv

theorem earlier_boxed_family_field : accepts []
    [boxed, ⟨true, 0, 0, [.pi false (ind 0) (ind 1)], 0⟩] = true := by cbv

theorem earlier_boxed_constructor_global : accepts
    [⟨ind 1, con 1 0 [con 0 0 [.alloc (.natural 2) (.integer 0)]]⟩]
    [boxed, ⟨true, 0, 0, [.pi false (ind 0) (ind 1)], 0⟩] = true := by cbv

theorem dependent_buffer_field : accepts [] [dependentBuffer] = true := by cbv

theorem dependent_buffer_global : accepts [dependentValue] [dependentBuffer] = true := by cbv

theorem recursive_family : accepts [] [recursion] = true := by cbv

theorem recursive_constructor_global : accepts [⟨ind 0, con 0 1 [con 0 0]⟩] [recursion] = true := by cbv

theorem mixed_definition_family_order : accepts
    [bitValue, ⟨ind 1, con 1 0 [global 0]⟩]
    [bits, ⟨true, 0, 0, [.pi false (ind 0) (ind 1)], 1⟩] = true := by cbv

theorem resource_valued_global : accepts
    [⟨.buffer (.natural 2), .alloc (.natural 2) (.integer 0)⟩] [] = true := by cbv

theorem resource_function_global : accepts
    [⟨.pi false (.buffer (.natural 2)) .i64,
      .lam false (.buffer (.natural 2)) (.free (.var 0) (.integer 0))⟩] [] = true := by cbv

theorem rejects_resource_leak : accepts
    [⟨.pi false (.buffer (.natural 2)) .i64, .lam false (.buffer (.natural 2)) (.integer 0)⟩] [] = false := by cbv

theorem rejects_hidden_self_domain : accepts []
    [⟨true, 0, 0, [.pi false (.pi false (ind 0) .u64) (ind 0)], 0⟩] = false := by cbv

theorem rejects_heap_flat_mix : accepts []
    [bits, ⟨true, 0, 0, [.pi false (ind 0) (.pi false (.buffer (.natural 2)) (ind 1))], 0⟩] = false := by cbv

theorem rejects_forward_global : accepts [⟨.i64, global 0⟩] [] = false := by cbv

end Jihoo.NativeKernel.UnifiedProgram.Examples
