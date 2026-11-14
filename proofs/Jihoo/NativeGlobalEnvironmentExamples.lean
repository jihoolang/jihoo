import Jihoo.NativeGlobalEnvironment

/-! Executable global-environment regressions check whole programs, exact
transparent expansions, declaration modes and resource accounting. -/
namespace Jihoo.NativeKernel.GlobalEnvironment.Examples

private def global (g : Nat) : Term := .node (.global g) []

private def constants : List Declaration :=
  [⟨.u64, .natural 3⟩,
   ⟨.u64, .uadd (global 0) (.natural 4)⟩,
   ⟨.eq (global 1) (.natural 7), .refl (global 1)⟩]

private def constantEnvironment : Environment :=
  #[⟨.u64, .natural 3⟩,
    ⟨.u64, .uadd (.natural 3) (.natural 4)⟩,
    ⟨.eq (.uadd (.natural 3) (.natural 4)) (.natural 7),
      .refl (.uadd (.natural 3) (.natural 4))⟩]

private def aliases : List Declaration :=
  [⟨.univ 0, .u64⟩, ⟨global 0, .natural 7⟩]

private def proofFunction : Declaration :=
  ⟨.pi true .u64 (.eq (.var 0) (.var 0)), .lam true .u64 (.refl (.var 0))⟩

private def proofIdentity : Declaration :=
  ⟨.pi true (.eq (.natural 0) (.natural 0)) (.eq (.natural 0) (.natural 0)),
    .lam true (.eq (.natural 0) (.natural 0)) (.var 0)⟩

private def repeatedEnvironment : Environment :=
  #[⟨.u64, .uadd (.natural 1) (.natural 2)⟩]

/-- Body conversion validates later evidence about earlier computed globals. -/
theorem constants_accepted : validateProgram 24 constants = true := by cbv

theorem constants_exact : checkProgram 24 constants = some constantEnvironment := by cbv

/-- A global may denote a type and be used in a later annotation. -/
theorem type_alias_accepted : validateProgram 24 aliases = true := by cbv

theorem type_alias_exact : (checkProgram 24 aliases).map (fun env => env[1]?.map (·.type)) =
    some (some .u64) := by cbv

/-- The erased parameter is available because this declaration's sort is Prop. -/
theorem proof_function_accepted : validateProgram 24
    [proofFunction, ⟨.eq (.natural 7) (.natural 7), .app (global 0) (.natural 7)⟩] = true := by cbv

theorem proof_identity_accepted : validateProgram 24 [proofIdentity] = true := by cbv

/-- A closed inserted body never captures an enclosing term variable. -/
theorem global_below_binders : (checkProgram 24
    [⟨.u64, .natural 3⟩,
     ⟨.pi false .u64 (.pi false .u64 .u64),
       .lam false .u64 (.lam false .u64 (.uadd (global 0) (.var 1)))⟩]).map
       (fun env => env[1]?.map (·.value)) =
    some (some (.lam false .u64 (.lam false .u64 (.uadd (.natural 3) (.var 1))))) := by cbv

/-- Dependent arrays and proof arguments are checked after transparent lookup. -/
theorem dependent_array_global : validateProgram 32
    [⟨.pi false .u64 (.pi false (.array (.var 0)) (.array (.var 1))),
       .lam false .u64 (.lam false (.array (.var 0)) (.var 0))⟩,
     ⟨.array (.natural 2),
       .app (.app (global 0) (.natural 2)) (.elements 2 [.integer (-2), .integer 9])⟩] = true := by cbv

theorem empty_program : validateProgram 0 [] = true := by cbv

theorem self_reference_rejected : validateProgram 24 [⟨.u64, global 0⟩] = false := by cbv

theorem forward_value_rejected : validateProgram 24
    [⟨.u64, global 1⟩, ⟨.u64, .natural 3⟩] = false := by cbv

theorem forward_type_rejected : validateProgram 24
    [⟨global 1, .natural 3⟩, ⟨.univ 0, .u64⟩] = false := by cbv

theorem malformed_global_rejected : validateProgram 24
    [⟨.u64, .natural 3⟩, ⟨.u64, .node (.global 0) [.natural 0]⟩] = false := by cbv

theorem unsupported_family_rejected : validateProgram 24
    [⟨.univ 0, .node (.ind 0 0) []⟩] = false := by cbv

theorem universe_overflow_rejected : validateProgram 24
    [⟨.univ 32, .univ 31⟩] = false := by cbv

theorem false_equality_rejected : validateProgram 24
    [⟨.eq (.natural 0) (.natural 1), .refl (.natural 0)⟩] = false := by cbv

/-- There is no caller-supplied ghost bit to bypass declaration body checking. -/
theorem runtime_erased_use_rejected : validateProgram 24
    [⟨.pi true .u64 .u64, .lam true .u64 (.var 0)⟩] = false := by cbv

/-- Core can use an opaque proof global in code through Strict. The eager
transparent checker conservatively rejects its expanded erased runtime use. -/
theorem opaque_proof_code_boundary : validateProgram 24
    [proofIdentity, ⟨.u64, .strict (global 0) (.natural 7)⟩] = false := by cbv

theorem wrong_declared_type_rejected : validateProgram 24
    [⟨.i64, .natural 7⟩] = false := by cbv

theorem expansion_fuel_exhausted : expand 0 #[] (.natural 0) = none := by cbv

theorem declaration_fuel_exhausted : validateProgram 0 [⟨.u64, .natural 0⟩] = false := by cbv

/-- A repeated global is charged for each inserted tree occurrence. -/
theorem repeated_global_exact_budget : expandWork 8 repeatedEnvironment 7
    (.uadd (global 0) (global 0)) =
    some (.uadd (.uadd (.natural 1) (.natural 2)) (.uadd (.natural 1) (.natural 2)), 0) := by cbv

theorem repeated_global_budget_rejected : expandWork 8 repeatedEnvironment 6
    (.uadd (global 0) (global 0)) = none := by cbv

theorem copied_body_precharged : expandWork 1 repeatedEnvironment 2 (global 0) = none := by cbv

private def nested : Nat → Term
  | 0 => .natural 0
  | n + 1 => .refl (nested n)

set_option maxRecDepth 4096 in
theorem copied_body_depth_rejected : expandWork 1 #[⟨.u64, nested 129⟩] 200000 (global 0) = none := by cbv

/-- Executable success feeds independent semantic and input safety theorems. -/
theorem constants_semantically_checked : SequentiallyChecked constants constantEnvironment :=
  checkProgram_sound constants_exact

theorem constants_ordered : Before 2 (constants[2]).value := by
  exact constants_semantically_checked.ordered (i := 2) (by rfl) |>.2

theorem final_global_typed :
    ∃ sort : SortTag, HasType [] true (constantEnvironment[2]).type sort.term ∧
      HasType [] (Definitions.bodyMode sort) (constantEnvironment[2]).value
        (constantEnvironment[2]).type :=
  checked_global_typed (g := 2) constants_semantically_checked (by rfl)

theorem final_correspondence :
    Expansion constantEnvironment (constants[2]).value (constantEnvironment[2]).value :=
  (checkProgram_correspondence (i := 2) constants_exact (by rfl) (by rfl)).2.1

end Jihoo.NativeKernel.GlobalEnvironment.Examples
