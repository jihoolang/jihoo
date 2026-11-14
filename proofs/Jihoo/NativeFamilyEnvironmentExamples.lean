import Jihoo.NativeFamilyEnvironment

/-! Kernel-checked constructor declarations, native telescope restrictions,
parameter invariance, storage classification and interleaved visibility. -/
namespace Jihoo.NativeKernel.FamilyEnvironment.Examples

private def ind (family : Nat) (xs : List Term) : Term := .node (.ind family xs.length) xs
private def global (g : Nat) : Term := .node (.global g) []
private def valid (fuel : Nat) (definitions : List Definitions.Definition) (families : List Declaration) : Bool :=
  (checkProgram fuel definitions families).isSome

private def bits (family : Nat) : Declaration :=
  ⟨true,0,0,[ind family [], .pi false .u64 (ind family [])],0⟩

private def naturals : Declaration :=
  ⟨true,0,0,[ind 0 [], .pi false (ind 0 []) (ind 0 [])],0⟩

private def chain : Declaration :=
  ⟨false,0,2,
    [.pi false .u64 (ind 0 [.var 0,.var 0]),
     .pi false .u64 (.pi false .u64 (.pi false .u64
       (.pi true (.eq (.var 2) (.var 1))
         (.pi true (ind 0 [.var 2,.var 1]) (ind 0 [.var 4,.var 2])))))],0⟩

private def parameterized : Declaration :=
  ⟨true,1,1,
    [.pi true .u64 (ind 0 [.var 0]),
     .pi true .u64 (.pi false .u64 (.pi false (ind 0 [.var 1]) (ind 0 [.var 2])))],0⟩

private def predicate : Term := .lam false .u64 (.eq (.var 0) (.var 0))

/-- Runtime scalar fields yield flat data; recursion yields a boxed data type. -/
theorem bits_accepted : valid 24 [] [bits 0] = true := by cbv

theorem bits_flat : (checkProgram 24 [] [bits 0]).map
    (fun env => env.families[0]?.map (·.boxed)) = some (some false) := by cbv

theorem recursive_data_accepted : valid 24 [] [naturals] = true := by cbv

theorem recursive_data_boxed : (checkProgram 24 [] [naturals]).map
    (fun env => env.families[0]?.map (·.boxed)) = some (some true) := by cbv

theorem proposition_chain_accepted : valid 32 [] [chain] = true := by cbv

theorem proposition_has_no_runtime_box : (checkProgram 32 [] [chain]).map
    (fun env => env.families[0]?.map (·.boxed)) = some (some false) := by cbv

theorem recursive_parameters_accepted : valid 32 [] [parameterized] = true := by cbv

theorem normalized_result_indices : (checkFamily 24 #[] #[]
    ⟨false,0,1,[ind 0 [.uadd (.natural 2) (.natural 3)]],0⟩).map
    (fun family => family.signatures.head?.map (·.result)) = some (some [.natural 5]) := by cbv

theorem signed_scalar_field : valid 24 []
    [⟨true,0,0,[.pi false .i64 (ind 0 [])],0⟩] = true := by cbv

theorem refinement_scalar_field : valid 24 []
    [⟨true,0,0,[.pi false (.refine predicate) (ind 0 [])],0⟩] = true := by cbv

theorem erased_equality_field : valid 24 []
    [⟨false,0,0,[.pi true (.eq (.natural 0) (.natural 1)) (ind 0 [])],0⟩] = true := by cbv

/-- A constructor can use earlier checked aliases in ordinary domains. -/
theorem interleaved_global_alias : valid 24 [⟨.univ 0,.u64⟩]
    [⟨false,0,1,[.pi false (global 0) (ind 0 [.var 0])],1⟩] = true := by cbv

theorem interleaved_definition_after_family : valid 24 [⟨.u64,.natural 7⟩]
    [bits 0] = true := by cbv

theorem two_ordered_families : (checkProgram 24 [] [bits 0,bits 1]).map
    (fun env => env.families.size) = some 2 := by cbv

theorem empty_program : valid 0 [] [] = true := by cbv

theorem wrong_result_family_rejected : valid 24 [] [bits 0,bits 0] = false := by cbv

theorem forward_family_rejected : valid 24 [] [bits 1] = false := by cbv

theorem missing_global_rejected : valid 24 []
    [⟨false,0,1,[.pi false (global 0) (ind 0 [.var 0])],0⟩] = false := by cbv

theorem later_global_rejected : valid 24 [⟨.univ 0,.u64⟩]
    [⟨false,0,1,[.pi false (global 0) (ind 0 [.var 0])],0⟩] = false := by cbv

theorem family_after_end_rejected : valid 24 [] [{ bits 0 with globals := 1 }] = false := by cbv

theorem backward_family_order_rejected : valid 24 [⟨.u64,.natural 7⟩]
    [{ bits 0 with globals := 1 },bits 1] = false := by cbv

theorem arity_limit_rejected : valid 24 [] [⟨false,0,17,[],0⟩] = false := by cbv

theorem excessive_parameters_rejected : valid 24 [] [⟨true,2,1,[],0⟩] = false := by cbv

theorem proposition_parameters_rejected : valid 24 [] [⟨false,1,1,[],0⟩] = false := by cbv

theorem result_arity_rejected : valid 24 [] [⟨false,0,1,[ind 0 []],0⟩] = false := by cbv

theorem malformed_index_vector_rejected : valid 24 []
    [⟨false,0,1,[.node (.ind 0 1) [.natural 0,.natural 0]],0⟩] = false := by cbv

theorem out_of_range_index_rejected : valid 24 []
    [⟨false,0,1,[ind 0 [.natural (2^64)]],0⟩] = false := by cbv

theorem free_index_rejected : valid 24 [] [⟨false,0,1,[ind 0 [.var 0]],0⟩] = false := by cbv

/-- The literal family occurrence under an arrow never becomes a recursive field. -/
theorem negative_function_field_rejected : valid 24 []
    [⟨false,0,0,[.pi true (.pi true (ind 0 []) (.eq (.natural 0) (.natural 0))) (ind 0 [])],0⟩] = false := by cbv

theorem beta_hidden_recursion_rejected : valid 24 []
    [⟨false,0,0,[.pi true (.app (.lam false (.univ 0) (.var 0)) (ind 0 [])) (ind 0 [])],0⟩] = false := by cbv

theorem relevant_proposition_recursion_rejected : valid 24 []
    [⟨false,0,0,[.pi false (ind 0 []) (ind 0 [])],0⟩] = false := by cbv

theorem erased_data_recursion_rejected : valid 24 []
    [⟨true,0,0,[.pi true (ind 0 []) (ind 0 [])],0⟩] = false := by cbv

theorem proposition_i64_field_rejected : valid 24 []
    [⟨false,0,0,[.pi false .i64 (ind 0 [])],0⟩] = false := by cbv

theorem relevant_proof_field_rejected : valid 24 []
    [⟨false,0,0,[.pi false (.eq (.natural 0) (.natural 0)) (ind 0 [])],0⟩] = false := by cbv

theorem relevant_function_field_rejected : valid 24 []
    [⟨true,0,0,[.pi false (.pi false .u64 .u64) (ind 0 [])],0⟩] = false := by cbv

theorem changed_recursive_parameter_rejected : valid 32 []
    [⟨true,1,1,[.pi true .u64 (.pi false (ind 0 [.natural 0]) (ind 0 [.var 1]))],0⟩] = false := by cbv

theorem changed_result_parameter_rejected : valid 24 []
    [⟨true,1,1,[.pi true .u64 (ind 0 [.natural 0])],0⟩] = false := by cbv

theorem relevant_parameter_rejected : valid 24 []
    [⟨true,1,1,[.pi false .u64 (ind 0 [.var 0])],0⟩] = false := by cbv

/-- Checking every raw index rejects evidence which beta computation discards. -/
theorem discarded_false_evidence_rejected : valid 32 []
    [⟨false,0,1,[ind 0 [.app (.lam true (.eq (.natural 0) (.natural 1)) (.natural 0)) (.refl (.natural 0))]],0⟩] = false := by cbv

theorem normalized_telescope_rejected : valid 24 []
    [⟨false,0,1,[.app (.lam false .u64 (ind 0 [.natural 0])) (.natural 0)],0⟩] = false := by cbv

/-- These native features deliberately need the next family-aware judgment. -/
theorem earlier_family_field_gap : valid 24 []
    [bits 0,⟨true,0,0,[.pi false (ind 0 []) (ind 1 [])],0⟩] = false := by cbv

theorem buffer_field_gap : valid 24 []
    [⟨true,0,0,[.pi false (.node .buffer [.natural 2]) (ind 0 [])],0⟩] = false := by cbv

theorem family_term_use_gap : valid 24
    [⟨ind 0 [],.node (.con 0 0 0) []⟩] [bits 0] = false := by cbv

theorem checker_fuel_exhaustion : valid 0 [] [bits 0] = false := by cbv

private theorem accepted (h : valid fuel definitions families = true) :
    ∃ env, ProgramChecked definitions families env := by
  unfold valid at h
  cases hc : checkProgram fuel definitions families with
  | none => simp [hc] at h
  | some env => exact ⟨env,checkProgram_sound hc⟩

theorem recursive_parameters_semantic : ∃ env, ProgramChecked [] [parameterized] env :=
  accepted recursive_parameters_accepted

theorem chain_positive : ∀ t ∈ chain.constructors, Positive 0 t := by
  have passed : (checkFamily 32 #[] #[] chain).isSome = true := by cbv
  cases hc : checkFamily 32 #[] #[] chain with
  | none => simp [hc] at passed
  | some entry => exact (checkFamily_sound hc).constructors_positive

end Jihoo.NativeKernel.FamilyEnvironment.Examples
