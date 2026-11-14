import Jihoo.NativeCheckerSoundness

/-! Kernel-checked executable regressions for native sorts, dependent type
abstraction, erasure modes, arithmetic evidence and exact constructor arity. -/
namespace Jihoo.NativeKernel.Checker.Examples

private def identity : Term :=
  .lam false (.univ 0) (.lam false (.var 0) (.var 0))

private def predicate : Term := .lam false .u64 (.eq (.var 0) (.var 0))

private def values : Term := .elements 2 [.integer (-7), .integer 9]

private def equalityContext : Context :=
  [⟨.app (.var 1) (.natural 7), true⟩,
   ⟨.eq (.natural 7) (.natural 7), true⟩,
   ⟨.pi false .u64 .prop, false⟩]

/-- The highest accepted universe literal infers the successor universe. -/
theorem universe_boundary : infer 8 [] true (.univ 31) = some (.univ 32) := by cbv

theorem universe_limit_rejected : infer 8 [] true (.univ 32) = none := by cbv

theorem prop_sort : infer 8 [] false .prop = some (.univ 0) := by cbv

theorem u64_sort : infer 8 [] false .u64 = some (.univ 0) := by cbv

theorem i64_sort : infer 8 [] false .i64 = some (.univ 0) := by cbv

/-- Predicative Pi formation computes the maximum of actual domain/result sorts. -/
theorem predicative_maximum : infer 12 [] true
    (.pi false (.univ 0) (.univ 1)) = some (.univ 2) := by cbv

/-- A Prop codomain remains Prop even over the highest accepted universe. -/
theorem impredicative_prop : infer 12 [] true
    (.pi false (.univ 31) (.eq (.natural 0) (.natural 0))) = some .prop := by cbv

theorem erased_proof_pi : infer 12 [] true
    (.pi true (.eq (.natural 0) (.natural 0)) (.eq (.natural 0) (.natural 0))) = some .prop := by cbv

/-- The native erased-U64 binder is represented and accepted. -/
theorem erased_index_function : infer 12 [] false (.lam true .u64 (.refl (.var 0))) =
    some (.pi true .u64 (.eq (.var 0) (.var 0))) := by cbv

theorem erased_index_application : check 16 [] false
    (.app (.lam true .u64 (.refl (.var 0))) (.natural 7))
    (.eq (.natural 7) (.natural 7)) = true := by cbv

/-- An erased index remains available while checking types and proofs. -/
theorem erased_index_in_type : infer 12 [] false (.lam true .u64 (.array (.var 0))) =
    some (.pi true .u64 (.univ 0)) := by cbv

theorem erased_runtime_use_rejected :
    infer 12 [] false (.lam true .u64 (.var 0)) = none := by cbv

theorem erased_ghost_use_accepted : infer 12 [] true (.lam true .u64 (.var 0)) =
    some (.pi true .u64 .u64) := by cbv

theorem runtime_proof_binder_rejected : infer 12 [] true
    (.lam false (.eq (.natural 0) (.natural 0)) (.natural 7)) = none := by cbv

theorem erased_i64_binder_rejected :
    infer 12 [] true (.lam true .i64 (.natural 7)) = none := by cbv

/-- One variable namespace carries both type binders and value binders. -/
theorem type_abstraction : infer 16 [] true identity =
    some (.pi false (.univ 0) (.pi false (.var 0) (.var 1))) := by cbv

theorem polymorphic_application : infer 24 [] true
    (.app (.app identity .u64) (.natural 7)) = some .u64 := by cbv

/-- Code polymorphism accepts a scalar type through the native first-order gate. -/
theorem runtime_type_application_accepted : infer 24 [] false (.app identity .u64) =
    some (.pi false .u64 .u64) := by cbv

theorem dependent_array_application : infer 24 [] true
    (.app (.app (.lam false .u64 (.lam false (.array (.var 0)) (.var 0))) (.natural 2)) values) =
    some (.array (.natural 2)) := by cbv

theorem array_read : infer 16 [] false
    (.index values (.natural 1) (.decide (.natural 1) (.natural 2))) = some .i64 := by cbv

theorem array_wrong_bound_rejected : infer 16 [] false
    (.index values (.natural 1) (.decide (.natural 1) (.natural 3))) = none := by cbv

theorem signed_arithmetic : infer 8 [] false
    (.arith .mul (.integer (-7)) (.integer 9)) = some .i64 := by cbv

theorem strict_sequence : infer 8 [] false
    (.strict (.arith .add (.integer 1) (.integer 2)) (.natural 7)) = some .u64 := by cbv

theorem subtraction_with_evidence : infer 12 [] false
    (.usub (.natural 5) (.natural 0) (.zeroLe (.natural 5))) = some .u64 := by cbv

theorem subtraction_forgery_rejected : infer 12 [] false
    (.usub (.natural 1) (.natural 2) (.decide (.natural 0) (.natural 1))) = none := by cbv

theorem arithmetic_evidence_add : infer 12 [] false
    (.ltAdd (.natural 1) (.natural 2) (.natural 3) (.decide (.natural 1) (.natural 2))) =
    some (.lt (.uadd (.natural 1) (.natural 3)) (.uadd (.natural 2) (.natural 3))) := by cbv

theorem arithmetic_evidence_cancel : infer 16 [] false
    (.ltCancel (.natural 1) (.natural 2) (.natural 3)
      (.ltAdd (.natural 1) (.natural 2) (.natural 3) (.decide (.natural 1) (.natural 2)))) =
    some (.lt (.natural 1) (.natural 2)) := by cbv

theorem arithmetic_evidence_le : infer 16 [] false
    (.ltLe (.natural 0) (.uadd (.natural 1) (.natural 1)) (.natural 2)
      (.zeroLe (.natural 1))
      (.ltAdd (.natural 1) (.natural 2) (.natural 1) (.decide (.natural 1) (.natural 2)))) =
    some (.lt (.natural 0) (.natural 2)) := by cbv

/-- Equality elimination is restricted to a U64-to-Prop family. -/
theorem transport_evidence : infer 16 equalityContext false
    (.transport (.var 2) (.var 1) (.var 0)) = some (.app (.var 2) (.natural 7)) := by cbv

theorem refinement_sort : infer 12 [] false (.refine predicate) = some (.univ 0) := by cbv

theorem refinement_pack : infer 16 [] false
    (.lam true (.app predicate (.natural 7)) (.pack predicate (.natural 7) (.var 0))) =
    some (.pi true (.app predicate (.natural 7)) (.refine predicate)) := by cbv

theorem refinement_witness : infer 8 [⟨.refine predicate, false⟩] false (.witness (.var 0)) =
    some .u64 := by cbv

theorem refinement_proof : infer 8 [⟨.refine predicate, true⟩] false (.proof (.var 0)) =
    some (.app predicate (.witness (.var 0))) := by cbv

/-- Exact native arity is checked instead of trusting an operator tag. -/
theorem malformed_scalar_rejected :
    infer 8 [] true (.node .u64 [.natural 0]) = none := by cbv

theorem malformed_vector_rejected :
    infer 8 [] true (.elements 1 [.integer 1, .integer 2]) = none := by cbv

theorem integer_bound_rejected : infer 8 [] true (.integer (2^63)) = none := by cbv

theorem unsigned_bound_rejected : infer 8 [] true (.natural (2^64)) = none := by cbv

/-- Full syntax does not give unproved ownership constructors a default rule. -/
theorem ownership_rule_pending :
    infer 8 [] false (.node .alloc [.natural 2, .integer 0]) = none := by cbv

/-- Verified conversion closes the former structural-only checking gap. -/
theorem arithmetic_conversion : check 12 [] true (.refl (.natural 1))
    (.eq (.uadd (.natural 0) (.natural 1)) (.natural 1)) = true := by cbv

theorem runtime_polymorphic_application : infer 24 [] false
    (.app (.app identity .u64) (.natural 7)) = some .u64 := by cbv

theorem function_type_argument_rejected :
    infer 24 [] false (.app identity (.pi false .u64 .u64)) = none := by cbv

/-- The expected kind prevents higher-kinded forwarding from bypassing plainness. -/
theorem higher_kind_argument_rejected : infer 24 [] false
    (.app (.lam false (.pi false (.univ 0) (.univ 0)) .u64)
      (.lam false (.univ 0) .u64)) = none := by cbv

theorem higher_kind_ghost_accepted : infer 24 [] true
    (.app (.lam false (.pi false (.univ 0) (.univ 0)) .u64)
      (.lam false (.univ 0) .u64)) = some (.univ 0) := by cbv

theorem beta_conversion : check 16 [] true (.refl (.natural 7))
    (.eq (.app (.lam false .u64 (.var 0)) (.natural 7)) (.natural 7)) = true := by cbv

theorem computed_decide : infer 12 [] false
    (.decide (.uadd (.natural 1) (.natural 1)) (.natural 3)) =
    some (.lt (.uadd (.natural 1) (.natural 1)) (.natural 3)) := by cbv

theorem closed_refinement_pack : infer 16 [] false
    (.pack predicate (.natural 7) (.refl (.natural 7))) = some (.refine predicate) := by cbv

theorem closed_refinement_witness : check 16 [] false
    (.witness (.pack predicate (.natural 7) (.refl (.natural 7)))) .u64 = true := by cbv

theorem closed_refinement_proof : check 16 [] false
    (.proof (.pack predicate (.natural 7) (.refl (.natural 7))))
    (.eq (.natural 7) (.natural 7)) = true := by cbv

theorem polymorphic_application_typed : HasType [] true
    (.app (.app identity .u64) (.natural 7)) .u64 := infer_sound polymorphic_application

end Jihoo.NativeKernel.Checker.Examples
