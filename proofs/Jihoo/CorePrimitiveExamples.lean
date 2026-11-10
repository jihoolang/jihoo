import Jihoo.CorePayloadErasure
import Jihoo.CoreBridgeExamples

namespace Jihoo.CoreBridge.Raw.Beta.PrimitiveExamples

def values : List Raw := [.integer (-signedBound), .integer 37, .integer (signedBound - 1)]
def arrayType : Raw := .array (.natural 3)
def boundType : Raw := .lt (.natural 2) (.natural 3)
def boundProof : Raw := .decide (.natural 2) (.natural 3)
def proofIdType : Raw := .pi true boundType boundType
def proofId : Raw := .lam true boundType (.var 0)
def higherProof : Raw := .app (.lam true proofIdType (.app (.var 0) boundProof)) proofId
def preparedArray : Raw := .app (.lam false arrayType (.var 0)) (.elements values)

private theorem values_typed (Γ : Context) : ∀ x ∈ values, HasType Γ x .i64 := by
  intro x hx
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact .integer (by decide) (by decide)
private theorem array_typed (Γ : Context) : HasType Γ (.elements values) arrayType :=
  .elements (values_typed Γ) (by decide)
private theorem bound_formed (Γ : Context) : IsType Γ boundType :=
  .lt (.natural (by decide)) (.natural (by decide))
private theorem bound_typed (Γ : Context) : HasType Γ boundProof boundType :=
  .decide (by decide) (by decide) (by decide)
private theorem proof_id_typed (Γ : Context) : HasType Γ proofId proofIdType :=
  .lam (bound_formed Γ) rfl (.var (by simp [Context.extend, boundType, rename]))

theorem higher_proof_typed (Γ : Context) : HasType Γ higherProof boundType := by
  have body : HasType (Γ.extend proofIdType) (.app (.var 0) boundProof) boundType := by
    have f : HasType (Γ.extend proofIdType) (.var 0) proofIdType :=
      .var (by simp [Context.extend, proofIdType, boundType, rename])
    simpa only [proofIdType, boundType, subst] using HasType.app f (bound_typed _)
  have function : HasType Γ (.lam true proofIdType (.app (.var 0) boundProof))
      (.pi true proofIdType boundType) :=
    .lam (.pi (bound_formed Γ) rfl (bound_formed _)) rfl body
  simpa only [higherProof, boundType, subst] using HasType.app function (proof_id_typed Γ)

theorem prepared_array_typed (Γ : Context) : HasType Γ preparedArray arrayType := by
  have identity : HasType Γ (.lam false arrayType (.var 0)) (.pi false arrayType arrayType) :=
    .lam (.array (.natural (by decide))) rfl
      (.var (by simp [Context.extend, arrayType, rename]))
  simpa only [preparedArray, arrayType, subst] using HasType.app identity (array_typed Γ)

def readFirst : Raw := .index (.elements values) (.natural 0) (.decide (.natural 0) (.natural 3))
def readLast : Raw := .index preparedArray (.natural 2) higherProof
def readComputed : Raw := .index preparedArray (.uadd (.natural 1) (.natural 1)) higherProof

theorem read_first_typed : HasType (fun _ => none) readFirst .i64 :=
  .index (array_typed _) (.natural (by decide)) (.decide (by decide) (by decide) (by decide))
theorem read_last_typed : HasType (fun _ => none) readLast .i64 :=
  .index (prepared_array_typed _) (.natural (by decide)) (higher_proof_typed _)
theorem read_computed_typed : HasType (fun _ => none) readComputed .i64 :=
  .index (prepared_array_typed _) (.uadd (.natural (by decide)) (.natural (by decide)))
    (.convert (higher_proof_typed _) (.lt (.symm (.add 1 1 (by decide))) (.refl _)))

theorem read_last_safe : ∃ v, ArrayRead preparedArray 2 v ∧ HasType (fun _ => none) v .i64 :=
  read_last_typed.closed_read_progress
theorem read_computed_safe : ∃ v, ArrayRead preparedArray 2 v ∧ HasType (fun _ => none) v .i64 :=
  read_computed_typed.evaluated_index_safe (.next (.add 1 1 (by decide)) .refl)

def maxWord : Nat := wordBound - 1
def maxProof : Raw := .zeroLe (.natural maxWord)
def maxSubtract : Raw := .usub (.natural maxWord) (.natural 0) maxProof

theorem max_proof_typed (Γ : Context) :
    HasType Γ maxProof (.lt (.natural 0) (.uadd (.natural maxWord) (.natural 1))) :=
  .zeroLe (.natural (by decide))
theorem max_subtract_typed : HasType (fun _ => none) maxSubtract .u64 :=
  .usub (.natural (by decide)) (.natural (by decide)) (max_proof_typed _)
theorem max_subtract_safe : 0 ≤ maxWord ∧ maxWord - 0 < wordBound ∧
    HasType (fun _ => none) (.natural (maxWord - 0)) .u64 := max_subtract_typed.closed_usub_safe

def ten : Raw := .app (.lam false .u64 (.var 0)) (.natural 10)
def three : Raw := .uadd (.natural 1) (.natural 2)
def subtract : Raw := .usub ten three (.decide (.natural 3) (.natural 11))

theorem subtract_typed : HasType (fun _ => none) subtract .u64 := by
  have identity : HasType (fun _ => none) (.lam false .u64 (.var 0)) (.pi false .u64 .u64) :=
    .lam .u64 rfl (.var (by simp [Context.extend, rename]))
  have ht : HasType (fun _ => none) ten .u64 := by
    simpa only [ten, subst] using HasType.app identity (HasType.natural (n := 10) (by decide))
  have ct : Conv ten (.natural 10) := by
    simpa only [ten, subst, single] using Conv.beta false .u64 (.var 0) (.natural 10)
  have cb : Conv three (.natural 3) := .add 1 2 (by decide)
  exact .usub ht (.uadd (.natural (by decide)) (.natural (by decide)))
    (.convert (.decide (by decide) (by decide) (by decide))
      (.lt cb.symm ((Conv.add 10 1 (by decide)).symm.trans (.uadd ct.symm (.refl _)))))

theorem subtract_safe : 3 ≤ 10 ∧ 10 - 3 < wordBound ∧
    HasType (fun _ => none) (.natural (10 - 3)) .u64 := by
  apply subtract_typed.evaluated_usub_safe
  · have hs : Computation.Step ten (.natural 10) := by
      simpa only [ten, subst, single] using Computation.Step.beta false .u64 (.var 0) (.natural 10)
    exact .next hs .refl
  · exact .next (.add 1 2 (by decide)) .refl

theorem subtract_computes : Computation.Steps subtract (.natural 7) := by
  apply (subtract_typed.evaluated_sub_computes (x := 10) (y := 3) ?_ ?_).1
  · have hs : Computation.Step ten (.natural 10) := by
      simpa only [ten, subst, single] using Computation.Step.beta false .u64 (.var 0) (.natural 10)
    exact .next hs .refl
  · exact .next (.add 1 2 (by decide)) .refl

def nestedSubtract : Raw := .usub subtract (.natural 5) (.decide (.natural 5) (.natural 8))

theorem nested_subtract_typed : HasType (fun _ => none) nestedSubtract .u64 :=
  .usub subtract_typed (.natural (by decide))
    (.convert (.decide (by decide) (by decide) (by decide))
      (.lt (.refl _) ((Conv.add 7 1 (by decide)).symm.trans
        (.uadd subtract_computes.conversion.symm (.refl _)))))

theorem nested_subtract_computes : Computation.Steps nestedSubtract (.natural 2) :=
  (nested_subtract_typed.evaluated_sub_computes subtract_computes .refl).1

def readSubtracted : Raw := .index preparedArray nestedSubtract boundProof

theorem read_subtracted_typed : HasType (fun _ => none) readSubtracted .i64 :=
  .index (prepared_array_typed _) nested_subtract_typed
    (.convert (bound_typed _) (.lt nested_subtract_computes.conversion.symm (.refl _)))

theorem read_subtracted_safe : ∃ v, ArrayRead preparedArray 2 v ∧ HasType (fun _ => none) v .i64 :=
  read_subtracted_typed.evaluated_index_safe nested_subtract_computes

def subDomain : Raw := .eq nestedSubtract (.natural 2)
def subLambda : Raw := .lam true subDomain (.integer 9)

theorem sub_lambda_typed : HasType (fun _ => none) subLambda (.pi true subDomain .i64) :=
  .lam (.eq nested_subtract_typed (.natural (by decide))) rfl (.integer (by decide) (by decide))

theorem sub_annotation_preserved :
    HasType (fun _ => none) (.lam true (.eq (.natural 2) (.natural 2)) (.integer 9))
      (.pi true subDomain .i64) := by
  exact Computation.preservation_steps sub_lambda_typed
    (nested_subtract_computes.map (fun n => .lam true (.eq n (.natural 2)) (.integer 9))
      (fun hs => .lamDomain (.eqLeft hs)))

def subApplication : Raw := .app subLambda (.refl (.natural 2))

theorem sub_application_typed : HasType (fun _ => none) subApplication .i64 := by
  have proof : HasType (fun _ => none) (.refl (.natural 2)) subDomain :=
    .convert (.refl (.natural (by decide)))
      (.eq nested_subtract_computes.conversion.symm (.refl _))
  simpa only [subst, subApplication] using HasType.app sub_lambda_typed proof

theorem max_subtract_computes : Computation.Step maxSubtract (.natural maxWord) := by
  simpa only [maxSubtract, Nat.sub_zero] using max_subtract_typed.closed_sub_computes.1

theorem underflow_not_saturated :
    ¬ Conv (.usub (.natural 0) (.natural 1) p) (.natural 0) :=
  Conv.invalid_sub_not_literal (by decide)

theorem oversized_sub_not_folded :
    ¬ Conv (.usub (.natural wordBound) (.natural 1) p) (.natural (wordBound - 1)) :=
  Conv.invalid_sub_not_literal (by decide)

example : headNormal higherProof = false := by decide
example : ¬ HasType (fun _ => none) (.zeroLe t) (.lt (.natural 1) (.natural 0)) :=
  no_closed_false_bound (by decide)

theorem read_subtracted_computes :
    ∃ v, Computation.Steps readSubtracted v ∧ HasType (fun _ => none) v .i64 :=
  read_subtracted_typed.closed_index_computes nested_subtract_computes

def nestedRead : Raw := .index (.elements [readFirst, readSubtracted])
  (.natural 1) (.decide (.natural 1) (.natural 2))

theorem nested_read_typed : HasType (fun _ => none) nestedRead .i64 := by
  apply HasType.index (n := .natural 2)
  · apply HasType.elements _ (by decide)
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact read_first_typed
    · exact read_subtracted_typed
  · exact .natural (by decide)
  · exact .decide (by decide) (by decide) (by decide)

theorem nested_read_computes :
    ∃ v, Computation.Steps nestedRead v ∧ HasType (fun _ => none) v .i64 := by
  obtain ⟨v, hs, ht⟩ := read_subtracted_computes
  exact ⟨v, .next (.read _ 1 _ _ rfl) hs, ht⟩

def dynamicRead : Raw := .lam false .u64
  (.lam true (.lt (.var 0) (.natural 3))
    (.index (.elements values) (.var 1) (.var 0)))
def dynamicReadType : Raw := .pi false .u64
  (.pi true (.lt (.var 0) (.natural 3)) .i64)

theorem dynamic_read_typed : HasType (fun _ => none) dynamicRead dynamicReadType := by
  apply HasType.lam .u64 rfl
  apply HasType.lam (.lt (.var (by simp [Context.extend, rename])) (.natural (by decide))) rfl
  exact .index (array_typed _) (.var (by simp [Context.extend, rename]))
    (.var (by simp [Context.extend, rename]))

theorem dynamic_read_at {k : Nat} (selected : values[k]? = some v) :
    Computation.Steps (.app (.app dynamicRead (.natural k)) p) v := by
  have first : Computation.Step (.app dynamicRead (.natural k))
      (.lam true (.lt (.natural k) (.natural 3))
        (.index (.elements values) (.natural k) (.var 0))) := by
    simpa [dynamicRead, subst, single, liftSub, rename, values] using
      Computation.Step.beta false .u64
        (.lam true (.lt (.var 0) (.natural 3))
          (.index (.elements values) (.var 1) (.var 0))) (.natural k)
  have second : Computation.Step
      (.app (.lam true (.lt (.natural k) (.natural 3))
        (.index (.elements values) (.natural k) (.var 0))) p)
      (.index (.elements values) (.natural k) p) := by
    simpa [subst, single, values] using
      Computation.Step.beta true (.lt (.natural k) (.natural 3))
        (.index (.elements values) (.natural k) (.var 0)) p
  exact .next (.appFunction first) (.next second (.next (.read values k p v selected) .refl))

theorem read_under_lambda_preserved :
    HasType (fun _ => none) (.lam false .u64 (.integer 37)) (.pi false .u64 .i64) := by
  have ht : HasType (fun _ => none)
      (.lam false .u64 (.index (.elements values) (.natural 1)
        (.decide (.natural 1) (.natural 3)))) (.pi false .u64 .i64) :=
    .lam .u64 rfl (.index (array_typed _) (.natural (by decide))
      (.decide (by decide) (by decide) (by decide)))
  exact Computation.preservation ht (.lamBody (.read values 1 _ (.integer 37) rfl))

theorem empty_read_not_integer :
    ¬ Conv (.index (.elements []) (.natural k) p) (.integer z) :=
  Conv.invalid_read_not_integer (by simp)

theorem end_read_not_integer :
    ¬ Conv (.index (.elements values) (.natural 3) p) (.integer z) :=
  Conv.invalid_read_not_integer rfl

theorem literal_read_unique
    (h : Conv (.index (.elements values) (.natural 1) p) (.integer z)) : 37 = z :=
  Conv.read_integer_unique rfl h

def strictScalar : Raw := .app (.lam false .u64 (.integer 7))
  (.uadd (.natural 1) (.natural 2))

theorem strict_scalar_typed : HasType (fun _ => none) strictScalar .i64 := by
  simpa only [strictScalar, subst, proposition] using
    HasType.app (HasType.lam (Γ := fun _ => none) .u64 rfl
      (.integer (n := 7) (by decide) (by decide)))
      (HasType.uadd (.natural (n := 1) (by decide)) (.natural (n := 2) (by decide)))

theorem strict_scalar_computes : Evaluation.Steps strictScalar (.integer 7) := by
  have first : Evaluation.Step strictScalar (.app (.lam false .u64 (.integer 7)) (.natural 3)) :=
    .context (.appArgument .u64 (.integer 7)) (.add (by decide))
  have last : Evaluation.Step (.app (.lam false .u64 (.integer 7)) (.natural 3)) (.integer 7) := by
    simpa only [subst] using Evaluation.Step.betaRuntime (A := .u64) (body := .integer 7)
      (Evaluation.Value.natural 3)
  exact .next first (.next last .refl)

def overflowing : Raw := .uadd (.natural maxWord) (.natural 1)

theorem overflowing_typed (Γ : Context) : HasType Γ overflowing .u64 :=
  .uadd (.natural (by decide)) (.natural (by decide))

theorem overflowing_traps : Evaluation.Trap overflowing := .overflow (by decide)

def discardTrap : Raw := .app (.lam false .u64 (.integer 7)) overflowing

theorem discard_trap_typed : HasType (fun _ => none) discardTrap .i64 := by
  simpa only [discardTrap, subst, proposition] using
    HasType.app (HasType.lam (Γ := fun _ => none) .u64 rfl
      (.integer (n := 7) (by decide) (by decide))) (overflowing_typed _)

theorem discard_argument_traps : Evaluation.Trap discardTrap :=
  .context (.appArgument .u64 (.integer 7)) overflowing_traps

def erasedOverflowDomain : Raw := .lt (.natural 0) (.uadd overflowing (.natural 1))
def erasedOverflow : Raw := .app (.lam true erasedOverflowDomain (.integer 7)) (.zeroLe overflowing)

theorem erased_overflow_typed : HasType (fun _ => none) erasedOverflow .i64 := by
  have hD : IsType (fun _ => none) erasedOverflowDomain :=
    .lt (.natural (by decide)) (.uadd (overflowing_typed _) (.natural (by decide)))
  simpa only [erasedOverflow, erasedOverflowDomain, subst, proposition] using
    HasType.app (HasType.lam hD rfl (.integer (n := 7) (by decide) (by decide)))
      (HasType.zeroLe (overflowing_typed _))

theorem erased_overflow_computes : Evaluation.Step erasedOverflow (.integer 7) := by
  simpa only [erasedOverflow, subst] using
    (Evaluation.Step.betaErased (A := erasedOverflowDomain) (body := .integer 7)
      (a := .zeroLe overflowing))

def arrayTrap : Raw := .index (.elements [.integer 7, discardTrap])
  (.natural 0) (.decide (.natural 0) (.natural 2))

theorem array_trap_typed : HasType (fun _ => none) arrayTrap .i64 := by
  apply HasType.index (n := .natural 2)
  · apply HasType.elements _ (by decide)
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact .integer (by decide) (by decide)
    · exact discard_trap_typed
  · exact .natural (by decide)
  · exact .decide (by decide) (by decide) (by decide)

theorem unselected_element_traps : Evaluation.Trap arrayTrap :=
  .context (.indexArray (.natural 0) (.decide (.natural 0) (.natural 2)))
    (.context (.elements [.integer 7] [] (by intro x hx; simp only [List.mem_singleton] at hx; subst x; exact .integer 7)) discard_argument_traps)

/-- The abstract relation can skip work that strict execution must retain. -/
theorem abstract_read_skips_trap : Computation.Step arrayTrap (.integer 7) :=
  .read _ 0 _ _ rfl

theorem strict_closed_execution_safe (hs : Evaluation.Steps erasedOverflow u) :
    HasType (fun _ => none) u .i64 ∧ Evaluation.Outcome u :=
  Evaluation.execution_safety erased_overflow_typed hs

def simpleEvidence : Raw := .app
  (.lam true (.lt (.natural 0) (.uadd (.natural 0) (.natural 1))) (.integer 7))
  (.zeroLe (.natural 0))

theorem simple_evidence_typed : HasType (fun _ => none) simpleEvidence .i64 := by
  have hD : IsType (fun _ => none) (.lt (.natural 0) (.uadd (.natural 0) (.natural 1))) :=
    .lt (.natural (by decide)) (.uadd (.natural (by decide)) (.natural (by decide)))
  simpa only [simpleEvidence, subst, proposition] using
    HasType.app (HasType.lam hD rfl (.integer (n := 7) (by decide) (by decide)))
      (HasType.zeroLe (HasType.natural (n := 0) (by decide)))

theorem evidence_payloads_agree :
    PayloadErasure.erase erasedOverflow = PayloadErasure.erase simpleEvidence := by
  simp [PayloadErasure.erase, erasedOverflow, simpleEvidence]

theorem erased_scalar_computes :
    Evaluation.Steps (PayloadErasure.erase strictScalar) (.integer 7) := by
  simpa only [PayloadErasure.erase] using PayloadErasure.steps_erasure strict_scalar_computes

theorem erased_evidence_computes :
    Evaluation.Step (PayloadErasure.erase erasedOverflow) (.integer 7) := by
  simpa only [PayloadErasure.erase] using PayloadErasure.step_erasure erased_overflow_computes

theorem erased_argument_still_traps : Evaluation.Trap (PayloadErasure.erase discardTrap) :=
  PayloadErasure.trap_erasure discard_argument_traps

theorem erased_array_still_traps : Evaluation.Trap (PayloadErasure.erase arrayTrap) :=
  PayloadErasure.trap_erasure unselected_element_traps

theorem mixed_binder_erased_substitution (a : Raw) :
    PayloadErasure.erase ((Raw.lam true (.lt (.var 0) (.natural 3))
      (.index (.elements values) (.var 1) (.var 0))).subst (single a)) =
    (PayloadErasure.erase (.lam true (.lt (.var 0) (.natural 3))
      (.index (.elements values) (.var 1) (.var 0)))).subst (single (PayloadErasure.erase a)) :=
  PayloadErasure.erase_instantiate _ a

/-- Each serialized fixture carries a checked closed typing derivation. The
renderer/parser/compiler association is tested rather than formally assumed. -/
structure Fixture where
  name : String
  runtime : Bool
  type : Raw
  value : Raw
  typed : HasType (fun _ => none) value type

def fixtures : List Fixture := [
  ⟨"primitive_first", true, .i64, readFirst, read_first_typed⟩,
  ⟨"primitive_last", true, .i64, readLast, read_last_typed⟩,
  ⟨"primitive_computed", true, .i64, readComputed, read_computed_typed⟩,
  ⟨"primitive_subtract", true, .u64, subtract, subtract_typed⟩,
  ⟨"primitive_max_subtract", true, .u64, maxSubtract, max_subtract_typed⟩,
  ⟨"primitive_nested_subtract", true, .u64, nestedSubtract, nested_subtract_typed⟩,
  ⟨"primitive_subtracted_index", true, .i64, readSubtracted, read_subtracted_typed⟩,
  ⟨"primitive_sub_annotation", true, .i64, subApplication, sub_application_typed⟩,
  ⟨"primitive_nested_read", true, .i64, nestedRead, nested_read_typed⟩,
  ⟨"primitive_dynamic_read", false, dynamicReadType, dynamicRead, dynamic_read_typed⟩,
  ⟨"primitive_strict_scalar", true, .i64, strictScalar, strict_scalar_typed⟩,
  ⟨"primitive_erased_overflow", true, .i64, erasedOverflow, erased_overflow_typed⟩,
  ⟨"primitive_discard_trap", false, .i64, discardTrap, discard_trap_typed⟩,
  ⟨"primitive_array_trap", false, .i64, arrayTrap, array_trap_typed⟩,
  ⟨"primitive_simple_evidence", true, .i64, simpleEvidence, simple_evidence_typed⟩,
  ⟨"primitive_max_proof", false, .lt (.natural 0) (.uadd (.natural maxWord) (.natural 1)),
    maxProof, max_proof_typed _⟩]

def program : Option String := do
  let lines ← fixtures.mapM fun f => do
    let A ← f.type.render 1024 []
    let t ← f.value.render 1024 []
    pure ("(" ++ (if f.runtime then "export" else "def") ++ " " ++ f.name ++ " " ++ A ++ " " ++ t ++ ")")
  pure ("; Generated from closed Lean typing derivations by EmitPrimitiveSafety.lean.\n" ++
    String.intercalate "\n" lines ++ "\n")
end Jihoo.CoreBridge.Raw.Beta.PrimitiveExamples
