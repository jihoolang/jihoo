import Jihoo.CorePrimitiveSafety
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

example : headNormal higherProof = false := by decide
example : ¬ HasType (fun _ => none) (.zeroLe t) (.lt (.natural 1) (.natural 0)) :=
  no_closed_false_bound (by decide)

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
