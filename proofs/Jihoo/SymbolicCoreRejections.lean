import Jihoo.SymbolicCoreExamples

/-! Adversarial static regressions: unreachable arms still require typing,
proofs retain their exact symbolic endpoints, and moved names stay revoked. -/
namespace Jihoo.SymbolicCoreRejections
open ScopedLend SymbolicCoreContext SymbolicCoreTyping
open DependentBufferIndices (Expr)

private theorem readLend_not_var
    (h : SizedCoreExecution.ReadLend g root owner refTy index proof ownerTy body) :
    Graph.nodeAt g root ≠ .var k := by
  cases h <;> simp_all

private theorem ownedReadLend_not_var
    (h : SizedCoreExecution.OwnedReadLend g root owner refTy length index proof resultTy ownerTy body) :
    Graph.nodeAt g root ≠ .var k := by
  cases h <;> simp_all

/-- A dead lexical name cannot acquire either scalar or owner authority. -/
theorem dead_var_rejected (shape : Graph.nodeAt g root = .var k)
    (dead : ctx[k]? = some .dead) : ¬ Typing g ctx sizes root kind := by
  intro typed
  cases typed <;> try simp_all
  case lend => exact readLend_not_var ‹_› shape
  case ownedLend => exact ownedReadLend_not_var ‹_› shape

/-- Both old aliases are rejected after transferring the selected capability. -/
theorem transferred_aliases_rejected
    (first : Graph.nodeAt g firstRoot = .var 1)
    (second : Graph.nodeAt g secondRoot = .var 3) :
    ¬ Typing g (transferred [.owner 0, .nat, .owner 0, .owner 1] 0)
        sizes firstRoot kind ∧
    ¬ Typing g (transferred [.owner 0, .nat, .owner 0, .owner 1] 0)
        sizes secondRoot kind :=
  ⟨dead_var_rejected first rfl, dead_var_rejected second rfl⟩

theorem consumed_aliases_rejected
    (first : Graph.nodeAt g firstRoot = .var 0)
    (second : Graph.nodeAt g secondRoot = .var 2) :
    ¬ Typing g (consumed 0 [.owner 0, .nat, .owner 0, .owner 1])
        sizes firstRoot kind ∧
    ¬ Typing g (consumed 0 [.owner 0, .nat, .owner 0, .owner 1])
        sizes secondRoot kind :=
  ⟨dead_var_rejected first rfl, dead_var_rejected second rfl⟩

/-- Even if two expressions might close to the same number in one instance,
a proof for one symbolic length does not certify a different symbolic length. -/
theorem wrong_length_evidence_rejected
    (shape : Graph.nodeAt g root = .var 0) (different : n ≠ m) :
    ¬ Evidence g [.bound i n] root i m := by
  intro typed
  cases typed <;> try simp_all

theorem wrong_index_evidence_rejected
    (shape : Graph.nodeAt g root = .var 0) (different : i ≠ j) :
    ¬ Evidence g [.bound i n] root j n := by
  intro typed
  cases typed <;> try simp_all

/-- The false arm is unreachable (0 < 1), but its dead variable is rejected. -/
def badBranch : Graph.Graph := #[.natural 0, .natural 1, .integer 7,
  .var 0, .ifLt 0 1 2 3]

theorem bad_unselected_branch_rejected :
    ¬ Typing badBranch [.dead] [] 4 kind := by
  intro typed
  have shape : Graph.nodeAt badBranch 4 = .ifLt 0 1 2 3 := rfl
  cases typed <;> try simp_all
  case branch no => exact dead_var_rejected (by rfl) (by rfl) no

/-- Substitution traverses an inner binder: the substituted outer variable is
lifted, while the inner bound variable remains 0 and old free variables lower. -/
theorem nested_substitution_capture_avoiding :
    (Expr.letE (.var 0) (.letE (.var 1) (.letE (.var 0) (.var 5)))).subst
      (Expr.single (.var 2)) =
    .letE (.var 2) (.letE (.var 3) (.letE (.var 0) (.var 4))) := rfl

theorem nested_result_substitution_capture_avoiding :
    (Result.owner (.letE (.var 0) (.var 1))).subst (Expr.single (.var 2)) =
      .owner (.letE (.var 2) (.var 3)) := rfl

end Jihoo.SymbolicCoreRejections
