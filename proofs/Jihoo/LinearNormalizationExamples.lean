import Jihoo.CheckedLinearNormalization

namespace Jihoo.CoreBridge.LinearNaturals.Examples

private def x : Expr 2 := .var ⟨0, by decide⟩
private def y : Expr 2 := .var ⟨1, by decide⟩
private def one : Expr 2 := .lit ⟨1, by decide⟩

theorem symbolic_commutativity (ρ : Nat → Nat) :
    (Expr.add x y).eval ρ = (Expr.add y x).eval ρ :=
  Expr.equal_normal_values _ _ (by decide) ρ

theorem association_and_multiplicity (ρ : Nat → Nat) :
    (Expr.add (.add x one) (.add y x)).eval ρ =
      (Expr.add (.add x x) (.add one y)).eval ρ :=
  Expr.equal_normal_values _ _ (by decide) ρ

theorem wrong_coefficient_rejected :
    (equivalent 1 (.var 0) (.uadd (.var 0) (.var 0))).isSome = false := by decide

theorem out_of_scope_rejected : (extract 1 (.var 1)).isSome = false := by decide

theorem subtraction_rejected :
    (extract 0 (.usub (.natural 3) (.natural 1) (.decide (.natural 1) (.natural 4)))).isSome = false := by
  decide

/-- Ghost arithmetic can exceed a word, even though each literal is a word.
No zero/wrapping interpretation is admitted. -/
theorem wide_sum_value (ρ : Nat → Nat) :
    (Expr.add (.lit ⟨wordBound - 1, by decide⟩) (.lit ⟨1, by decide⟩) : Expr 0).eval ρ = wordBound := by
  simp [Expr.eval, wordBound]

theorem wide_sum_not_zero :
    (equivalent 0 (.uadd (.natural (wordBound - 1)) (.natural 1)) (.natural 0)).isSome = false := by
  decide

/-- A self-looping/untypable beta term cannot enter this arithmetic profile. -/
theorem application_rejected :
    (extract 0 (.app (.lam false .u64 (.var 0)) (.natural 7))).isSome = false := by decide

end Jihoo.CoreBridge.LinearNaturals.Examples
