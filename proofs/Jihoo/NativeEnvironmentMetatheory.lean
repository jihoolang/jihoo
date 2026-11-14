import Jihoo.NativeEnvironmentTyping
import Jihoo.NativeModeSafety

/-! Structural metatheory for the unified native judgment. These facts follow
from the same environment-indexed rules used by executable soundness. -/
namespace Jihoo.NativeKernel.Environment

private theorem dataCase_wellFormed (analysis : Bool) (family : Nat)
    (motive scrutinee : Term) (cases : List Term)
    (hm : motive.WellFormed) (hs : scrutinee.WellFormed)
    (hc : ∀ branch ∈ cases, branch.WellFormed) :
    (Term.node (if analysis then .caseOf family cases.length else .elim family cases.length)
      (motive :: (cases ++ [scrutinee]))).WellFormed := by
  cases analysis <;> simp_all [Term.WellFormed, Op.arity, List.mem_append]
  all_goals intro a member
  all_goals rcases member with member | rfl
  all_goals first | exact hc _ member | exact hs

theorem HasType.term_wellFormed (h : HasType env ctx mode t T) : t.WellFormed := by
  apply HasType.rec (t := h)
    (motive_1 := fun _ _ A _ _ => A.WellFormed)
    (motive_2 := fun _ _ t _ _ => t.WellFormed)
    (motive_3 := fun _ _ _ _ xs _ _ => ∀ x ∈ xs, x.WellFormed)
    (motive_4 := fun _ _ _ xs _ => ∀ x ∈ xs, x.WellFormed)
    (motive_5 := fun _ _ _ xs _ => ∀ x ∈ xs, x.WellFormed)
  all_goals intros
  all_goals try (apply dataCase_wellFormed <;> assumption)
  all_goals simp_all [Term.WellFormed, Op.arity, List.mem_append]
  all_goals first
    | assumption
    | solve | intros x member; rcases member with h | h <;> simp_all
    | solve | rename_i member; rcases member with h | h <;> simp_all

end Jihoo.NativeKernel.Environment
