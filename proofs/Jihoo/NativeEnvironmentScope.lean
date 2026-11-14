import Jihoo.NativeEnvironmentMetatheory
import Jihoo.NativeEnvironmentCheckerSoundness

/-! Actual-term scoping for every unified native rule, including dependent
constructor fields and explicit memory continuations. -/
namespace Jihoo.NativeKernel.Environment

private theorem scoped_node {depth : Nat} {op : Op} {args : List Term}
    (h0 : ∀ i, op.binders i = 0) (hs : ∀ t ∈ args, t.Scoped depth) :
    (Term.node op args).Scoped depth := by
  apply Term.Scoped.node
  intro i t ht
  rw [h0 i, Nat.add_zero]
  exact hs t (List.mem_of_getElem? ht)

private theorem scoped_binder {depth : Nat} {op : Op} {A B : Term}
    (h0 : op.binders 0 = 0) (h1 : op.binders 1 = 1)
    (hA : A.Scoped depth) (hB : B.Scoped (depth + 1)) :
    (Term.node op [A, B]).Scoped depth := by
  apply Term.Scoped.node
  intro i t ht
  cases i with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
      subst t
      simpa only [h0, Nat.add_zero] using hA
  | succ i =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at ht
          subst t
          simpa only [h1] using hB
      | succ i => simp at ht


private theorem scoped_branch {depth : Nat} {op : Op} {a b yes no : Term}
    (h0 : op.binders 0 = 0) (h1 : op.binders 1 = 0)
    (h2 : op.binders 2 = 1) (h3 : op.binders 3 = 0)
    (ha : a.Scoped depth) (hb : b.Scoped depth)
    (hy : yes.Scoped (depth+1)) (hn : no.Scoped depth) :
    (Term.node op [a,b,yes,no]).Scoped depth := by
  apply Term.Scoped.node
  intro i t ht
  cases i with
  | zero => simpa [h0] using (Option.some.inj ht ▸ ha)
  | succ i =>
      cases i with
      | zero => simpa [h1] using (Option.some.inj ht ▸ hb)
      | succ i =>
          cases i with
          | zero => simpa [h2] using (Option.some.inj ht ▸ hy)
          | succ i =>
              cases i with
              | zero => simpa [h3] using (Option.some.inj ht ▸ hn)
              | succ i => simp at ht

private theorem dataCase_scoped (analysis : Bool) (family depth : Nat)
    (motive scrutinee : Term) (cases : List Term)
    (hm : motive.Scoped depth) (hs : scrutinee.Scoped depth)
    (hc : ∀ branch ∈ cases, branch.Scoped depth) :
    (Term.node (if analysis then .caseOf family cases.length else .elim family cases.length)
      (motive :: (cases ++ [scrutinee]))).Scoped depth := by
  cases analysis <;> apply scoped_node (by intro i; rfl)
  all_goals intro a member
  all_goals rcases List.mem_cons.mp member with rfl | member
  all_goals first | exact hm | skip
  all_goals rcases List.mem_append.mp member with member | member
  all_goals first | exact hc _ member | (obtain rfl := List.mem_singleton.mp member; exact hs)

theorem HasType.term_scoped (h : HasType env ctx mode t T) : t.Scoped ctx.length := by
  apply HasType.rec (t := h)
    (motive_1 := fun ctx _ A _ _ => A.Scoped ctx.length)
    (motive_2 := fun ctx _ t _ _ => t.Scoped ctx.length)
    (motive_3 := fun ctx _ _ _ xs _ _ => ∀ x ∈ xs, x.Scoped ctx.length)
    (motive_4 := fun ctx _ _ xs _ => ∀ x ∈ xs, x.Scoped ctx.length)
    (motive_5 := fun ctx _ _ xs _ => ∀ x ∈ xs, x.Scoped ctx.length)
  all_goals intros
  all_goals try (apply dataCase_scoped <;> assumption)
  all_goals first
    | assumption
    | solve | apply Term.Scoped.var; exact lookup_bound (by assumption)
    | solve | apply scoped_binder rfl rfl <;> assumption
    | solve | apply scoped_branch rfl rfl rfl rfl <;> assumption
    | solve
      | apply scoped_node (by intro i; simp [Op.binders])
        simp_all (failIfUnchanged := false) [List.mem_append, List.mem_cons, forall_eq_or_imp]
    | solve
      | rename_i x member
        rcases List.mem_cons.mp member with rfl | member <;> solve_by_elim
    | solve
      | apply scoped_node (by intro i; simp [Op.binders])
        intro x member
        rcases List.mem_cons.mp member with rfl | member
        · assumption
        · rcases List.mem_append.mp member with member | member
          · solve_by_elim
          · rcases List.mem_singleton.mp member with rfl
            assumption
    | solve
      | apply scoped_node (by intro i; simp [Op.binders])
        simp only [List.mem_singleton, forall_eq]
        apply scoped_node (by intro i; simp [Op.binders])
        simp_all
    | solve | simp_all (failIfUnchanged := false)

namespace Checker

theorem infer_scoped (h : infer fuel env ctx ghost t = some T) : t.Scoped ctx.length :=
  (infer_sound h).term_scoped

theorem check_scoped (h : check fuel env ctx ghost t T = true) : t.Scoped ctx.length :=
  (check_sound h).term_scoped

theorem infer_wellFormed (h : infer fuel env ctx ghost t = some T) : t.WellFormed :=
  (infer_sound h).term_wellFormed

theorem check_wellFormed (h : check fuel env ctx ghost t T = true) : t.WellFormed :=
  (check_sound h).term_wellFormed

end Checker
end Jihoo.NativeKernel.Environment
