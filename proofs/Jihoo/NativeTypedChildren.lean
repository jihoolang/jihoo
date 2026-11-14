import Jihoo.NativeEnvironmentContextualPreservation

/-! Typed child recovery for the native binding profile. The only excluded
edges are the four explicit source binder edges; they are handled separately
by context-indexed representation and projection judgments. -/
namespace Jihoo.NativeKernel.Environment

private theorem childWitness (typed : HasType env ctx mode child type) :
    ∃ childType, HasType env ctx true child childType := ⟨type, typed.ghost⟩

 theorem HasType.childrenTyped (typed : HasType env ctx mode term type) :
    ∀ op children, term = .node op children → (∀ index, op.binders index = 0) →
      ∀ child ∈ children, ∃ childType, HasType env ctx true child childType := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun ctx _ term _ _ =>
      ∀ op children, term = .node op children → (∀ index, op.binders index = 0) →
        ∀ child ∈ children, ∃ childType, HasType env ctx true child childType)
    (motive_3 := fun ctx _ _ _ arguments _ _ =>
      ∀ child ∈ arguments, ∃ childType, HasType env ctx true child childType)
    (motive_4 := fun ctx _ _ branches _ =>
      ∀ child ∈ branches, ∃ childType, HasType env ctx true child childType)
    (motive_5 := fun ctx _ _ branches _ =>
      ∀ child ∈ branches, ∃ childType, HasType env ctx true child childType)
  all_goals intros
  all_goals first | trivial | skip
  case convert =>
    rename_i original converted ih op children equality binders child member
    exact ih op children equality binders child member
  case pi =>
    rename_i binding body _ _ op children equality binders child member
    cases equality
    have impossible := binders 1
    contradiction
  case lam =>
    rename_i binding body _ _ op children equality binders child member
    cases equality
    have impossible := binders 1
    contradiction
  case ifLt =>
    rename_i first second yes no _ _ _ _ op children equality binders child member
    cases equality
    have impossible := binders 2
    contradiction
  case ifEq =>
    rename_i first second yes no _ _ _ _ op children equality binders child member
    cases equality
    have impossible := binders 2
    contradiction
  case cons =>
    rename_i converted head rest ihhead ihrest child member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,head.ghost⟩
    · exact ihrest child member
  case cons =>
    rename_i head rest ihhead ihrest child member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,head.ghost⟩
    · exact ihrest child member
  case cons =>
    rename_i head rest ihhead ihrest child member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,head.ghost⟩
    · exact ihrest child member
  all_goals rename_i op children equality binders child member
  all_goals cases equality
  all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at member
  all_goals repeat' (have disjunction : Or _ _ := member; clear member; rcases disjunction with member | member)
  all_goals try subst child
  all_goals first
    | solve | apply childWitness; assumption
    | solve | apply childWitness (mode := true); apply HasType.natural; assumption
    | solve | apply childWitness (mode := true); apply HasType.buffer; assumption
    | solve | apply_assumption; assumption
    | solve | apply childWitness; apply_assumption; assumption
    | skip
  case propElim.refl.inr.inl =>
    rename_i _ branchesIH _
    exact branchesIH child member
  case dataElim.refl.inr.inl =>
    rename_i _ _ branchesIH
    exact branchesIH child member
  case view.refl.inr.inl =>
    rename_i _ _ branchesIH
    exact branchesIH child member

end Jihoo.NativeKernel.Environment
