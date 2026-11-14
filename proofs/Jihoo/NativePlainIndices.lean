import Jihoo.NativeRepresentationIndices

/-! Plain representation modulo typed U64 indices. A hole records an actual
U64 derivation and may contain memory/type syntax. Lambda annotations do not
contribute representation, matching Core.plain. Binding-sensitive branches
retain their exact source proof contexts. -/
namespace Jihoo.NativeKernel.Environment.Representation
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

def plainNode (env : Environment) : Op → Bool
  | .global _ | .buffer | .ref | .pi _ | .back _ | .lam _ | .ifLt | .ifEq => false
  | .ind family _ => (env.families[family]?).any fun entry => !entry.boxed
  | _ => true

theorem plainNode_noBinders (h : plainNode env op = true) : ∀ index, op.binders index = 0 := by
  cases op <;> simp only [plainNode] at h <;> try contradiction
  all_goals intro index; rfl

inductive PlainIndices (env : Environment) : Context → Term → Prop where
  | var : PlainIndices env ctx (.var index)
  | index : HasType env ctx true term .u64 → PlainIndices env ctx term
  | node : plainNode env op = true →
      (∀ child ∈ children, PlainIndices env ctx child) → PlainIndices env ctx (.node op children)
  | lam : PlainIndices env (⟨domain, erased⟩ :: ctx) body →
      PlainIndices env ctx (.lam erased domain body)
  | ifLt : PlainIndices env ctx left → PlainIndices env ctx right →
      PlainIndices env (⟨.lt left right, true⟩ :: ctx) yes → PlainIndices env ctx no →
      PlainIndices env ctx (.ifLt left right yes no)
  | ifEq : PlainIndices env ctx left → PlainIndices env ctx right →
      PlainIndices env (⟨.eq left right, true⟩ :: ctx) yes → PlainIndices env ctx no →
      PlainIndices env ctx (.ifEq left right yes no)

private theorem renameArgs_noBinders (h : ∀ index, op.binders index = 0)
    (arguments : List Term) (offset : Nat) (ρ : Nat → Nat) :
    renameArgs op ρ offset arguments = arguments.map (Term.rename ρ) := by
  induction arguments generalizing offset with
  | nil => simp only [renameArgs, List.map_nil]
  | cons first rest ih => simp only [renameArgs, h, liftRenaming, List.map_cons, ih]

private theorem substArgs_noBinders (h : ∀ index, op.binders index = 0)
    (arguments : List Term) (offset : Nat) (σ : Nat → Term) :
    substArgs op σ offset arguments = arguments.map (Term.subst σ) := by
  induction arguments generalizing offset with
  | nil => simp only [substArgs, List.map_nil]
  | cons first rest ih => simp only [substArgs, h, liftSub, List.map_cons, ih]

private theorem globalFreeArgs_all (arguments : List Term) (free : globalFreeArgs arguments = true) :
    ∀ child ∈ arguments, globalFree child = true := by
  induction arguments with
  | nil => intro child member; cases member
  | cons first rest ih =>
      simp only [globalFreeArgs] at free
      have checked := Bool.and_eq_true_iff.mp free
      intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact checked.1
      · exact ih checked.2 _ member

private theorem globalFree_children (free : globalFree (.node op arguments) = true) :
    ∀ child ∈ arguments, globalFree child = true := by
  cases op <;> simp only [globalFree] at free <;> try contradiction
  all_goals exact globalFreeArgs_all _ free

/-- All actually checked plain arguments enter the logical relation. Unknown
indices are not inspected here; the typed-hole constructor handles them later. -/
theorem PlainIndices.of_familyPlain (formed : term.WellFormed)
    (plain : familyPlain env term = true) (free : globalFree term = true) : PlainIndices env ctx term := by
  induction term using Term.rec
    (motive_2 := fun children => ∀ child ∈ children, ∀ ctx,
      child.WellFormed → familyPlain env child = true → globalFree child = true → PlainIndices env ctx child) generalizing ctx with
  | var => exact .var
  | node op arguments ih =>
      simp only [Term.WellFormed] at formed
      have childrenFree := globalFree_children free
      cases op with
      | global => simp [globalFree] at free
      | lam erased =>
          cases arguments with
          | nil => simp [familyPlain] at plain
          | cons domain rest => cases rest with
            | nil => simp [familyPlain] at plain
            | cons body rest => cases rest with
              | cons => simp [familyPlain] at plain
              | nil => exact .lam (ih body (by simp) _ (formed.2 _ (by simp)) (by simpa only [familyPlain] using plain) (childrenFree _ (by simp)))
      | ifLt =>
          simp only [familyPlain] at plain
          rcases arguments with _ | ⟨left, _ | ⟨right, _ | ⟨yes, _ | ⟨no, rest⟩⟩⟩⟩
          all_goals try (have bad := formed.1; simp [Op.arity] at bad)
          cases rest with
          | cons => have bad := formed.1; simp [Op.arity] at bad
          | nil =>
              have children := (familyPlainArgs_all _).mp plain
              exact .ifLt (ih left (by simp) _ (formed.2 _ (by simp)) (children _ (by simp)) (childrenFree _ (by simp)))
                (ih right (by simp) _ (formed.2 _ (by simp)) (children _ (by simp)) (childrenFree _ (by simp)))
                (ih yes (by simp) _ (formed.2 _ (by simp)) (children _ (by simp)) (childrenFree _ (by simp)))
                (ih no (by simp) _ (formed.2 _ (by simp)) (children _ (by simp)) (childrenFree _ (by simp)))
      | ifEq =>
          simp only [familyPlain] at plain
          rcases arguments with _ | ⟨left, _ | ⟨right, _ | ⟨yes, _ | ⟨no, rest⟩⟩⟩⟩
          all_goals try (have bad := formed.1; simp [Op.arity] at bad)
          cases rest with
          | cons => have bad := formed.1; simp [Op.arity] at bad
          | nil =>
              have children := (familyPlainArgs_all _).mp plain
              exact .ifEq (ih left (by simp) _ (formed.2 _ (by simp)) (children _ (by simp)) (childrenFree _ (by simp)))
                (ih right (by simp) _ (formed.2 _ (by simp)) (children _ (by simp)) (childrenFree _ (by simp)))
                (ih yes (by simp) _ (formed.2 _ (by simp)) (children _ (by simp)) (childrenFree _ (by simp)))
                (ih no (by simp) _ (formed.2 _ (by simp)) (children _ (by simp)) (childrenFree _ (by simp)))
      | ind family count =>
          simp only [familyPlain] at plain
          obtain ⟨head,args⟩ := Bool.and_eq_true_iff.mp plain
          exact .node head (fun child member => ih child member _ (formed.2 _ member)
            ((familyPlainArgs_all _).mp args _ member) (childrenFree _ member))
      | buffer | ref | pi _ | back _ => simp [familyPlain] at plain
      | _ =>
          simp only [familyPlain] at plain
          apply PlainIndices.node rfl
          intro child member
          exact ih child member _ (formed.2 _ member) ((familyPlainArgs_all _).mp plain _ member) (childrenFree _ member)
  | nil => rename_i child member _ _ _ _; cases member
  | cons first rest ihfirst ihrest =>
      rename_i child member ctx formed plain free
      rcases List.mem_cons.mp member with rfl | member
      · exact ihfirst formed plain free
      · exact ihrest _ member ctx formed plain free

theorem PlainIndices.rename (wf : UnifiedProgram.EnvWellFormed env)
    (plain : PlainIndices env ctx term) (renamed : Ghost.Renaming ctx target ρ) :
    PlainIndices env target (term.rename ρ) := by
  induction plain generalizing target ρ with
  | var => simpa only [Term.rename] using (PlainIndices.var (env := env) (ctx := target) (index := ρ _))
  | index typed =>
      exact .index (by simpa [Term.rename, renameArgs] using typed.ghostRenaming wf renamed)
  | node head children ih =>
      simp only [Term.rename, renameArgs_noBinders (plainNode_noBinders head)]
      apply PlainIndices.node head
      intro child member
      obtain ⟨original, found, rfl⟩ := List.mem_map.mp member
      exact ih original found renamed
  | lam body ih =>
      simpa only [Term.rename, renameArgs, Op.binders, liftRenaming] using
        PlainIndices.lam (ih (renamed.lift _ _))
  | @ifLt ctx left right yes no first second yesPlain noPlain ihfirst ihsecond ihyes ihno =>
      have yes' := ihyes (renamed.lift (Term.lt left right) true)
      simp only [Term.rename, renameArgs, Op.binders, liftRenaming] at yes'
      simpa only [Term.rename, renameArgs, Op.binders, liftRenaming] using
        PlainIndices.ifLt (ihfirst renamed) (ihsecond renamed) yes' (ihno renamed)
  | @ifEq ctx left right yes no first second yesPlain noPlain ihfirst ihsecond ihyes ihno =>
      have yes' := ihyes (renamed.lift (Term.eq left right) true)
      simp only [Term.rename, renameArgs, Op.binders, liftRenaming] at yes'
      simpa only [Term.rename, renameArgs, Op.binders, liftRenaming] using
        PlainIndices.ifEq (ihfirst renamed) (ihsecond renamed) yes' (ihno renamed)

theorem PlainIndices.weaken (wf : UnifiedProgram.EnvWellFormed env)
    (plain : PlainIndices env ctx term) (domain : Term) (erased : Bool) :
    PlainIndices env (⟨domain, erased⟩ :: ctx) (term.rename Nat.succ) :=
  plain.rename wf (Jihoo.NativeKernel.Ghost.Renaming.shift _ _ _)

theorem PlainIndices.substitution (wf : UnifiedProgram.EnvWellFormed env)
    (plain : PlainIndices env ctx term) (typed : Ghost.Substitution env ctx target σ)
    (values : ∀ index, PlainIndices env target (σ index)) :
    PlainIndices env target (term.subst σ) := by
  induction plain generalizing target σ with
  | var => simpa only [Term.subst] using values _
  | index formed =>
      exact .index (by simpa [Term.subst, substArgs] using formed.ghostSubstitution wf typed)
  | node head children ih =>
      simp only [Term.subst, substArgs_noBinders (plainNode_noBinders head)]
      apply PlainIndices.node head
      intro child member
      obtain ⟨original, found, rfl⟩ := List.mem_map.mp member
      exact ih original found typed values
  | @lam domain erased ctx body bodyPlain ih =>
      have liftedValues : ∀ index, PlainIndices env (⟨domain.subst σ,erased⟩ :: target) (liftSubOne σ index) := by
        intro index
        cases index with
        | zero => exact .var
        | succ index => exact (values index).weaken wf _ _
      simpa only [Term.subst, substArgs, Op.binders, liftSub] using
        PlainIndices.lam (ih (typed.lift wf _ _) liftedValues)
  | @ifLt ctx left right yes no first second yesPlain noPlain ihfirst ihsecond ihyes ihno =>
      have liftedValues : ∀ index, PlainIndices env
          (⟨(Term.lt left right).subst σ,true⟩ :: target) (liftSubOne σ index) := by
        intro index
        cases index with
        | zero => exact .var
        | succ index => exact (values index).weaken wf _ _
      have yes' := ihyes (typed.lift wf (Term.lt left right) true) liftedValues
      simp only [Term.subst, substArgs, Op.binders, liftSub] at yes'
      simpa only [Term.subst, substArgs, Op.binders, liftSub] using
        PlainIndices.ifLt (ihfirst typed values) (ihsecond typed values) yes' (ihno typed values)
  | @ifEq ctx left right yes no first second yesPlain noPlain ihfirst ihsecond ihyes ihno =>
      have liftedValues : ∀ index, PlainIndices env
          (⟨(Term.eq left right).subst σ,true⟩ :: target) (liftSubOne σ index) := by
        intro index
        cases index with
        | zero => exact .var
        | succ index => exact (values index).weaken wf _ _
      have yes' := ihyes (typed.lift wf (Term.eq left right) true) liftedValues
      simp only [Term.subst, substArgs, Op.binders, liftSub] at yes'
      simpa only [Term.subst, substArgs, Op.binders, liftSub] using
        PlainIndices.ifEq (ihfirst typed values) (ihsecond typed values) yes' (ihno typed values)

theorem PlainIndices.context (wf : UnifiedProgram.EnvWellFormed env)
    (plain : PlainIndices env ctx term) (related : Ghost.ContextConversion env ctx target) :
    PlainIndices env target term := by
  simpa only [Term.subst_id] using plain.substitution wf related.substitution (fun _ => .var)

theorem PlainIndices.u64_application {index : Term} (function : PlainIndices env ctx f)
    (argument : HasType env ctx true index .u64) : PlainIndices env ctx (.app f index) := by
  apply PlainIndices.node rfl
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact function
  · exact .index argument

theorem PlainIndices.no_buffer (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (plain : PlainIndices env ctx (.buffer n)) : False := by
  cases plain with
  | index typed => exact u64_not_buffer history typed (.refl _)
  | node head _ => simp [plainNode] at head

theorem PlainIndices.no_ref (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (plain : PlainIndices env ctx (.ref owner)) : False := by
  cases plain with
  | index typed => exact u64_not_ref history typed (.refl _)
  | node head _ => simp [plainNode] at head

theorem PlainIndices.no_back (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (plain : PlainIndices env ctx (.back erased owner motive)) : False := by
  cases plain with
  | index typed => exact u64_not_back history typed (.refl _)
  | node head _ => simp [plainNode] at head

theorem PlainIndices.no_pi (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (plain : PlainIndices env ctx (.pi erased domain result)) : False := by
  cases plain with
  | index typed => exact u64_not_pi history typed (.refl _)
  | node head _ => simp [plainNode] at head

theorem PlainIndices.no_boxed_family (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (found : env.families[family]? = some entry) (boxed : entry.boxed = true)
    (plain : PlainIndices env ctx (.node (.ind family count) indices)) : False := by
  cases plain with
  | index typed => exact u64_not_family history typed (.refl _)
  | node head _ => simp [plainNode, found, boxed] at head

end Jihoo.NativeKernel.Environment.Representation
