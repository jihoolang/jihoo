import Jihoo.NativePlainIndices
import Jihoo.NativeTypedChildren

/-! Forward preservation of representation modulo actual typed indices.
No arbitrary quotient-parallel term is assumed well typed. -/
namespace Jihoo.NativeKernel.Environment.Representation
open Environment.Conversion

structure PlainTransform (env : Environment) (input output : Term) : Prop where
  forward : EnvironmentDelta.Forward env input output
  preserves : ∀ {ctx mode type}, HasType env ctx mode input type →
    PlainIndices env ctx input → PlainIndices env ctx output

theorem PlainTransform.converted (change : PlainTransform env input output) : Conversion.Conv env input output :=
  EnvironmentDelta.Basis.forward_toConv change.forward

private theorem list_forward (changes : ListRel (PlainTransform env) xs ys) :
    ListRel (EnvironmentDelta.Forward env) xs ys := by
  induction changes with
  | nil => exact .nil
  | cons first rest ih => exact .cons first.forward ih

private theorem list_target (changes : ListRel R xs ys) (member : y ∈ ys) :
    ∃ x, x ∈ xs ∧ R x y := by
  induction changes with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, by simp, first⟩
      · obtain ⟨x, member, related⟩ := ih member
        exact ⟨x, List.mem_cons_of_mem _ member, related⟩

private theorem list_two (changes : ListRel R [a,b] ys) :
    ∃ a' b', ys = [a',b'] ∧ R a a' ∧ R b b' := by
  cases changes with
  | cons first rest =>
      cases rest with
      | cons second rest =>
          cases rest
          exact ⟨_,_,rfl,first,second⟩

private theorem list_four (changes : ListRel R [a,b,c,d] ys) :
    ∃ a' b' c' d', ys = [a',b',c',d'] ∧ R a a' ∧ R b b' ∧ R c c' ∧ R d d' := by
  cases changes with
  | cons first rest =>
      cases rest with
      | cons second rest =>
          cases rest with
          | cons third rest =>
              cases rest with
              | cons fourth rest =>
                  cases rest
                  exact ⟨_,_,_,_,rfl,first,second,third,fourth⟩

theorem PlainTransform.refl (term : Term) : PlainTransform env term term :=
  ⟨.refl,fun _ plain => plain⟩

theorem PlainTransform.trans (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (first : PlainTransform env a b) (second : PlainTransform env b c) : PlainTransform env a c :=
  ⟨.trans first.forward second.forward,fun typed plain =>
    second.preserves (typed.ghostForward history first.forward) (first.preserves typed plain)⟩

/-- Every node child is transformed at its actual source binder context. -/
theorem PlainTransform.node (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (changes : ListRel (PlainTransform env) xs ys) : PlainTransform env (.node op xs) (.node op ys) := by
  refine ⟨.node op (list_forward changes),?_⟩
  intro ctx mode type typed plain
  cases plain with
  | index indexTyped => exact .index (indexTyped.ghostForward history (.node op (list_forward changes)))
  | node head children =>
      apply PlainIndices.node head
      intro child member
      obtain ⟨original, found, change⟩ := list_target changes member
      obtain ⟨childType, childTyped⟩ := typed.childrenTyped _ _ rfl (plainNode_noBinders head) _ found
      exact change.preserves childTyped (children _ found)
  | @lam domain erased ctx body bodyPlain =>
      obtain ⟨domain',body',rfl,domainChange,bodyChange⟩ := list_two changes
      obtain ⟨_,_,_,bodyTyped,_⟩ := typed.lamView
      apply PlainIndices.lam
      exact (bodyChange.preserves bodyTyped bodyPlain).context history.wellFormed
        ((Ghost.ContextConversion.refl env _).extend domainChange.converted _ history.wellFormed.closed)
  | @ifLt ctx left right yes no leftPlain rightPlain yesPlain noPlain =>
      obtain ⟨left',right',yes',no',rfl,leftChange,rightChange,yesChange,noChange⟩ := list_four changes
      obtain ⟨_,leftTyped,rightTyped,yesTyped,noTyped,_⟩ := typed.ifLtView
      apply PlainIndices.ifLt (leftChange.preserves leftTyped leftPlain)
        (rightChange.preserves rightTyped rightPlain)
      · exact (yesChange.preserves yesTyped yesPlain).context history.wellFormed
          ((Ghost.ContextConversion.refl env _).extend
            (.node .lt (.cons leftChange.converted (.cons rightChange.converted .nil))) _ history.wellFormed.closed)
      · exact noChange.preserves noTyped noPlain
  | @ifEq ctx left right yes no leftPlain rightPlain yesPlain noPlain =>
      obtain ⟨left',right',yes',no',rfl,leftChange,rightChange,yesChange,noChange⟩ := list_four changes
      obtain ⟨_,leftTyped,rightTyped,yesTyped,noTyped,_⟩ := typed.ifEqView
      apply PlainIndices.ifEq (leftChange.preserves leftTyped leftPlain)
        (rightChange.preserves rightTyped rightPlain)
      · exact (yesChange.preserves yesTyped yesPlain).context history.wellFormed
          ((Ghost.ContextConversion.refl env _).extend
            (.node .eq (.cons leftChange.converted (.cons rightChange.converted .nil))) _ history.wellFormed.closed)
      · exact noChange.preserves noTyped noPlain

private theorem uadd_transform (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (step : ACU.ArithmeticRed (.uadd left right) output) :
    PlainTransform env (.uadd left right) output := by
  refine ⟨.acu (.arithmetic step),?_⟩
  intro ctx mode type typed _
  have result : Conv env .u64 type := typed.principalView
  exact .index ((typed.convert result.symm).ghostArithmeticRed history.wellFormed step)

theorem arithmetic_plain_transform (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (step : ACU.ArithmeticRed input output) : PlainTransform env input output := by
  induction step using ACU.ArithmeticRed.rec
    (motive_2 := fun xs ys _ => ListRel (PlainTransform env) xs ys) with
  | refl term => exact .refl term
  | trans first second ihfirst ihsecond => exact ihfirst.trans history ihsecond
  | node op children ih => exact .node history ih
  | assocRight a b c => exact uadd_transform history (.assocRight a b c)
  | assocLeft a b c => exact uadd_transform history (.assocLeft a b c)
  | comm a b => exact uadd_transform history (.comm a b)
  | zeroRight a => exact uadd_transform history (.zeroRight a)
  | zeroLeft a => exact uadd_transform history (.zeroLeft a)
  | literalAdd a b bound => exact uadd_transform history (.literalAdd a b bound)
  | literalSplit n bound =>
      refine ⟨.acu (.arithmetic (.literalSplit n bound)),?_⟩
      intro ctx mode type _ _
      exact .index ((HasType.natural (env := env) (ctx := ctx) (ghost := true) bound).ghostArithmeticRed history.wellFormed
        (.literalSplit n bound))
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

end Jihoo.NativeKernel.Environment.Representation
