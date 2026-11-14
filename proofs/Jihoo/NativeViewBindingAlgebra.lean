import Jihoo.NativeViewSyntax
import Jihoo.NativeDataMotiveCongruence
import Jihoo.NativeViewExtension

/-! Reading through borrowed fields preserves binders and commutes with every
outer substitution. This is syntax algebra, without a borrow/deref computation
axiom or any assumed normalization/substitution law. -/
namespace Jihoo.NativeKernel.Environment
set_option linter.unusedSimpArgs false

theorem viewReadAt_above (borrowed : List Bool) (bound : borrowed.length ≤ x) :
    viewReadAt borrowed x = .var x := by
  simp only [viewReadAt,show ¬ x < borrowed.length by omega,false_and,ite_false]

theorem viewRead_shift (borrowed : List Bool) (term : Term) :
    viewRead borrowed (term.rename (fun x => x + borrowed.length)) =
      term.rename (fun x => x + borrowed.length) := by
  unfold viewRead
  rw [Term.subst_rename,← variable_subst_eq_rename]
  apply congrArg (fun σ => term.subst σ)
  funext x
  exact viewReadAt_above borrowed (by omega)

theorem viewReadAt_subst (borrowed : List Bool) (σ : Nat → Term) (x : Nat) :
    (viewReadAt borrowed x).subst (liftSub borrowed.length σ) =
      (liftSub borrowed.length σ x).subst (viewReadAt borrowed) := by
  by_cases bound : x < borrowed.length
  · have stable : liftSub borrowed.length σ x = .var x := by
      simpa only [Term.subst] using scoped_subst_lift (Term.Scoped.var bound) σ
    rw [stable]
    simp only [Term.subst]
    unfold viewReadAt
    split
    · simp only [Term.subst,substArgs,Op.binders,liftSub,stable]
    · simpa only [Term.subst] using stable
  · have upper : borrowed.length ≤ x := by omega
    rw [viewReadAt_above borrowed upper,Term.subst]
    have index : x = (x - borrowed.length) + borrowed.length := by omega
    rw [index,liftSub_after_shift]
    exact (viewRead_shift borrowed (σ (x - borrowed.length))).symm

theorem viewRead_subst (borrowed : List Bool) (term : Term) (σ : Nat → Term) :
    (viewRead borrowed term).subst (liftSub borrowed.length σ) =
      viewRead borrowed (term.subst (liftSub borrowed.length σ)) := by
  unfold viewRead
  rw [Term.subst_comp,Term.subst_comp]
  apply congrArg (fun τ => term.subst τ)
  funext x
  exact viewReadAt_subst borrowed σ x

theorem viewInstFields_length (depth : Nat) (ps : List Term) (previous : List Bool) (plans : List ViewFieldPlan) :
    (viewInstFields depth ps previous plans).length = plans.length := by
  induction plans generalizing previous with
  | nil => rfl
  | cons plan plans ih => simp only [viewInstFields,List.length_cons,ih]

theorem viewInstFields_subst (sourceDepth targetDepth : Nat) (ps : List Term) (previous : List Bool)
    (plans : List ViewFieldPlan)
    (scopes : ∀ (j : Nat) (plan : ViewFieldPlan),plans[j]? = some plan →
      plan.field.domain.Scoped (previous.length + j + ps.length)) (σ : Nat → Term) :
    transformDataFields σ previous.length (viewInstFields sourceDepth ps previous plans) =
      viewInstFields targetDepth (ps.map (Term.subst σ)) previous plans := by
  induction plans generalizing previous with
  | nil => rfl
  | cons plan plans ih =>
    have scopeProof := scopes 0 plan rfl
    simp only [Nat.add_zero] at scopeProof
    have domainNatural := (viewRead_subst previous
      (plan.field.domain.subst (parameterAt sourceDepth previous.length ps)) σ).trans
        (congrArg (viewRead previous) (parameterAt_subst scopeProof σ sourceDepth targetDepth))
    simp only [viewInstFields,transformDataFields]
    have fieldsNatural := ih (previous ++ [plan.borrowed]) (by
      intro j selected found
      have scopeProof := scopes (j + 1) selected found
      simpa only [List.length_append,List.length_singleton,Nat.add_assoc,Nat.add_comm 1 j] using scopeProof)
    simp only [List.length_append,List.length_singleton] at fieldsNatural
    rw [fieldsNatural]
    cases borrowed : plan.borrowed with
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      exact congrArg (fun domain => (plan.field.erased,domain) :: _) domainNatural
    | true =>
      simp only [ite_true]
      apply congrArg (fun domain => (false,domain) :: _)
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using congrArg Term.ref domainNatural

theorem viewFieldPlan_source (h : viewFieldPlan env family field = some plan) : plan.field = field := by
  unfold viewFieldPlan at h
  simp only [Option.map] at h
  repeat' first | split at h | contradiction
  all_goals cases h; rfl

theorem viewPlan_source (h : viewPlan env family fields = some plans) :
    plans.map ViewFieldPlan.field = fields := by
  unfold viewPlan at h
  induction fields generalizing plans with
  | nil => simp only [List.mapM_nil,pure,Option.some.injEq] at h; cases h; rfl
  | cons field fields ih =>
    simp only [List.mapM_cons] at h
    cases head : viewFieldPlan env family field with
    | none => simp [head] at h
    | some plan =>
      simp only [head,Bind.bind,Option.bind] at h
      cases tail : fields.mapM (viewFieldPlan env family) with
      | none => simp [tail] at h
      | some rest =>
        simp only [tail,Bind.bind,Option.bind,pure,Option.some.injEq] at h
        subst plans
        simp only [List.map_cons,viewFieldPlan_source head,ih tail]

theorem viewPlan_scoped {ps : List Term} (checked : UnifiedProgram.SignatureScoped signature)
    (h : viewPlan env family (signature.fields.drop params) = some plans)
    (count : ps.length = params) :
    ∀ (j : Nat) (plan : ViewFieldPlan),plans[j]? = some plan →
      plan.field.domain.Scoped (j + ps.length) := by
  intro j plan found
  have source := viewPlan_source h
  have selected : (signature.fields.drop params)[j]? = some plan.field := by
    rw [← source,List.getElem?_map,found]
    rfl
  have original : signature.fields[params + j]? = some plan.field := by
    simpa only [List.getElem?_drop] using selected
  have scopeProof := checked.domains (params + j) plan.field original
  simpa only [count,Nat.add_comm params j] using scopeProof

theorem viewPositions_bound (member : position ∈ viewPositions plans) : position < plans.length := by
  obtain ⟨⟨plan,j⟩,inPlans,chosen⟩ := List.mem_filterMap.mp member
  have found := List.mk_mem_zipIdx_iff_getElem?.mp inPlans
  change (if plan.self then some j else none) = some position at chosen
  by_cases flag : plan.self = true
  · simp only [flag,ite_true,Option.some.injEq] at chosen
    subst position
    exact (List.getElem?_eq_some_iff.mp found).1
  · simp only [flag,ite_false] at chosen
    contradiction

theorem viewHypothesisType_subst (bound : position < fields) (motive : Term) (σ : Nat → Term) :
    (viewHypothesisType fields motive dependent position q).subst (liftSub (fields + q) σ) =
      viewHypothesisType fields (motive.subst σ) dependent position q := by
  have shifted := Term.shift_subst motive (fields + q) σ
  simp only [← Nat.add_assoc] at shifted
  cases dependent with
  | false => exact shifted
  | true =>
    simp only [viewHypothesisType,ite_true,Term.subst,substArgs,Op.binders,liftSub]
    rw [shifted]
    have stable := scoped_subst_lift
      (Term.Scoped.var (show fields + q - 1 - position < fields + q by omega)) σ
    simpa only [Term.subst] using congrArg
      (Term.app ((motive.subst σ).rename (fun x => x + fields + q))) stable

private theorem viewCongrTwo {α β γ : Type} (f : α → β → γ) {a a' : α} {b b' : β}
    (ha : a = a') (hb : b = b') : f a b = f a' b' := by cases ha; cases hb; rfl

theorem viewHypothesisTelescope_subst (positions : List Nat)
    (bounds : ∀ position ∈ positions,position < fields) (offset : Nat) (σ : Nat → Term) :
    (viewHypothesisTelescope fields offset positions motive dependent body).subst (liftSub (fields + offset) σ) =
      viewHypothesisTelescope fields offset positions (motive.subst σ) dependent
        (body.subst (liftSub (fields + offset + positions.length) σ)) := by
  induction positions generalizing offset with
  | nil => simp only [viewHypothesisTelescope,List.zipIdx_nil,List.foldr_nil,List.length_nil,Nat.add_zero]
  | cons position positions ih =>
    have bound := bounds position (by simp)
    have remaining : ∀ p ∈ positions,p < fields := fun p member => bounds p (by simp [member])
    have inner := ih remaining (offset + 1)
    simp only [viewHypothesisTelescope,List.zipIdx_cons,List.foldr_cons,List.length_cons]
    simp only [Term.subst,substArgs,Op.binders,liftSub]
    rw [viewHypothesisType_subst bound]
    have shift1 : liftSub (fields + (offset + 1)) σ = liftSubOne (liftSub (fields + offset) σ) := by
      rw [← Nat.add_assoc]; rfl
    have shift2 : liftSub (fields + (offset + 1) + positions.length) σ =
        liftSubOne (liftSub (fields + offset + positions.length) σ) := by
      rw [show fields + (offset + 1) + positions.length = (fields + offset + positions.length) + 1 by omega]; rfl
    rw [shift1,shift2] at inner
    exact congrArg (Term.pi false (viewHypothesisType fields (motive.subst σ) dependent position offset)) inner

theorem viewCaseResult_subst (family constructor fields hypotheses : Nat) (ps : List Term)
    (motive : Term) (borrowed : List Bool) (dependent : Bool) (σ : Nat → Term) :
    (viewCaseResult family constructor fields hypotheses ps motive borrowed dependent).subst
        (liftSub (fields + hypotheses) σ) =
      viewCaseResult family constructor fields hypotheses (ps.map (Term.subst σ)) (motive.subst σ) borrowed dependent := by
  have shifted := Term.shift_subst motive (fields + hypotheses) σ
  simp only [← Nat.add_assoc] at shifted
  cases dependent with
  | false => exact shifted
  | true =>
    unfold viewCaseResult
    simp only [ite_true,Term.subst,substArgs,Op.binders,liftSub]
    rw [shifted]
    apply congrArg (Term.app ((motive.subst σ).rename (fun x => x + fields + hypotheses)))
    apply congrArg Term.borrow
    simp only [substArgs_dataCon]
    have counts : (ps.map (Term.rename (fun x => x + fields + hypotheses)) ++
        (List.range fields).map (fun j =>
          if borrowed[j]?.getD false then Term.deref (.var (fields - 1 - j + hypotheses)) else .var (fields - 1 - j + hypotheses))).length =
        ((ps.map (Term.subst σ)).map (Term.rename (fun x => x + fields + hypotheses)) ++
        (List.range fields).map (fun j =>
          if borrowed[j]?.getD false then Term.deref (.var (fields - 1 - j + hypotheses)) else .var (fields - 1 - j + hypotheses))).length := by
      simp only [List.length_append,List.length_map]
    rw [counts]
    apply congrArg (Term.node _)
    rw [List.map_append]
    apply viewCongrTwo List.append
    · simp only [List.map_map]
      apply List.map_congr_left
      intro term _
      simpa only [Function.comp_def,Nat.add_assoc] using Term.shift_subst term (fields + hypotheses) σ
    · rw [List.map_map]
      apply List.map_congr_left
      intro j member
      have bound := List.mem_range.mp member
      have stable := scoped_subst_lift
        (Term.Scoped.var (show fields - 1 - j + hypotheses < fields + hypotheses by omega)) σ
      simp only [Function.comp_def]
      split
      · simpa only [Term.subst,substArgs,Op.binders,liftSub] using congrArg Term.deref stable
      · exact stable

theorem viewCaseType_subst (checked : UnifiedProgram.SignatureScoped signature)
    (env : Environment) (family constructor params sourceDepth targetDepth : Nat) (ps : List Term)
    (motive : Term) (recursion dependent : Bool) (σ : Nat → Term) :
    (viewCaseType env family constructor params sourceDepth signature ps motive recursion dependent).map (Term.subst σ) =
      viewCaseType env family constructor params targetDepth signature (ps.map (Term.subst σ))
        (motive.subst σ) recursion dependent := by
  by_cases count : ps.length = params
  · by_cases enough : params ≤ signature.fields.length
    · have gate : (ps.length != params || decide (params > signature.fields.length)) = false := by
        simp only [count,bne_self_eq_false,gt_iff_lt,decide_eq_false_iff_not,Bool.false_or]; omega
      unfold viewCaseType
      simp only [List.length_map,gate,Bool.false_eq_true,ite_false]
      cases planned : viewPlan env family (signature.fields.drop params) with
      | none => simp only [planned,Bind.bind,Option.bind,Option.map_none]
      | some plans =>
        simp only [planned,Bind.bind,Option.bind,Option.map_some]
        apply congrArg some
        let positions := if recursion then viewPositions plans else []
        have planScopes := viewPlan_scoped checked planned count
        have domainScopes : ∀ (j : Nat) (plan : ViewFieldPlan),plans[j]? = some plan →
            plan.field.domain.Scoped (([] : List Bool).length + j + ps.length) := by
          simpa only [List.length_nil,Nat.zero_add] using planScopes
        have positionsBound : ∀ position ∈ positions,position < plans.length := by
          cases recursion with
          | false => intro p member; simp [positions] at member
          | true => exact fun p member => viewPositions_bound member
        rw [show σ = liftSub 0 σ from rfl,closeDataFields_subst]
        have fieldsNatural := viewInstFields_subst sourceDepth targetDepth ps [] plans domainScopes σ
        simp only [List.length_nil] at fieldsNatural
        rw [fieldsNatural]
        simp only [List.length_nil,Nat.zero_add,viewInstFields_length,liftSub]
        congr 1
        have hypotheses := viewHypothesisTelescope_subst (fields := plans.length)
          (motive := motive) (dependent := dependent)
          (body := viewCaseResult family constructor plans.length positions.length ps motive
            (plans.map ViewFieldPlan.borrowed) dependent) positions positionsBound 0 σ
        simp only [Nat.add_zero] at hypotheses
        rw [hypotheses,viewCaseResult_subst]
    · have greater : signature.fields.length < params := by omega
      simp [viewCaseType,count,greater]
  · simp [viewCaseType,count]

private theorem viewMapM_natural {α β γ : Type} (xs : List α) (f : α → Option β) (g : α → Option γ)
    (transform : β → γ) (natural : ∀ x ∈ xs,(f x).map transform = g x) :
    (xs.mapM f).map (List.map transform) = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have head := natural x (by simp)
    have rest := ih (fun x member => natural x (by simp [member]))
    simp only [List.mapM_cons]
    cases fx : f x with
    | none =>
      simp only [fx,Option.map_none] at head
      simp only [fx,← head,Bind.bind,Option.bind,Option.map_none]
    | some value =>
      simp only [fx,Option.map_some] at head
      rw [← head]
      cases tail : xs.mapM f with
      | none =>
        simp only [tail,Option.map_none] at rest
        simp only [fx,tail,← rest,Bind.bind,Option.bind,Option.map_none]
      | some values =>
        simp only [tail,Option.map_some] at rest
        simp only [fx,tail,← rest,Bind.bind,Option.bind,pure,Option.map_some,List.map_cons]

theorem viewCaseTypes_subst
    (checked : ∀ signature ∈ signatures,UnifiedProgram.SignatureScoped signature)
    (env : Environment) (family params sourceDepth targetDepth : Nat) (ps : List Term)
    (motive : Term) (recursion dependent : Bool) (σ : Nat → Term) :
    (viewCaseTypes env family params sourceDepth signatures ps motive recursion dependent).map (List.map (Term.subst σ)) =
      viewCaseTypes env family params targetDepth signatures (ps.map (Term.subst σ)) (motive.subst σ) recursion dependent := by
  unfold viewCaseTypes
  apply viewMapM_natural
  intro pair member
  rcases pair with ⟨signature,constructor⟩
  have found := List.mk_mem_zipIdx_iff_getElem?.mp member
  exact viewCaseType_subst (checked signature (List.mem_of_getElem? found)) env
    family constructor params sourceDepth targetDepth ps motive recursion dependent σ

theorem viewCaseTypes_subst_success
    (checked : ∀ signature ∈ signatures,UnifiedProgram.SignatureScoped signature)
    (generated : viewCaseTypes env family params sourceDepth signatures ps motive recursion dependent = some types)
    (targetDepth : Nat) (σ : Nat → Term) :
    viewCaseTypes env family params targetDepth signatures (ps.map (Term.subst σ)) (motive.subst σ) recursion dependent =
      some (types.map (Term.subst σ)) := by
  rw [← viewCaseTypes_subst checked env family params sourceDepth targetDepth ps motive recursion dependent σ,generated]
  rfl

theorem viewCaseTypes_rename
    (checked : ∀ signature ∈ signatures,UnifiedProgram.SignatureScoped signature)
    (env : Environment) (family params sourceDepth targetDepth : Nat) (ps : List Term)
    (motive : Term) (recursion dependent : Bool) (ρ : Nat → Nat) :
    (viewCaseTypes env family params sourceDepth signatures ps motive recursion dependent).map (List.map (Term.rename ρ)) =
      viewCaseTypes env family params targetDepth signatures (ps.map (Term.rename ρ)) (motive.rename ρ) recursion dependent := by
  have asSub : Term.subst (fun x => Term.var (ρ x)) = Term.rename ρ :=
    funext fun term => variable_subst_eq_rename term ρ
  simpa only [asSub] using viewCaseTypes_subst checked env family params sourceDepth targetDepth ps motive
    recursion dependent (fun x => Term.var (ρ x))

theorem viewCaseTypes_rename_success
    (checked : ∀ signature ∈ signatures,UnifiedProgram.SignatureScoped signature)
    (generated : viewCaseTypes env family params sourceDepth signatures ps motive recursion dependent = some types)
    (targetDepth : Nat) (ρ : Nat → Nat) :
    viewCaseTypes env family params targetDepth signatures (ps.map (Term.rename ρ)) (motive.rename ρ) recursion dependent =
      some (types.map (Term.rename ρ)) := by
  rw [← viewCaseTypes_rename checked env family params sourceDepth targetDepth ps motive recursion dependent ρ,generated]
  rfl

@[simp] theorem viewMotiveType_subst (dependent : Bool) (owner : Term) (σ : Nat → Term) :
    (viewMotiveType dependent owner).subst σ = viewMotiveType dependent (owner.subst σ) := by
  cases dependent <;> simp only [viewMotiveType,Bool.false_eq_true,ite_true,ite_false,Term.subst,substArgs,Op.binders,liftSub]

@[simp] theorem viewResult_subst (dependent : Bool) (motive scrutinee : Term) (σ : Nat → Term) :
    (viewResult dependent motive scrutinee).subst σ = viewResult dependent (motive.subst σ) (scrutinee.subst σ) := by
  cases dependent <;> simp only [viewResult,Bool.false_eq_true,ite_true,ite_false,Term.subst,substArgs,Op.binders,liftSub]

@[simp] theorem viewMotiveType_rename (dependent : Bool) (owner : Term) (ρ : Nat → Nat) :
    (viewMotiveType dependent owner).rename ρ = viewMotiveType dependent (owner.rename ρ) := by
  cases dependent <;> simp only [viewMotiveType,Bool.false_eq_true,ite_true,ite_false,Term.rename,renameArgs,Op.binders,liftRenaming]

@[simp] theorem viewResult_rename (dependent : Bool) (motive scrutinee : Term) (ρ : Nat → Nat) :
    (viewResult dependent motive scrutinee).rename ρ = viewResult dependent (motive.rename ρ) (scrutinee.rename ρ) := by
  cases dependent <;> simp only [viewResult,Bool.false_eq_true,ite_true,ite_false,Term.rename,renameArgs,Op.binders,liftRenaming]

end Jihoo.NativeKernel.Environment
