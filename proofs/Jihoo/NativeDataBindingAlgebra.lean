import Jihoo.NativeEnvironmentBindingAlgebra

/-! Capture-avoiding naturality of the checked data telescopes. Parameters are
actual outer terms; stored fields and recursive indices retain authentic scopes.
No equation asserts that normalization commutes with arbitrary substitution. -/
namespace Jihoo.NativeKernel.Environment
set_option linter.unusedSimpArgs false

private theorem congrTwo {α β γ : Type} (f : α → β → γ) {a a' : α} {b b' : β}
    (ha : a = a') (hb : b = b') : f a b = f a' b' := by cases ha; cases hb; rfl

 theorem parameterAt_subst {term : Term} {locals : Nat} {ps : List Term} (scope : term.Scoped (locals + ps.length))
    (σ : Nat → Term) (sourceDepth targetDepth : Nat) :
    (term.subst (parameterAt sourceDepth locals ps)).subst (liftSub locals σ) =
      term.subst (parameterAt targetDepth locals (ps.map (Term.subst σ))) := by
  rw [Term.subst_comp]
  apply scoped_subst_congr scope
  intro x bound
  unfold parameterAt
  simp only [List.length_map, ← List.map_reverse]
  split
  · rename_i below
    have stable := scoped_subst_lift (Term.Scoped.var below) σ
    simpa only [Term.subst] using stable
  · rename_i above
    have inside : x - locals < ps.reverse.length := by simp only [List.length_reverse]; omega
    cases selected : ps.reverse[x - locals]? with
    | none => have outside := List.getElem?_eq_none_iff.mp selected; omega
    | some p =>
      simp only [selected, Option.map_some, Option.getD_some, List.getElem?_map,
        Option.map_some]
      exact Term.shift_subst p locals σ

private theorem liftSub_renaming (locals : Nat) (ρ : Nat → Nat) :
    liftSub locals (fun x => Term.var (ρ x)) = fun x => Term.var (liftRenaming locals ρ x) := by
  induction locals with
  | zero => rfl
  | succ n ih =>
      funext x
      cases x <;> simp only [liftSub, liftSubOne, ih, liftRenaming, Indexed.liftRenaming, Term.rename]

 theorem parameterAt_rename {term : Term} {locals : Nat} {ps : List Term} (scope : term.Scoped (locals + ps.length))
    (ρ : Nat → Nat) (sourceDepth targetDepth : Nat) :
    (term.subst (parameterAt sourceDepth locals ps)).rename (liftRenaming locals ρ) =
      term.subst (parameterAt targetDepth locals (ps.map (Term.rename ρ))) := by
  rw [← variable_subst_eq_rename]
  rw [show (fun x => Term.var (liftRenaming locals ρ x)) = liftSub locals (fun x => Term.var (ρ x)) by
    funext x; exact (congrFun (liftSub_renaming locals ρ) x).symm]
  have natural := parameterAt_subst scope (fun x => Term.var (ρ x)) sourceDepth targetDepth
  have maps : ps.map (Term.subst (fun x => Term.var (ρ x))) = ps.map (Term.rename ρ) := by
    apply List.map_congr_left
    intro term _
    exact variable_subst_eq_rename term ρ
  rw [maps] at natural
  exact natural

/-- Substitution of a dependent field telescope follows its successive scopes. -/
def transformDataFields (σ : Nat → Term) : Nat → List (Bool × Term) → List (Bool × Term)
  | _, [] => []
  | n, (erased, domain) :: fields =>
      (erased, domain.subst (liftSub n σ)) :: transformDataFields σ (n + 1) fields

theorem closeDataFields_subst (fields : List (Bool × Term)) (n : Nat) (body : Term) (σ : Nat → Term) :
    (closeDataFields fields body).subst (liftSub n σ) =
      closeDataFields (transformDataFields σ n fields)
        (body.subst (liftSub (n + fields.length) σ)) := by
  induction fields generalizing n with
  | nil => simp only [closeDataFields, List.foldr_nil, transformDataFields, List.length_nil, Nat.add_zero]
  | cons field fields ih =>
      rcases field with ⟨erased, domain⟩
      simp only [closeDataFields, List.foldr_cons, Term.subst, substArgs, Op.binders,
        liftSub, transformDataFields, List.length_cons]
      have inner := ih (n + 1)
      simp only [closeDataFields, show n + 1 + fields.length = n + (fields.length + 1) by omega] at inner
      exact congrArg (Term.pi erased (domain.subst (liftSub n σ))) inner

theorem instantiatedFields_length (depth position : Nat) (ps : List Term) (recursion : Bool) (fields : List Field) :
    (instantiatedFields depth ps recursion position fields).length = fields.length := by
  induction fields generalizing position with
  | nil => rfl
  | cons field fields ih => simpa only [instantiatedFields, List.length_cons] using congrArg Nat.succ (ih (position + 1))

theorem instantiatedFields_subst (ps : List Term) (position sourceDepth targetDepth : Nat)
    (fields : List Field)
    (scopes : ∀ (j : Nat) (field : Field), fields[j]? = some field → field.domain.Scoped (position + j + ps.length))
    (σ : Nat → Term) :
    transformDataFields σ position (instantiatedFields sourceDepth ps recursion position fields) =
      instantiatedFields targetDepth (ps.map (Term.subst σ)) recursion position fields := by
  induction fields generalizing position with
  | nil => rfl
  | cons field fields ih =>
      simp only [instantiatedFields, transformDataFields]
      rw [parameterAt_subst (by simpa only [Nat.add_zero] using scopes 0 field rfl) σ sourceDepth targetDepth]
      congr 1
      apply ih
      intro j selected found
      have scopeProof := scopes (j + 1) selected found
      simpa only [Nat.add_assoc, Nat.add_comm 1 j] using scopeProof

theorem u64Telescope_subst (n depth : Nat) (body : Term) (σ : Nat → Term) :
    (u64Telescope n body).subst (liftSub depth σ) =
      u64Telescope n (body.subst (liftSub (depth + n) σ)) := by
  induction n generalizing depth with
  | zero => simp only [u64Telescope, Nat.add_zero]
  | succ n ih =>
      simp only [u64Telescope, Term.subst, substArgs, Op.binders, liftSub]
      have inner := ih (depth + 1)
      simpa only [show depth + 1 + n = depth + (n + 1) by omega, liftSub] using
        congrArg (Term.pi false .u64) inner

@[simp] theorem substArgs_dataInd (family arity offset : Nat) (σ : Nat → Term) (xs : List Term) :
    substArgs (.ind family arity) σ offset xs = xs.map (Term.subst σ) := by
  induction xs generalizing offset with
  | nil => simp only [substArgs,List.map_nil]
  | cons x xs ih => simp only [substArgs, Op.binders, liftSub, ih, List.map_cons]

theorem dataMotiveType_subst (family params arity : Nat) (ps : List Term) (proof : Bool) (σ : Nat → Term) :
    (dataMotiveType family params arity ps proof).subst σ =
      dataMotiveType family params arity (ps.map (Term.subst σ)) proof := by
  unfold dataMotiveType
  rw [show σ = liftSub 0 σ from rfl, u64Telescope_subst]
  simp only [Nat.zero_add]
  congr 1
  simp only [Term.subst, substArgs, Op.binders, liftSub, substArgs_dataInd]
  have sortStable : (loopSortTerm proof).subst (liftSubOne (liftSub (arity - params) σ)) = loopSortTerm proof := by
    cases proof <;> simp only [loopSortTerm, Bool.false_eq_true, ite_false, ite_true, Term.subst, substArgs]
  rw [sortStable]
  congr 2
  rw [List.map_append]
  apply congrArg (Term.node (.ind family arity))
  apply congrTwo List.append
  · simp only [List.map_map]
    apply List.map_congr_left
    intro term _
    exact Term.shift_subst term (arity - params) σ
  · rw [List.map_map]
    apply List.map_congr_left
    intro j member
    have bound := List.mem_range.mp member
    exact scoped_subst_lift (Term.Scoped.var (by omega)) σ

def transformDataRecursive (σ : Nat → Term) (recursive : List (Nat × List Term)) : List (Nat × List Term) :=
  recursive.map fun (position, indices) => (position,indices.map (Term.subst (liftSub position σ)))

theorem instantiatedRecursive_subst (fields : List Field) (ps : List Term)
    (scopes : ∀ (j : Nat) (field : Field) (indices : List Term), fields[j]? = some field → field.recursive = some indices →
      ∀ index ∈ indices, index.Scoped (j + ps.length)) (σ : Nat → Term) :
    transformDataRecursive σ (instantiatedRecursive sourceDepth ps fields) =
      instantiatedRecursive targetDepth (ps.map (Term.subst σ)) fields := by
  unfold transformDataRecursive instantiatedRecursive
  rw [List.map_map]
  apply List.map_congr_left
  intro pair member
  obtain ⟨⟨field, j⟩, inFields, selected⟩ := List.mem_filterMap.mp member
  have found := List.mk_mem_zipIdx_iff_getElem?.mp inFields
  cases recursive : field.recursive with
  | none => simp [recursive] at selected
  | some indices =>
    simp only [recursive,Option.map_some,Option.some.injEq] at selected
    subst pair
    simp only [List.map_map, Function.comp_def]
    apply congrArg (Prod.mk j)
    apply List.map_congr_left
    intro index inside
    exact parameterAt_subst (scopes j field indices found recursive index inside) σ sourceDepth targetDepth

theorem instantiatedRecursive_position
    (member : pair ∈ instantiatedRecursive depth ps fields) : pair.1 < fields.length := by
  obtain ⟨⟨j, indices⟩, original, selected⟩ := List.mem_map.mp member
  cases selected
  obtain ⟨⟨field, position⟩, inFields, selected⟩ := List.mem_filterMap.mp original
  have found := List.mk_mem_zipIdx_iff_getElem?.mp inFields
  cases recursive : field.recursive with
  | none => simp [recursive] at selected
  | some indices =>
    simp only [recursive,Option.map_some,Option.some.injEq,Prod.mk.injEq] at selected
    obtain ⟨rfl,rfl⟩ := selected
    exact (List.getElem?_eq_some_iff.mp found).1

theorem dataHypothesisType_subst {recursive : Nat × List Term} {fields params q : Nat} {motive : Term} (bound : recursive.1 < fields) (σ : Nat → Term) :
    (dataHypothesisType params fields motive recursive q).subst (liftSub (fields + q) σ) =
      dataHypothesisType params fields (motive.subst σ)
        (recursive.1, recursive.2.map (Term.subst (liftSub recursive.1 σ))) q := by
  unfold dataHypothesisType
  simp only [Term.subst, substArgs, Op.binders, liftSub]
  have shiftedMotive := Term.shift_subst motive (fields + q) σ
  simp only [← Nat.add_assoc] at shiftedMotive
  rw [applications_subst, shiftedMotive]
  have shiftedIndex : ∀ (index : Term),
      (index.rename (fun x => x + (fields + q - recursive.1))).subst (liftSub (fields + q) σ) =
      (index.subst (liftSub recursive.1 σ)).rename (fun x => x + (fields + q - recursive.1)) := by
    intro index
    have lifts : liftSub (fields + q) σ = liftSub (fields + q - recursive.1) (liftSub recursive.1 σ) := by
      rw [PartialRenaming.liftSub_add]
      congr 1
      omega
    rw [lifts]
    exact Term.shift_subst index (fields + q - recursive.1) (liftSub recursive.1 σ)
  apply congrTwo Term.app
  · apply congrArg (applications (motive.subst σ |>.rename (fun x => x + fields + q)))
    simp only [← List.map_drop, List.map_map]
    exact List.map_congr_left (fun index _ => shiftedIndex index)
  · simpa only [Term.subst] using scoped_subst_lift
      (Term.Scoped.var (show fields - 1 - recursive.1 + q < fields + q by omega)) σ

theorem dataHypothesisTelescope_subst {recursion : List (Nat × List Term)}
    {fields params : Nat} {proof : Bool} {motive body : Term}
    (bounds : ∀ recursive ∈ recursion, recursive.1 < fields)
    (offset : Nat) (σ : Nat → Term) :
    (dataHypothesisTelescope params fields offset recursion proof motive body).subst (liftSub (fields + offset) σ) =
      dataHypothesisTelescope params fields offset (transformDataRecursive σ recursion) proof (motive.subst σ)
        (body.subst (liftSub (fields + offset + recursion.length) σ)) := by
  induction recursion generalizing offset with
  | nil => simp only [dataHypothesisTelescope, List.zipIdx_nil, List.foldr_nil, transformDataRecursive,
      List.map_nil, List.length_nil, Nat.add_zero]
  | cons recursive recursion ih =>
    have bound := bounds recursive (by simp)
    have remaining : ∀ pair ∈ recursion, pair.1 < fields := fun pair member => bounds pair (by simp [member])
    have inner := ih remaining (offset + 1)
    simp only [dataHypothesisTelescope, List.zipIdx_cons, List.foldr_cons, List.length_cons,
      transformDataRecursive, List.map_cons]
    simp only [Term.subst, substArgs, Op.binders, liftSub]
    rw [dataHypothesisType_subst bound]
    have shift1 : liftSub (fields + (offset + 1)) σ = liftSubOne (liftSub (fields + offset) σ) := by
      rw [← Nat.add_assoc]; rfl
    have shift2 : liftSub (fields + (offset + 1) + recursion.length) σ =
        liftSubOne (liftSub (fields + offset + recursion.length) σ) := by
      rw [show fields + (offset + 1) + recursion.length = (fields + offset + recursion.length) + 1 by omega]; rfl
    rw [shift1,shift2] at inner
    exact congrArg (Term.pi proof (dataHypothesisType params fields (motive.subst σ)
      (recursive.1, recursive.2.map (Term.subst (liftSub recursive.1 σ))) offset)) inner

@[simp] theorem substArgs_dataCon (family constructor count offset : Nat) (σ : Nat → Term) (xs : List Term) :
    substArgs (.con family constructor count) σ offset xs = xs.map (Term.subst σ) := by
  induction xs generalizing offset with
  | nil => simp only [substArgs,List.map_nil]
  | cons x xs ih => simp only [substArgs, Op.binders, liftSub, ih, List.map_cons]

theorem dataCaseResult_subst (family constructor params fields hypotheses : Nat)
    (ps : List Term) (motive : Term) (indices : List Term) (σ : Nat → Term) :
    (dataCaseResult family constructor params fields hypotheses ps motive indices).subst
        (liftSub (fields + hypotheses) σ) =
      dataCaseResult family constructor params fields hypotheses (ps.map (Term.subst σ)) (motive.subst σ)
        (indices.map (Term.subst (liftSub fields σ))) := by
  unfold dataCaseResult
  simp only [Term.subst, substArgs, Op.binders, liftSub, substArgs_dataCon]
  apply congrTwo Term.app
  · rw [applications_subst]
    have shiftedMotive := Term.shift_subst motive (fields + hypotheses) σ
    simp only [← Nat.add_assoc] at shiftedMotive
    rw [shiftedMotive]
    apply congrArg (applications ((motive.subst σ).rename (fun x => x + fields + hypotheses)))
    simp only [← List.map_drop, List.map_map]
    apply List.map_congr_left
    intro index _
    have lifts : liftSub (fields + hypotheses) σ = liftSub hypotheses (liftSub fields σ) :=
      (PartialRenaming.liftSub_add fields hypotheses σ).symm
    rw [lifts]
    exact Term.shift_subst index hypotheses (liftSub fields σ)
  · have counts : (ps.map (Term.rename (fun x => x + fields + hypotheses)) ++
        (List.range fields).map (fun j => Term.var (fields - 1 - j + hypotheses))).length =
        ((ps.map (Term.subst σ)).map (Term.rename (fun x => x + fields + hypotheses)) ++
        (List.range fields).map (fun j => Term.var (fields - 1 - j + hypotheses))).length := by
      simp only [List.length_append,List.length_map]
    rw [counts]
    apply congrArg (Term.node _)
    rw [List.map_append]
    apply congrTwo List.append
    · simp only [List.map_map]
      apply List.map_congr_left
      intro term _
      simpa only [Nat.add_assoc,Function.comp_def] using Term.shift_subst term (fields + hypotheses) σ
    · rw [List.map_map]
      apply List.map_congr_left
      intro j member
      have bound := List.mem_range.mp member
      exact scoped_subst_lift (Term.Scoped.var (show fields - 1 - j + hypotheses < fields + hypotheses by omega)) σ

theorem dataCaseType_subst (checked : UnifiedProgram.SignatureScoped signature)
    (family constructor params sourceDepth targetDepth : Nat) (ps : List Term)
    (motive : Term) (recursion proof : Bool) (σ : Nat → Term) :
    (dataCaseType family constructor params sourceDepth signature ps motive recursion proof).map (Term.subst σ) =
      dataCaseType family constructor params targetDepth signature (ps.map (Term.subst σ))
        (motive.subst σ) recursion proof := by
  by_cases count : ps.length = params
  · by_cases enough : params ≤ signature.fields.length
    · let fields := signature.fields.drop params
      let recursive := if recursion then instantiatedRecursive sourceDepth ps fields else []
      let recursive' := if recursion then instantiatedRecursive targetDepth (ps.map (Term.subst σ)) fields else []
      have fieldScopes : ∀ (j : Nat) (field : Field), fields[j]? = some field →
          field.domain.Scoped (0 + j + ps.length) := by
        intro j field found
        have original : signature.fields[params + j]? = some field := by simpa only [fields,List.getElem?_drop] using found
        have scopeProof := checked.domains (params + j) field original
        simpa only [count,Nat.zero_add,Nat.add_comm params j] using scopeProof
      have recursiveScopes : ∀ (j : Nat) (field : Field) (indices : List Term),
          fields[j]? = some field → field.recursive = some indices →
          ∀ index ∈ indices, index.Scoped (j + ps.length) := by
        intro j field indices found marker
        have original : signature.fields[params + j]? = some field := by simpa only [fields,List.getElem?_drop] using found
        intro index member
        have scopeProof := checked.recursive (params + j) field indices original marker index member
        simpa only [count,Nat.add_comm params j] using scopeProof
      have recursiveNatural : transformDataRecursive σ recursive = recursive' := by
        cases recursion with
        | false => rfl
        | true => exact instantiatedRecursive_subst fields ps recursiveScopes σ
      have recursiveLength : recursive'.length = recursive.length := by
        rw [← recursiveNatural]
        simp only [transformDataRecursive,List.length_map]
      have recursiveBounds : ∀ pair ∈ recursive, pair.1 < fields.length := by
        cases recursion with
        | false => intro pair member; simp [recursive] at member
        | true => exact fun pair member => instantiatedRecursive_position member
      have indexNatural :
          (signature.result.map (Term.subst (parameterAt sourceDepth fields.length ps))).map
            (Term.subst (liftSub fields.length σ)) =
          signature.result.map (Term.subst (parameterAt targetDepth fields.length (ps.map (Term.subst σ)))) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro index member
        have scopeProof : index.Scoped (fields.length + ps.length) := by
          have total : fields.length + ps.length = signature.fields.length := by
            simp only [fields,List.length_drop,count]; omega
          rw [total]
          exact checked.result index member
        exact parameterAt_subst scopeProof σ sourceDepth targetDepth
      have gate : (ps.length != params || decide (params > signature.fields.length)) = false := by
        simp only [count,bne_self_eq_false,gt_iff_lt,decide_eq_false_iff_not,Bool.false_or]
        omega
      unfold dataCaseType
      simp only [List.length_map,gate,Bool.false_eq_true,ite_false,Option.map_some]
      apply congrArg some
      change (closeDataFields (instantiatedFields sourceDepth ps recursion 0 fields)
        (dataHypothesisTelescope params fields.length 0 recursive proof motive
          (dataCaseResult family constructor params fields.length recursive.length ps motive
            (signature.result.map (Term.subst (parameterAt sourceDepth fields.length ps)))))).subst σ =
        closeDataFields (instantiatedFields targetDepth (ps.map (Term.subst σ)) recursion 0 fields)
          (dataHypothesisTelescope params fields.length 0 recursive' proof (motive.subst σ)
            (dataCaseResult family constructor params fields.length recursive'.length (ps.map (Term.subst σ)) (motive.subst σ)
              (signature.result.map (Term.subst (parameterAt targetDepth fields.length (ps.map (Term.subst σ)))))))
      rw [show σ = liftSub 0 σ from rfl,closeDataFields_subst]
      rw [instantiatedFields_subst ps 0 sourceDepth targetDepth fields fieldScopes σ]
      simp only [instantiatedFields_length,Nat.zero_add]
      congr 1
      simp only [liftSub]
      have hypotheses := dataHypothesisTelescope_subst (params := params) (proof := proof) (motive := motive)
        (body := dataCaseResult family constructor params fields.length recursive.length ps motive
          (signature.result.map (Term.subst (parameterAt sourceDepth fields.length ps)))) recursiveBounds 0 σ
      simp only [Nat.add_zero] at hypotheses
      rw [hypotheses]
      rw [recursiveNatural,recursiveLength,dataCaseResult_subst,indexNatural]
    · have greater : signature.fields.length < params := by omega
      simp [dataCaseType,count,greater]
  · simp [dataCaseType,count]

private theorem mapM_natural {α β γ : Type} (xs : List α) (f : α → Option β) (g : α → Option γ)
    (transform : β → γ) (natural : ∀ x ∈ xs, (f x).map transform = g x) :
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

theorem dataCaseTypes_subst
    (checked : ∀ signature ∈ signatures, UnifiedProgram.SignatureScoped signature)
    (family params sourceDepth targetDepth : Nat) (ps : List Term)
    (motive : Term) (recursion proof : Bool) (σ : Nat → Term) :
    (dataCaseTypes family params sourceDepth signatures ps motive recursion proof).map (List.map (Term.subst σ)) =
      dataCaseTypes family params targetDepth signatures (ps.map (Term.subst σ)) (motive.subst σ) recursion proof := by
  unfold dataCaseTypes
  apply mapM_natural
  intro pair member
  rcases pair with ⟨signature,constructor⟩
  have found := List.mk_mem_zipIdx_iff_getElem?.mp member
  exact dataCaseType_subst (checked signature (List.mem_of_getElem? found))
    family constructor params sourceDepth targetDepth ps motive recursion proof σ

theorem dataCaseTypes_subst_success
    (checked : ∀ signature ∈ signatures, UnifiedProgram.SignatureScoped signature)
    (generated : dataCaseTypes family params sourceDepth signatures ps motive recursion proof = some types)
    (targetDepth : Nat) (σ : Nat → Term) :
    dataCaseTypes family params targetDepth signatures (ps.map (Term.subst σ)) (motive.subst σ) recursion proof =
      some (types.map (Term.subst σ)) := by
  rw [← dataCaseTypes_subst checked family params sourceDepth targetDepth ps motive recursion proof σ,generated]
  rfl

theorem dataMotiveType_rename (family params arity : Nat) (ps : List Term) (proof : Bool) (ρ : Nat → Nat) :
    (dataMotiveType family params arity ps proof).rename ρ =
      dataMotiveType family params arity (ps.map (Term.rename ρ)) proof := by
  have asSub : Term.subst (fun x => Term.var (ρ x)) = Term.rename ρ :=
    funext fun term => variable_subst_eq_rename term ρ
  simpa only [asSub] using dataMotiveType_subst family params arity ps proof (fun x => Term.var (ρ x))

theorem dataCaseType_rename (checked : UnifiedProgram.SignatureScoped signature)
    (family constructor params sourceDepth targetDepth : Nat) (ps : List Term)
    (motive : Term) (recursion proof : Bool) (ρ : Nat → Nat) :
    (dataCaseType family constructor params sourceDepth signature ps motive recursion proof).map (Term.rename ρ) =
      dataCaseType family constructor params targetDepth signature (ps.map (Term.rename ρ))
        (motive.rename ρ) recursion proof := by
  have asSub : Term.subst (fun x => Term.var (ρ x)) = Term.rename ρ :=
    funext fun term => variable_subst_eq_rename term ρ
  simpa only [asSub] using dataCaseType_subst checked family constructor params sourceDepth targetDepth ps motive
    recursion proof (fun x => Term.var (ρ x))

theorem dataCaseTypes_rename
    (checked : ∀ signature ∈ signatures, UnifiedProgram.SignatureScoped signature)
    (family params sourceDepth targetDepth : Nat) (ps : List Term)
    (motive : Term) (recursion proof : Bool) (ρ : Nat → Nat) :
    (dataCaseTypes family params sourceDepth signatures ps motive recursion proof).map (List.map (Term.rename ρ)) =
      dataCaseTypes family params targetDepth signatures (ps.map (Term.rename ρ)) (motive.rename ρ) recursion proof := by
  have asSub : Term.subst (fun x => Term.var (ρ x)) = Term.rename ρ :=
    funext fun term => variable_subst_eq_rename term ρ
  simpa only [asSub] using dataCaseTypes_subst checked family params sourceDepth targetDepth ps motive
    recursion proof (fun x => Term.var (ρ x))

theorem dataCaseTypes_rename_success
    (checked : ∀ signature ∈ signatures, UnifiedProgram.SignatureScoped signature)
    (generated : dataCaseTypes family params sourceDepth signatures ps motive recursion proof = some types)
    (targetDepth : Nat) (ρ : Nat → Nat) :
    dataCaseTypes family params targetDepth signatures (ps.map (Term.rename ρ)) (motive.rename ρ) recursion proof =
      some (types.map (Term.rename ρ)) := by
  rw [← dataCaseTypes_rename checked family params sourceDepth targetDepth ps motive recursion proof ρ,generated]
  rfl

end Jihoo.NativeKernel.Environment
