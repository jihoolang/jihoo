import Jihoo.NativeEnvironmentWellFormed
import Jihoo.NativeLoopTelescopes
import Jihoo.NativeResourceSyntax

/-! Binding algebra for fixed closed environment entries and the dependent
proposition-case/continuation telescopes used by the unified judgment. -/
namespace Jihoo.NativeKernel.Environment

private theorem liftRenaming_agree {depth : Nat} {ρ τ : Nat → Nat}
    (same : ∀ x < depth, ρ x = τ x) (binders : Nat) :
    ∀ x < depth + binders, liftRenaming binders ρ x = liftRenaming binders τ x := by
  induction binders with
  | zero => exact same
  | succ n ih =>
      intro x bound
      cases x with
      | zero => rfl
      | succ x =>
          exact congrArg Nat.succ (ih x (by omega))

private theorem liftSub_agree {depth : Nat} {σ τ : Nat → Term}
    (same : ∀ x < depth, σ x = τ x) (binders : Nat) :
    ∀ x < depth + binders, liftSub binders σ x = liftSub binders τ x := by
  induction binders with
  | zero => exact same
  | succ n ih =>
      intro x bound
      cases x with
      | zero => rfl
      | succ x =>
          exact congrArg (Term.rename Nat.succ) (ih x (by omega))

theorem scoped_rename_congr {term : Term} {depth : Nat} {ρ τ : Nat → Nat} (scope : term.Scoped depth)
    (same : ∀ x < depth, ρ x = τ x) : term.rename ρ = term.rename τ := by
  induction scope generalizing ρ τ with
  | var bound => simp only [Term.rename, same _ bound]
  | @node arguments depth op scopes ih =>
      simp only [Term.rename]
      apply congrArg (Term.node op)
      apply List.ext_getElem?
      intro index
      rw [renameArgs_get, renameArgs_get]
      cases found : arguments[index]? with
      | none => simp only [Option.map_none]
      | some child =>
          simp only [Option.map_some]
          apply congrArg some
          exact ih index child found (by simpa only [Nat.zero_add] using liftRenaming_agree same (op.binders index))

theorem scoped_subst_congr {term : Term} {depth : Nat} {σ τ : Nat → Term} (scope : term.Scoped depth)
    (same : ∀ x < depth, σ x = τ x) : term.subst σ = term.subst τ := by
  induction scope generalizing σ τ with
  | var bound => simp only [Term.subst, same _ bound]
  | @node arguments depth op scopes ih =>
      simp only [Term.subst]
      apply congrArg (Term.node op)
      apply List.ext_getElem?
      intro index
      rw [substArgs_get, substArgs_get]
      cases found : arguments[index]? with
      | none => simp only [Option.map_none]
      | some child =>
          simp only [Option.map_some]
          apply congrArg some
          exact ih index child found (by simpa only [Nat.zero_add] using liftSub_agree same (op.binders index))

theorem closed_rename {term : Term} (scope : term.Scoped 0) (ρ : Nat → Nat) : term.rename ρ = term := by
  exact (scoped_rename_congr scope (ρ := ρ) (τ := id) (by intro x bound; omega)).trans (Term.rename_id term)

theorem closed_subst {term : Term} (scope : term.Scoped 0) (σ : Nat → Term) : term.subst σ = term := by
  exact (scoped_subst_congr scope (σ := σ) (τ := Term.var) (by intro x bound; omega)).trans (Term.subst_id term)

private theorem liftRenaming_below (n : Nat) (ρ : Nat → Nat) :
    ∀ x < n, liftRenaming n ρ x = x := by
  induction n with
  | zero => intro x bound; omega
  | succ n ih =>
      intro x bound
      cases x with
      | zero => rfl
      | succ x => exact congrArg Nat.succ (ih x (by omega))

private theorem liftSub_below (n : Nat) (σ : Nat → Term) :
    ∀ x < n, liftSub n σ x = .var x := by
  induction n with
  | zero => intro x bound; omega
  | succ n ih =>
      intro x bound
      cases x with
      | zero => rfl
      | succ x => simp only [liftSub, liftSubOne, ih x (by omega), Term.rename]

theorem scoped_rename_lift {term : Term} {n : Nat} (scope : term.Scoped n) (ρ : Nat → Nat) :
    term.rename (liftRenaming n ρ) = term :=
  (scoped_rename_congr scope (τ := id) (liftRenaming_below n ρ)).trans (Term.rename_id term)

theorem scoped_subst_lift {term : Term} {n : Nat} (scope : term.Scoped n) (σ : Nat → Term) :
    term.subst (liftSub n σ) = term :=
  (scoped_subst_congr scope (τ := Term.var) (liftSub_below n σ)).trans (Term.subst_id term)

theorem applications_rename (function : Term) (arguments : List Term) (ρ : Nat → Nat) :
    (applications function arguments).rename ρ =
      applications (function.rename ρ) (arguments.map (Term.rename ρ)) := by
  induction arguments generalizing function with
  | nil => simp only [applications, List.foldl_nil, List.map_nil]
  | cons argument rest ih =>
      simp only [applications, List.foldl_cons, List.map_cons] at ih ⊢
      rw [ih]
      simp only [Term.rename, renameArgs, Op.binders, liftRenaming]

theorem applications_subst (function : Term) (arguments : List Term) (σ : Nat → Term) :
    (applications function arguments).subst σ =
      applications (function.subst σ) (arguments.map (Term.subst σ)) := by
  induction arguments generalizing function with
  | nil => simp only [applications, List.foldl_nil, List.map_nil]
  | cons argument rest ih =>
      simp only [applications, List.foldl_cons, List.map_cons] at ih ⊢
      rw [ih]
      simp only [Term.subst, substArgs, Op.binders, liftSub]

def hypothesisType (fields : Nat) (motive : Term) (recursive : Nat × List Term) (q : Nat) : Term :=
  applications (motive.rename (fun x => x + fields + q))
    (recursive.2.map fun term => term.rename (fun x => x + (fields + q - recursive.1)))

def hypothesisTelescope (fields offset : Nat) (recursive : List (Nat × List Term)) (motive body : Term) : Term :=
  (recursive.zipIdx offset).foldr (fun (field, q) rest => .pi true (hypothesisType fields motive field q) rest) body

theorem propCaseType_eq (signature : Signature) (motive : Term) :
    propCaseType signature motive = signature.fields.foldr (fun field rest => .pi field.erased field.domain rest)
      (hypothesisTelescope signature.fields.length 0 (recursiveFields signature.fields) motive
        (applications (motive.rename (fun x => x + signature.fields.length + (recursiveFields signature.fields).length))
          (signature.result.map fun term => term.rename (fun x => x + (recursiveFields signature.fields).length)))) := by
  simp [propCaseType, hypothesisTelescope, hypothesisType]

theorem variable_subst_eq_rename (term : Term) (ρ : Nat → Nat) :
    term.subst (fun x => .var (ρ x)) = term.rename ρ := by
  simpa only [Term.subst_id, Term.rename] using (Term.rename_subst term Term.var ρ).symm

theorem shifted_scoped {term : Term} {earlier later : Nat} (scope : term.Scoped earlier) (bound : earlier ≤ later) :
    (term.rename (fun x => x + (later - earlier))).Scoped later :=
  scope.rename (fun x inside => by omega)

def RecursiveScoped (fields : Nat) (recursive : List (Nat × List Term)) : Prop :=
  ∀ field ∈ recursive, field.1 ≤ fields ∧ ∀ term ∈ field.2, term.Scoped field.1

theorem recursiveFields_scoped (checked : UnifiedProgram.SignatureScoped signature) :
    RecursiveScoped signature.fields.length (recursiveFields signature.fields) := by
  intro pair member
  obtain ⟨⟨field, position⟩, fieldMember, result⟩ := List.mem_filterMap.mp member
  have found := List.mk_mem_zipIdx_iff_getElem?.mp fieldMember
  cases recursive : field.recursive with
  | none => simp [recursive] at result
  | some indices =>
      simp only [recursive, Option.map_some, Option.some.injEq] at result
      subst pair
      exact ⟨Nat.le_of_lt (List.getElem?_eq_some_iff.mp found).1,
        checked.recursive position field indices found recursive⟩

theorem hypothesisType_subst (scope : pair.1 ≤ fields ∧ ∀ term ∈ pair.2, term.Scoped pair.1)
    (motive : Term) (q : Nat) (σ : Nat → Term) :
    (hypothesisType fields motive pair q).subst (liftSub (fields + q) σ) =
      hypothesisType fields (motive.subst σ) pair q := by
  unfold hypothesisType
  rw [applications_subst]
  simp only [Nat.add_assoc]
  rw [Term.shift_subst]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro term member
  exact scoped_subst_lift (shifted_scoped (scope.2 term member) (by omega)) σ

theorem fieldTelescope_subst (fields : List Field) (depth : Nat) (body : Term)
    (domains : ∀ (index : Nat) field, fields[index]? = some field → field.domain.Scoped (depth + index))
    (σ : Nat → Term) :
    (fields.foldr (fun field rest => Term.pi field.erased field.domain rest) body).subst (liftSub depth σ) =
      fields.foldr (fun field rest => Term.pi field.erased field.domain rest)
        (body.subst (liftSub (depth + fields.length) σ)) := by
  induction fields generalizing depth with
  | nil => simp only [List.foldr_nil, List.length_nil, Nat.add_zero]
  | cons field fields ih =>
      have domainScope : field.domain.Scoped depth := by simpa only [Nat.add_zero] using domains 0 field rfl
      have remaining : ∀ (index : Nat) selected, fields[index]? = some selected →
          selected.domain.Scoped (depth + 1 + index) := by
        intro index selected found
        have scope := domains (index + 1) selected found
        simpa only [Nat.add_assoc, Nat.add_comm 1 index] using scope
      have inner := ih (depth + 1) remaining
      simpa only [List.foldr_cons, List.length_cons, Term.pi, Term.subst, substArgs, Op.binders, liftSub,
        scoped_subst_lift domainScope σ, Nat.add_assoc, Nat.add_comm 1 fields.length] using
        congrArg (Term.pi field.erased field.domain) inner

theorem hypothesisTelescope_subst (scope : RecursiveScoped fields recursive)
    (offset : Nat) (motive body : Term) (σ : Nat → Term) :
    (hypothesisTelescope fields offset recursive motive body).subst (liftSub (fields + offset) σ) =
      hypothesisTelescope fields offset recursive (motive.subst σ)
        (body.subst (liftSub (fields + offset + recursive.length) σ)) := by
  induction recursive generalizing offset with
  | nil => simp only [hypothesisTelescope, List.zipIdx_nil, List.foldr_nil, List.length_nil, Nat.add_zero]
  | cons pair recursive ih =>
      have pairScope := scope pair (by simp)
      have remaining : RecursiveScoped fields recursive := fun field member => scope field (by simp [member])
      have inner := ih remaining (offset + 1)
      simp only [hypothesisTelescope, List.zipIdx_cons, List.foldr_cons, List.length_cons]
      simp only [Term.subst, substArgs, Op.binders, liftSub]
      rw [hypothesisType_subst pairScope motive offset σ]
      have shift1 : liftSub (fields + (offset + 1)) σ = liftSubOne (liftSub (fields + offset) σ) := by
        rw [← Nat.add_assoc]
        rfl
      have shift2 : liftSub (fields + (offset + 1) + recursive.length) σ =
          liftSubOne (liftSub (fields + offset + recursive.length) σ) := by
        rw [show fields + (offset + 1) + recursive.length = (fields + offset + recursive.length) + 1 by omega]
        rfl
      rw [shift1, shift2] at inner
      exact congrArg (Term.pi true (hypothesisType fields (motive.subst σ) pair offset)) inner

theorem propCaseType_subst (checked : UnifiedProgram.SignatureScoped signature) (motive : Term) (σ : Nat → Term) :
    (propCaseType signature motive).subst σ = propCaseType signature (motive.subst σ) := by
  rw [propCaseType_eq, propCaseType_eq]
  have transformed := fieldTelescope_subst signature.fields 0
    (hypothesisTelescope signature.fields.length 0 (recursiveFields signature.fields) motive
      (applications (motive.rename (fun x => x + signature.fields.length + (recursiveFields signature.fields).length))
        (signature.result.map fun term => term.rename (fun x => x + (recursiveFields signature.fields).length))))
    (fun index field found => by simpa only [Nat.zero_add] using checked.domains index field found) σ
  simp only [liftSub] at transformed
  rw [transformed]
  congr 1
  simp only [Nat.zero_add]
  have hypotheses := hypothesisTelescope_subst (recursiveFields_scoped checked) 0 motive
    (applications (motive.rename (fun x => x + signature.fields.length + (recursiveFields signature.fields).length))
      (signature.result.map fun term => term.rename (fun x => x + (recursiveFields signature.fields).length))) σ
  simp only [Nat.add_zero] at hypotheses
  rw [hypotheses]
  congr 1
  rw [applications_subst]
  simp only [Nat.add_assoc]
  rw [Term.shift_subst]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro term member
  have scope : (term.rename (fun x => x + (recursiveFields signature.fields).length)).Scoped
      (signature.fields.length + (recursiveFields signature.fields).length) :=
    (checked.result term member).rename (fun x inside => by omega)
  exact scoped_subst_lift scope σ

theorem propCaseType_rename (checked : UnifiedProgram.SignatureScoped signature) (motive : Term) (ρ : Nat → Nat) :
    (propCaseType signature motive).rename ρ = propCaseType signature (motive.rename ρ) := by
  rw [← variable_subst_eq_rename, propCaseType_subst checked, variable_subst_eq_rename]

private theorem partial_inverse_lift {lowerMap : Nat → Option Nat} {total : Nat → Nat}
    (inverse : ∀ x, lowerMap (total x) = some x) (n : Nat) :
    ∀ x, PartialRenaming.lift n lowerMap (liftRenaming n total x) = some x := by
  induction n with
  | zero => exact inverse
  | succ n ih =>
      intro x
      cases x with
      | zero => rfl
      | succ x => simp only [PartialRenaming.lift, PartialRenaming.liftOne, liftRenaming,
          Indexed.liftRenaming, ih, Option.map_some]

private theorem partial_undo_rename (term : Term) {lowerMap : Nat → Option Nat} {total : Nat → Nat}
    (inverse : ∀ x, lowerMap (total x) = some x) :
    PartialRenaming.rename? lowerMap (term.rename total) = some term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ op offset lowerMap total,
      (∀ x, lowerMap (total x) = some x) →
      PartialRenaming.renameArgs? op lowerMap offset (renameArgs op total offset terms) = some terms)
    generalizing lowerMap total with
  | var index => simp only [Term.rename, PartialRenaming.rename?, inverse, Option.map_some]
  | node op arguments ih =>
      simp only [Term.rename, PartialRenaming.rename?, ih op 0 lowerMap total inverse, Option.map_some]
  | nil => rename_i op offset lowerMap total inverse; simp only [renameArgs, PartialRenaming.renameArgs?]
  | cons term rest ih iht =>
      rename_i op offset lowerMap total inverse
      simp only [renameArgs, PartialRenaming.renameArgs?,
        ih (partial_inverse_lift inverse (op.binders offset)),
        iht op (offset + 1) lowerMap total inverse, Bind.bind, Option.bind]

theorem lower_raised (term : Term) (amount : Nat) :
    PartialRenaming.lower 0 amount (term.rename (fun x => x + amount)) = some term := by
  apply partial_undo_rename
  intro x
  simp only [PartialRenaming.lowerIndex, Nat.not_lt_zero, ↓reduceIte, Nat.zero_add]
  simp only [show amount ≤ x + amount by omega, ↓reduceIte, Nat.add_sub_cancel]

theorem load_result_shifted (term : Term) :
    PartialRenaming.shift (-2) 0 (term.rename (fun x => x + 2)) = some term := by
  rw [PartialRenaming.shift_negative (by decide : (-2 : Int) < 0)]
  exact lower_raised term 2

@[simp] theorem propMotiveType_subst (arity : Nat) (σ : Nat → Term) :
    (propMotiveType arity).subst σ = propMotiveType arity := by
  induction arity generalizing σ with
  | zero => simp only [propMotiveType, Term.subst, substArgs]
  | succ arity ih => simp only [propMotiveType, Term.subst, substArgs, Op.binders, liftSub, ih]

@[simp] theorem propMotiveType_rename (arity : Nat) (ρ : Nat → Nat) :
    (propMotiveType arity).rename ρ = propMotiveType arity := by
  rw [← variable_subst_eq_rename, propMotiveType_subst]

end Jihoo.NativeKernel.Environment
