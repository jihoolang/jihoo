import Jihoo.NativeEnvironmentWellFormed
import Jihoo.NativeFamilyEnvironment

/-! Source telescope checking against the same unified earlier environment.
Ordinary fields may contain earlier checked data and buffers. Self references
remain restricted to whole recursive fields and the literal final result. -/
namespace Jihoo.NativeKernel.UnifiedProgram.Families
open Environment

abbrev Declaration := FamilyDeclaration
abbrev fieldContext := FamilyEnvironment.fieldContext

mutual
  def selfFree (self : Nat) : Term → Bool
    | .var _ => true
    | .node op arguments =>
        (match op with | .ind family _ => decide (family ≠ self) | _ => true) && selfFreeArgs self arguments
    termination_by term => sizeOf term
  def selfFreeArgs (self : Nat) : List Term → Bool
    | [] => true
    | term :: rest => selfFree self term && selfFreeArgs self rest
    termination_by terms => sizeOf terms
end

def runtimeFieldOK (env : Environment) (data erased : Bool) (domain : Term) : Bool :=
  erased || if !data then decide (domain = .u64) else
    match domain with
    | .u64 | .i64 | .refine _ | .buffer _ => true
    | .node (.ind family _) _ => (env.families[family]?).any fun entry => entry.declaration.data
    | _ => false

def IndexChecked (env : Environment) (self : Nat) (ctx : Context) (source normal : Term) : Prop :=
  selfFree self source = true ∧ ∃ expanded,
    GlobalEnvironment.Expansion env.globals source expanded ∧
    Environment.HasType env ctx true expanded .u64 ∧ Environment.Conversion.Conv env expanded normal ∧
    Environment.HasType env ctx true normal .u64

abbrev IndicesChecked (env : Environment) (self : Nat) (ctx : Context) :=
  FamilyEnvironment.RelList (IndexChecked env self ctx)

def checkIndex (fuel : Nat) (env : Environment) (self : Nat) (ctx : Context) (source : Term) : Option Term := do
  if selfFree self source then
    let expanded ← GlobalEnvironment.expand fuel env.globals source
    if Environment.Checker.check fuel env ctx true expanded .u64 then
      let normal := Environment.Conversion.normalize env fuel expanded
      if Environment.Checker.check fuel env ctx true normal .u64 then some normal else none
    else none
  else none

def checkIndices (fuel : Nat) (env : Environment) (self : Nat) (ctx : Context) (terms : List Term) :
    Option (List Term) := FamilyEnvironment.mapChecked (checkIndex fuel env self ctx) terms

inductive FieldChecked (env : Environment) (self : Nat) (declaration : Declaration)
    (ctx : Context) : Bool → Term → Field → Prop where
  | ordinary : selfFree self source = true →
      GlobalEnvironment.Expansion env.globals source expanded →
      Environment.Binder env ctx erased expanded sourceSort → Environment.Conversion.Conv env expanded normal →
      Environment.Binder env ctx erased normal normalSort →
      runtimeFieldOK env declaration.data erased normal = true →
      FieldChecked env self declaration ctx erased source ⟨erased, normal, none⟩
  | recursive : count = declaration.arity → indices.length = declaration.arity →
      IndicesChecked env self ctx indices normal → erased = !declaration.data →
      (declaration.data = true → FamilyEnvironment.sameParameters ctx.length declaration.params indices) →
      FieldChecked env self declaration ctx erased (.node (.ind self count) indices)
        ⟨erased, .node (.ind self count) normal, some normal⟩

def checkField (fuel : Nat) (env : Environment) (self : Nat) (declaration : Declaration)
    (ctx : Context) (erased : Bool) (source : Term) : Option Field :=
  match source with
  | .node (.ind family count) indices =>
      if family = self then
        if count = declaration.arity ∧ indices.length = declaration.arity ∧ erased = !declaration.data ∧
            (declaration.data = false ∨ FamilyEnvironment.sameParametersOK ctx.length declaration.params indices = true) then do
          let normal ← checkIndices fuel env self ctx indices
          some ⟨erased, .node (.ind self count) normal, some normal⟩
        else none
      else ordinary
  | _ => ordinary
where ordinary : Option Field := do
  if selfFree self source then
    let expanded ← GlobalEnvironment.expand fuel env.globals source
    let _ ← Environment.Checker.binder fuel env ctx erased expanded
    let normal := Environment.Conversion.normalize env fuel expanded
    let _ ← Environment.Checker.binder fuel env ctx erased normal
    if runtimeFieldOK env declaration.data erased normal then some ⟨erased, normal, none⟩ else none
  else none

inductive TelescopeChecked (env : Environment) (self : Nat) (declaration : Declaration) :
    List Field → Term → Signature → Prop where
  | field : FieldChecked env self declaration (fieldContext fields) erased domain field →
      TelescopeChecked env self declaration (fields ++ [field]) rest signature →
      TelescopeChecked env self declaration fields (.pi erased domain rest) signature
  | result : count = declaration.arity → indices.length = declaration.arity →
      IndicesChecked env self (fieldContext fields) indices normal →
      FamilyEnvironment.Parameters fields declaration.params indices →
      TelescopeChecked env self declaration fields (.node (.ind self count) indices) ⟨fields, normal⟩

def checkTelescope : Nat → Environment → Nat → Declaration → List Field → Term → Option Signature
  | 0, _, _, _, _, _ => none
  | fuel + 1, env, self, declaration, fields, source =>
      match source with
      | .pi erased domain rest => do
          let field ← checkField fuel env self declaration (fieldContext fields) erased domain
          checkTelescope fuel env self declaration (fields ++ [field]) rest
      | .node (.ind family count) indices =>
          if family = self ∧ count = declaration.arity ∧ indices.length = declaration.arity ∧
              FamilyEnvironment.parametersOK fields declaration.params indices = true then do
            let normal ← checkIndices fuel env self (fieldContext fields) indices
            some ⟨fields, normal⟩
          else none
      | _ => none

structure FamilyChecked (env : Environment) (source : Declaration) (entry : CheckedFamily) : Prop where
  metadata : FamilyEnvironment.Metadata env.globals source
  declaration : entry.declaration = source
  signatures : FamilyEnvironment.RelList (TelescopeChecked env env.families.size source [])
    source.constructors entry.signatures
  layout : entry.boxed = (FamilyEnvironment.heapLayout env.families entry.signatures && source.data)
  compatible : ¬(FamilyEnvironment.heapLayout env.families entry.signatures = true ∧
    FamilyEnvironment.flatLayout env.families entry.signatures = true)

def checkFamily (fuel : Nat) (env : Environment) (source : Declaration) : Option CheckedFamily := do
  if source.globals = env.globals.size ∧ source.arity ≤ 16 ∧ source.params ≤ source.arity ∧
      (source.data = true ∨ source.params = 0) then
    let signatures ← FamilyEnvironment.mapChecked (checkTelescope fuel env env.families.size source []) source.constructors
    if FamilyEnvironment.heapLayout env.families signatures && FamilyEnvironment.flatLayout env.families signatures
    then none else some ⟨source, signatures, FamilyEnvironment.heapLayout env.families signatures && source.data⟩
  else none

private theorem mapChecked_sound {f : α → Option β} {R : α → β → Prop}
    (sound : ∀ x y, f x = some y → R x y)
    (h : FamilyEnvironment.mapChecked f xs = some ys) : FamilyEnvironment.RelList R xs ys := by
  induction xs generalizing ys with
  | nil => simp only [FamilyEnvironment.mapChecked, Option.some.injEq] at h; subst ys; exact .nil
  | cons x xs ih =>
      simp only [FamilyEnvironment.mapChecked] at h
      cases head : f x with
      | none => simp [head] at h
      | some y =>
          simp only [head, Bind.bind, Option.bind] at h
          cases tail : FamilyEnvironment.mapChecked f xs with
          | none => simp [tail] at h
          | some rest =>
              simp only [tail] at h
              cases h
              exact .cons (sound _ _ head) (ih tail)

theorem checkIndex_sound (h : checkIndex fuel env self ctx source = some normal) :
    IndexChecked env self ctx source normal := by
  unfold checkIndex at h
  split at h
  · rename_i free
    cases expanded : GlobalEnvironment.expand fuel env.globals source with
    | none => simp [expanded] at h
    | some term =>
        simp only [expanded, Bind.bind, Option.bind] at h
        split at h
        · rename_i sourceTyped
          split at h
          · rename_i normalTyped
            cases h
            exact ⟨free, term, GlobalEnvironment.expand_sound expanded,
              Environment.Checker.check_sound sourceTyped, Environment.Conversion.normalize_sound env fuel term,
              Environment.Checker.check_sound normalTyped⟩
          · contradiction
        · contradiction
  · contradiction

theorem checkIndices_sound (h : checkIndices fuel env self ctx source = some normal) :
    IndicesChecked env self ctx source normal :=
  mapChecked_sound (fun _ _ h => checkIndex_sound h) h

private theorem ordinary_sound
    (h : checkField.ordinary fuel env self declaration ctx erased source = some field) :
    FieldChecked env self declaration ctx erased source field := by
  unfold checkField.ordinary at h
  split at h
  · rename_i free
    cases expanded : GlobalEnvironment.expand fuel env.globals source with
    | none => simp [expanded] at h
    | some term =>
        simp only [expanded, Bind.bind, Option.bind] at h
        cases sourceBound : Environment.Checker.binder fuel env ctx erased term with
        | none => simp [sourceBound] at h
        | some sourceSort =>
            simp only [sourceBound] at h
            cases normalBound : Environment.Checker.binder fuel env ctx erased (Environment.Conversion.normalize env fuel term) with
            | none => simp [normalBound] at h
            | some normalSort =>
                simp only [normalBound] at h
                split at h
                · rename_i runtime
                  cases h
                  exact .ordinary free (GlobalEnvironment.expand_sound expanded)
                    (Environment.Checker.binder_sound sourceBound) (Environment.Conversion.normalize_sound env fuel term)
                    (Environment.Checker.binder_sound normalBound) runtime
                · contradiction
  · contradiction

theorem checkField_sound (h : checkField fuel env self declaration ctx erased source = some field) :
    FieldChecked env self declaration ctx erased source field := by
  unfold checkField at h
  split at h
  · rename_i family count indices
    split at h
    · rename_i same
      subst family
      split at h
      · rename_i checks
        obtain ⟨count, size, erasedPolicy, params⟩ := checks
        cases checked : checkIndices fuel env self ctx indices with
        | none => simp [checked] at h
        | some normal =>
            simp only [checked, Bind.bind, Option.bind, Option.some.injEq] at h
            subst field
            apply FieldChecked.recursive count size (checkIndices_sound checked) erasedPolicy
            intro data
            rcases params with prop | params
            · simp [data] at prop
            · exact FamilyEnvironment.sameParametersOK_sound params
      · contradiction
    · exact ordinary_sound h
  · exact ordinary_sound h

theorem checkTelescope_sound
    (h : checkTelescope fuel env self declaration fields source = some signature) :
    TelescopeChecked env self declaration fields source signature := by
  induction fuel generalizing fields source signature with
  | zero => simp [checkTelescope] at h
  | succ fuel ih =>
      simp only [checkTelescope] at h
      split at h
      · rename_i erased domain rest
        cases checked : checkField fuel env self declaration (fieldContext fields) erased domain with
        | none => simp [checked] at h
        | some field =>
            simp only [checked, Bind.bind, Option.bind] at h
            exact .field (checkField_sound checked) (ih h)
      · rename_i family count indices
        split at h
        · rename_i checks
          obtain ⟨rfl, count, size, params⟩ := checks
          cases checked : checkIndices fuel env family (fieldContext fields) indices with
          | none => simp [checked] at h
          | some normal =>
              simp only [checked, Bind.bind, Option.bind, Option.some.injEq] at h
              subst signature
              exact .result count size (checkIndices_sound checked) (FamilyEnvironment.parametersOK_sound params)
        · contradiction
      · contradiction

theorem checkFamily_sound (h : checkFamily fuel env source = some entry) : FamilyChecked env source entry := by
  unfold checkFamily at h
  split at h
  · rename_i metadata
    cases checked : FamilyEnvironment.mapChecked (checkTelescope fuel env env.families.size source []) source.constructors with
    | none => simp [checked] at h
    | some signatures =>
        simp only [checked, Bind.bind, Option.bind] at h
        split at h
        · contradiction
        · rename_i compatible
          cases h
          refine ⟨metadata, rfl, mapChecked_sound (fun _ _ h => checkTelescope_sound h) checked, rfl, ?_⟩
          simpa only [Bool.and_eq_true] using compatible
  · contradiction

def FieldsScoped (fields : List Field) : Prop :=
  ∀ (j : Nat) field, fields[j]? = some field → field.domain.Scoped j ∧
    ∀ indices, field.recursive = some indices → ∀ index ∈ indices, index.Scoped j

theorem FieldsScoped.empty : FieldsScoped [] := by
  intro j field found
  simp at found

theorem FieldsScoped.append (prior : FieldsScoped fields)
    (domain : field.domain.Scoped fields.length)
    (recursive : ∀ indices, field.recursive = some indices → ∀ index ∈ indices, index.Scoped fields.length) :
    FieldsScoped (fields ++ [field]) := by
  intro j selected found
  by_cases earlier : j < fields.length
  · rw [List.getElem?_append_left earlier] at found
    exact prior j selected found
  · have later : fields.length ≤ j := by omega
    rw [List.getElem?_append_right later] at found
    cases difference : j - fields.length with
    | zero =>
        simp only [difference, List.getElem?_cons_zero, Option.some.injEq] at found
        subst selected
        have same : j = fields.length := by omega
        subst j
        exact ⟨domain, recursive⟩
    | succ k => simp [difference] at found

theorem IndexChecked.normal_typed (checked : IndexChecked env self ctx source normal) :
    Environment.HasType env ctx true normal .u64 := by
  obtain ⟨_, _, _, _, _, typed⟩ := checked
  exact typed

theorem IndicesChecked.normal_typed (checked : IndicesChecked env self ctx source normal) :
    ∀ index ∈ normal, Environment.HasType env ctx true index .u64 := by
  induction checked with
  | nil => simp
  | cons head tail ih =>
      simpa only [List.mem_cons, forall_eq_or_imp] using And.intro head.normal_typed ih

theorem IndicesChecked.source_selfFree (checked : IndicesChecked env self ctx source normal) :
    selfFreeArgs self source = true := by
  induction checked with
  | nil => simp only [selfFreeArgs]
  | cons head tail ih =>
      simp only [selfFreeArgs]
      exact Bool.and_eq_true_iff.mpr ⟨head.1, ih⟩

theorem FieldChecked.stored_scoped (checked : FieldChecked env self declaration ctx erased source field) :
    field.domain.Scoped ctx.length ∧
      ∀ indices, field.recursive = some indices → ∀ index ∈ indices, index.Scoped ctx.length := by
  cases checked with
  | ordinary _ _ _ _ formed _ =>
      cases formed with
      | intro typed _ => exact ⟨typed.term_scoped, by intro indices impossible; cases impossible⟩
  | recursive _ _ indices _ _ =>
      constructor
      · apply Term.Scoped.node
        intro i term found
        change term.Scoped ctx.length
        exact (indices.normal_typed term (List.mem_of_getElem? found)).term_scoped
      · intro normal same term member
        cases same
        exact (indices.normal_typed term member).term_scoped

theorem TelescopeChecked.signature_scoped
    (checked : TelescopeChecked env self declaration fields source signature) :
    FieldsScoped fields → SignatureScoped signature := by
  induction checked with
  | field formed rest ih =>
      intro prior
      have scopeProof := formed.stored_scoped
      simp only [FamilyEnvironment.fieldContext_length] at scopeProof
      exact ih (prior.append scopeProof.1 scopeProof.2)
  | result _ _ indices _ =>
      intro prior
      refine ⟨fun j field found => (prior j field found).1,
        fun j field normal found same => (prior j field found).2 normal same, ?_⟩
      intro term member
      simpa only [FamilyEnvironment.fieldContext_length] using (indices.normal_typed term member).term_scoped

theorem FamilyChecked.signatures_scoped (checked : FamilyChecked env source entry) :
    ∀ signature ∈ entry.signatures, SignatureScoped signature := by
  intro signature member
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨term, _, telescope⟩ := checked.signatures.right found
  exact telescope.signature_scoped FieldsScoped.empty

/-- Positivity is checked on the original source Pi/Ind structure. -/
inductive Positive (self : Nat) : Term → Prop where
  | result : selfFreeArgs self indices = true → Positive self (.node (.ind self count) indices)
  | ordinary : selfFree self domain = true → Positive self rest → Positive self (.pi erased domain rest)
  | recursive : selfFreeArgs self indices = true → Positive self rest →
      Positive self (.pi erased (.node (.ind self count) indices) rest)

theorem TelescopeChecked.positive (checked : TelescopeChecked env self declaration fields source signature) :
    Positive self source := by
  induction checked with
  | field formed rest ih =>
      cases formed with
      | ordinary free _ _ _ _ _ => exact .ordinary free ih
      | recursive _ _ indices _ _ => exact .recursive indices.source_selfFree ih
  | result _ _ indices _ => exact .result indices.source_selfFree

theorem FamilyChecked.constructors_positive (checked : FamilyChecked env source entry) :
    ∀ term ∈ source.constructors, Positive env.families.size term := by
  intro term member
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨_, _, telescope⟩ := checked.signatures.left found
  exact telescope.positive

end Jihoo.NativeKernel.UnifiedProgram.Families
