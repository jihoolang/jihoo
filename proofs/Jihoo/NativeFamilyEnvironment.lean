import Jihoo.NativeGlobalEnvironment
import Jihoo.NativePreservation

/-! Independently checked constructor telescopes on the complete native syntax.
The scan examines the source Pi/Ind structure before normalization, permits
self-reference only as an entire recursive field or final result, and derives
field signatures and storage layout. This first stage checks ordinary domains
with the pure native judgment; earlier-family fields and buffers conservatively
reject until a family-aware term judgment is available. -/
namespace Jihoo.NativeKernel.FamilyEnvironment

abbrev Declaration := Jihoo.NativeKernel.Environment.FamilyDeclaration
abbrev Field := Jihoo.NativeKernel.Environment.Field
abbrev Signature := Jihoo.NativeKernel.Environment.Signature
abbrev CheckedFamily := Jihoo.NativeKernel.Environment.CheckedFamily

abbrev Environment := Array CheckedFamily

/-- Domains use the preceding fields in newest-first de Bruijn order. -/
def fieldContext (fields : List Field) : Context :=
  fields.reverse.map fun field => ⟨field.domain, field.erased⟩

@[simp] theorem fieldContext_length : (fieldContext fields).length = fields.length := by
  simp [fieldContext]

@[simp] theorem fieldContext_append (fields : List Field) (field : Field) :
    fieldContext (fields ++ [field]) = ⟨field.domain, field.erased⟩ :: fieldContext fields := by
  simp [fieldContext]

def isInd : Op → Bool
  | .ind _ _ => true
  | _ => false

/-- Literal family occurrences, including occurrences hidden under binders,
are excluded from ordinary checked domains and index expressions. -/
def IndFree : Term → Prop
  | .var _ => True
  | .node op args => isInd op = false ∧ ∀ t ∈ args, IndFree t

theorem hasType_indFree (h : HasType ctx mode t T) : IndFree t := by
  induction h using HasType.rec (motive_1 := fun _ _ A _ _ => IndFree A) <;>
    simp_all [IndFree, isInd]

theorem binder_indFree (h : Binder ctx e A s) : IndFree A := by
  cases h with
  | intro formed allowed => exact hasType_indFree formed

theorem expansion_indFree_source
    (h : GlobalEnvironment.Expansion globals t u) (hu : IndFree u) : IndFree t := by
  induction h using GlobalEnvironment.Expansion.rec
    (motive_2 := fun xs ys _ => (∀ u ∈ ys, IndFree u) → ∀ t ∈ xs, IndFree t) with
  | var => trivial
  | global => simp [IndFree, isInd]
  | node op _ _ ih =>
      simp only [IndFree] at hu ⊢
      exact ⟨hu.1, ih hu.2⟩
  | nil => rename_i free t member; cases member
  | cons _ _ ih ihts =>
      rename_i free t member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ih (free _ (by simp))
      · exact ihts (fun u hu => free u (by simp [hu])) t member

/-- Each source index is expanded only through a checked global prefix and
checked as U64; the stored index retains typing and genuine conversion. -/
inductive RelList {α : Type u} {β : Type v} (R : α → β → Prop) : List α → List β → Prop where
  | nil : RelList R [] []
  | cons : R a b → RelList R xs ys → RelList R (a :: xs) (b :: ys)

def IndexChecked (globals : GlobalEnvironment.Environment) (ctx : Context)
    (source normal : Term) : Prop :=
  ∃ expanded, GlobalEnvironment.Expansion globals source expanded ∧
    HasType ctx true expanded .u64 ∧ Conversion.Conv expanded normal ∧
    HasType ctx true normal .u64

abbrev IndicesChecked (globals : GlobalEnvironment.Environment) (ctx : Context) :=
  RelList (IndexChecked globals ctx)

def checkIndex (fuel : Nat) (globals : GlobalEnvironment.Environment) (ctx : Context)
    (source : Term) : Option Term := do
  let expanded ← GlobalEnvironment.expand fuel globals source
  if Checker.check fuel ctx true expanded .u64 then
    some (Conversion.normalize fuel expanded)
  else none

def mapChecked (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => do
      let y ← f x
      let ys ← mapChecked f xs
      pure (y :: ys)

def checkIndices (fuel : Nat) (globals : GlobalEnvironment.Environment) (ctx : Context)
    (xs : List Term) : Option (List Term) := mapChecked (checkIndex fuel globals ctx) xs

/-- Parameters repeat their literal de Bruijn variables, before normalization. -/
def sameParameters (depth params : Nat) (xs : List Term) : Prop :=
  params ≤ depth ∧ ∀ j < params, xs[j]? = some (.var (depth - 1 - j))

def sameParametersOK (depth params : Nat) (xs : List Term) : Bool :=
  decide (params ≤ depth) &&
    (List.range params).all fun j => decide (xs[j]? = some (.var (depth - 1 - j)))

/-- Parameters must be the first erased, nonrecursive U64 fields and be
returned unchanged in the constructor result, as written. -/
def Parameters (fields : List Field) (params : Nat) (xs : List Term) : Prop :=
  ∀ j < params, ∃ field, fields[j]? = some field ∧ field.erased = true ∧
    field.recursive = none ∧ field.domain = .u64 ∧ xs[j]? = some (.var (fields.length - 1 - j))

def parametersOK (fields : List Field) (params : Nat) (xs : List Term) : Bool :=
  (List.range params).all fun j =>
    match fields[j]?, xs[j]? with
    | some field, some (.var n) => field.erased && field.recursive.isNone &&
        decide (field.domain = .u64) && decide (n = fields.length - 1 - j)
    | _, _ => false

/-- The accepted ordinary runtime fields have exactly the native first-order
scalar/refinement shapes. Memory and earlier-family fields are later stages. -/
def RuntimeFieldAllowed (data erased : Bool) (domain : Term) : Prop :=
  erased = true ∨
    if data then domain = .u64 ∨ domain = .i64 ∨ ∃ p, domain = .refine p
    else domain = .u64

def runtimeFieldOK (data erased : Bool) (domain : Term) : Bool :=
  erased || match domain with
    | .u64 => true
    | .i64 | .refine _ => data
    | _ => false

/-- Independent signature-field validation. The current family is not made a
formation axiom: its only special occurrence is the entire recursive domain. -/
inductive FieldChecked (globals : GlobalEnvironment.Environment) (self : Nat)
    (declaration : Declaration) (ctx : Context) : Bool → Term → Field → Prop where
  | ordinary : GlobalEnvironment.Expansion globals source expanded →
      Binder ctx erased expanded sort → Conversion.Conv expanded normal →
      Binder ctx erased normal sort → RuntimeFieldAllowed declaration.data erased normal →
      FieldChecked globals self declaration ctx erased source ⟨erased, normal, none⟩
  | recursive : count = declaration.arity → xs.length = declaration.arity →
      IndicesChecked globals ctx xs normal → erased = !declaration.data →
      (declaration.data = true → sameParameters ctx.length declaration.params xs) →
      FieldChecked globals self declaration ctx erased (.node (.ind self count) xs)
        ⟨erased, .node (.ind self count) normal, some normal⟩

def checkField (fuel : Nat) (globals : GlobalEnvironment.Environment) (self : Nat)
    (declaration : Declaration) (ctx : Context) (erased : Bool) (source : Term) : Option Field :=
  match source with
  | .node (.ind family count) xs =>
      if family = self then
        if count = declaration.arity ∧ xs.length = declaration.arity ∧ erased = !declaration.data ∧
            (declaration.data = false ∨ sameParametersOK ctx.length declaration.params xs = true) then do
          let normal ← checkIndices fuel globals ctx xs
          some ⟨erased, .node (.ind self count) normal, some normal⟩
        else none
      else ordinary
  | _ => ordinary
where ordinary : Option Field := do
  let expanded ← GlobalEnvironment.expand fuel globals source
  let _sort ← Checker.binder fuel ctx erased expanded
  let normal := Conversion.normalize fuel expanded
  if runtimeFieldOK declaration.data erased normal then some ⟨erased, normal, none⟩ else none

/-- Scan exactly the original telescope structure. Normalizing a term into Pi
or Ind does not make it a constructor declaration. -/
inductive TelescopeChecked (globals : GlobalEnvironment.Environment) (self : Nat)
    (declaration : Declaration) : List Field → Term → Signature → Prop where
  | field : FieldChecked globals self declaration (fieldContext fields) erased domain field →
      TelescopeChecked globals self declaration (fields ++ [field]) rest signature →
      TelescopeChecked globals self declaration fields (.pi erased domain rest) signature
  | result : count = declaration.arity → xs.length = declaration.arity →
      IndicesChecked globals (fieldContext fields) xs normal → Parameters fields declaration.params xs →
      TelescopeChecked globals self declaration fields (.node (.ind self count) xs) ⟨fields, normal⟩

def checkTelescope : Nat → GlobalEnvironment.Environment → Nat → Declaration → List Field → Term → Option Signature
  | 0, _, _, _, _, _ => none
  | fuel + 1, globals, self, declaration, fields, source =>
      match source with
      | .pi erased domain rest => do
          let field ← checkField fuel globals self declaration (fieldContext fields) erased domain
          checkTelescope fuel globals self declaration (fields ++ [field]) rest
      | .node (.ind family count) xs =>
          if family = self ∧ count = declaration.arity ∧ xs.length = declaration.arity ∧
              parametersOK fields declaration.params xs = true then do
            let normal ← checkIndices fuel globals (fieldContext fields) xs
            some ⟨fields, normal⟩
          else none
      | _ => none

/-- Native storage classification is derived from checked fields. -/
def heapField (earlier : Environment) (field : Field) : Bool :=
  !field.erased && (field.recursive.isSome || match field.domain with
    | .node .buffer [_] => true
    | .node (.ind family _) _ => (earlier[family]?).any (·.boxed)
    | _ => false)

def flatField (earlier : Environment) (field : Field) : Bool :=
  !field.erased && field.recursive.isNone && match field.domain with
    | .node (.ind family _) _ => (earlier[family]?).any fun entry => !entry.boxed
    | _ => false

def heapLayout (earlier : Environment) (signatures : List Signature) : Bool :=
  signatures.any fun signature => signature.fields.any (heapField earlier)

def flatLayout (earlier : Environment) (signatures : List Signature) : Bool :=
  signatures.any fun signature => signature.fields.any (flatField earlier)

def Metadata (globals : GlobalEnvironment.Environment) (declaration : Declaration) : Prop :=
  declaration.globals = globals.size ∧ declaration.arity ≤ 16 ∧
    declaration.params ≤ declaration.arity ∧ (declaration.data = true ∨ declaration.params = 0)

structure FamilyChecked (globals : GlobalEnvironment.Environment) (earlier : Environment)
    (source : Declaration) (entry : CheckedFamily) : Prop where
  metadata : Metadata globals source
  declaration : entry.declaration = source
  signatures : RelList (TelescopeChecked globals earlier.size source []) source.constructors entry.signatures
  layout : entry.boxed = (heapLayout earlier entry.signatures && source.data)
  compatible : ¬(heapLayout earlier entry.signatures = true ∧ flatLayout earlier entry.signatures = true)

def checkFamily (fuel : Nat) (globals : GlobalEnvironment.Environment) (earlier : Environment)
    (source : Declaration) : Option CheckedFamily := do
  if source.globals = globals.size ∧ source.arity ≤ 16 ∧ source.params ≤ source.arity ∧
      (source.data = true ∨ source.params = 0) then
    let signatures ← mapChecked (checkTelescope fuel globals earlier.size source []) source.constructors
    if heapLayout earlier signatures && flatLayout earlier signatures then none
    else some ⟨source, signatures, heapLayout earlier signatures && source.data⟩
  else none


private theorem mapChecked_sound {f : α → Option β} {R : α → β → Prop}
    (hf : ∀ x y, f x = some y → R x y)
    (h : mapChecked f xs = some ys) : RelList R xs ys := by
  induction xs generalizing ys with
  | nil => simp only [mapChecked, Option.some.injEq] at h; subst ys; exact .nil
  | cons x xs ih =>
      simp only [mapChecked] at h
      cases hy : f x with
      | none => simp [hy] at h
      | some y =>
          simp only [hy, Bind.bind, Option.bind] at h
          cases hys : mapChecked f xs with
          | none => simp [hys] at h
          | some ys' =>
              simp only [hys] at h
              cases h
              exact .cons (hf _ _ hy) (ih hys)

theorem checkIndex_sound (h : checkIndex fuel globals ctx source = some normal) :
    IndexChecked globals ctx source normal := by
  unfold checkIndex at h
  cases he : GlobalEnvironment.expand fuel globals source with
  | none => simp [he] at h
  | some expanded =>
      simp only [he, Bind.bind, Option.bind] at h
      split at h
      · rename_i checked
        cases h
        have typed := Checker.check_sound checked
        exact ⟨expanded, GlobalEnvironment.expand_sound he, typed,
          Conversion.normalize_sound _ _, typed.ghostNormalize _⟩
      · contradiction

theorem checkIndices_sound (h : checkIndices fuel globals ctx xs = some normal) :
    IndicesChecked globals ctx xs normal :=
  mapChecked_sound (fun _ _ h => checkIndex_sound h) h

theorem sameParametersOK_sound (h : sameParametersOK depth params xs = true) :
    sameParameters depth params xs := by
  obtain ⟨bound, vars⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨of_decide_eq_true bound, ?_⟩
  intro j hj
  exact of_decide_eq_true (List.all_eq_true.mp vars j (List.mem_range.mpr hj))

theorem parametersOK_sound (h : parametersOK fields params xs = true) :
    Parameters fields params xs := by
  intro j hj
  have one := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  split at one
  · rename_i field n hfield hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at one
    obtain ⟨⟨⟨erased, empty⟩, domain⟩, same⟩ := one
    have recnone : field.recursive = none := by
      cases hr : field.recursive <;> simp_all
    exact ⟨field, hfield, erased, recnone, domain, by simpa only [same] using hx⟩
  · contradiction

theorem runtimeFieldOK_sound (h : runtimeFieldOK data erased domain = true) :
    RuntimeFieldAllowed data erased domain := by
  cases erased with
  | true => exact Or.inl rfl
  | false =>
      apply Or.inr
      simp only [runtimeFieldOK, Bool.false_or] at h
      split at h
      · cases data <;> simp
      · simp [h]
      · simp [h]
      · contradiction

private theorem ordinary_sound
    (h : checkField.ordinary fuel globals declaration ctx erased source = some field) :
    FieldChecked globals self declaration ctx erased source field := by
  unfold checkField.ordinary at h
  cases he : GlobalEnvironment.expand fuel globals source with
  | none => simp [he] at h
  | some expanded =>
      simp only [he, Bind.bind, Option.bind] at h
      cases hb : Checker.binder fuel ctx erased expanded with
      | none => simp [hb] at h
      | some sort =>
          simp only [hb] at h
          split at h
          · rename_i allowed
            cases h
            have binder := Checker.binder_sound hb
            exact .ordinary (GlobalEnvironment.expand_sound he) binder
              (Conversion.normalize_sound _ _) (binder.ghostNormalize _) (runtimeFieldOK_sound allowed)
          · contradiction

theorem checkField_sound (h : checkField fuel globals self declaration ctx erased source = some field) :
    FieldChecked globals self declaration ctx erased source field := by
  unfold checkField at h
  split at h
  · rename_i family count xs
    split at h
    · rename_i same
      subst family
      split at h
      · rename_i checks
        obtain ⟨count, size, erasedPolicy, params⟩ := checks
        cases hn : checkIndices fuel globals ctx xs with
        | none => simp [hn] at h
        | some normal =>
            simp only [hn, Bind.bind, Option.bind, Option.some.injEq] at h
            subst field
            apply FieldChecked.recursive count size (checkIndices_sound hn) erasedPolicy
            intro data
            rcases params with prop | params
            · simp [data] at prop
            · exact sameParametersOK_sound params
      · contradiction
    · exact ordinary_sound h
  · exact ordinary_sound h

theorem checkTelescope_sound
    (h : checkTelescope fuel globals self declaration fields source = some signature) :
    TelescopeChecked globals self declaration fields source signature := by
  induction fuel generalizing fields source signature with
  | zero => simp [checkTelescope] at h
  | succ fuel ih =>
      simp only [checkTelescope] at h
      split at h
      · rename_i erased domain rest
        cases hf : checkField fuel globals self declaration (fieldContext fields) erased domain with
        | none => simp [hf] at h
        | some field =>
            simp only [hf, Bind.bind, Option.bind] at h
            exact .field (checkField_sound hf) (ih h)
      · rename_i family count xs
        split at h
        · rename_i checks
          obtain ⟨rfl, count, size, params⟩ := checks
          cases hn : checkIndices fuel globals (fieldContext fields) xs with
          | none => simp [hn] at h
          | some normal =>
              simp only [hn, Bind.bind, Option.bind, Option.some.injEq] at h
              subst signature
              exact .result count size (checkIndices_sound hn) (parametersOK_sound params)
        · contradiction
      · contradiction

theorem checkFamily_sound
    (h : checkFamily fuel globals earlier source = some entry) : FamilyChecked globals earlier source entry := by
  unfold checkFamily at h
  split at h
  · rename_i metadata
    cases hs : mapChecked (checkTelescope fuel globals earlier.size source []) source.constructors with
    | none => simp [hs] at h
    | some signatures =>
        simp only [hs, Bind.bind, Option.bind] at h
        split at h
        · contradiction
        · rename_i compatible
          cases h
          refine ⟨metadata, rfl, mapChecked_sound (fun _ _ h => checkTelescope_sound h) hs, rfl, ?_⟩
          simpa only [Bool.and_eq_true] using compatible
  · contradiction


/-- Pointwise list evidence preserves vector lengths and indexed positions. -/
theorem RelList.length (h : RelList R xs ys) : xs.length = ys.length := by
  induction h <;> simp_all

theorem RelList.left {α : Type u} {β : Type v} {R : α → β → Prop}
    {xs : List α} {ys : List β} {i : Nat} {x : α} (h : RelList R xs ys) (hx : xs[i]? = some x) :
    ∃ y, ys[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hx
  | @cons a b xs ys head tail ih =>
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst x; exact ⟨b,rfl,head⟩
      | succ i => exact ih hx

theorem RelList.right {α : Type u} {β : Type v} {R : α → β → Prop}
    {xs : List α} {ys : List β} {i : Nat} {y : β} (h : RelList R xs ys) (hy : ys[i]? = some y) :
    ∃ x, xs[i]? = some x ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hy
  | @cons a b xs ys head tail ih =>
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hy; subst y; exact ⟨a,rfl,head⟩
      | succ i => exact ih hy

private theorem conversion_list_left {i : Nat} (h : Conversion.ListRel R xs ys) (hx : xs[i]? = some x) :
    ∃ y, ys[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hx
  | @cons a b xs ys head tail ih =>
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst x; exact ⟨b,rfl,head⟩
      | succ i => exact ih hx

/-- Transparent expansion cannot hide an unbound source variable. -/
theorem expansion_scoped_source (h : GlobalEnvironment.Expansion globals t u) :
    ∀ depth, u.Scoped depth → t.Scoped depth := by
  induction h using GlobalEnvironment.Expansion.rec
    (motive_2 := fun xs ys _ => Conversion.ListRel (fun t u => ∀ depth, u.Scoped depth → t.Scoped depth) xs ys) with
  | var => intro depth h; exact h
  | global => intro depth _; apply Term.Scoped.node; intro i t ht; simp at ht
  | node op _ _ ih =>
      intro depth hu
      cases hu with
      | node children =>
          apply Term.Scoped.node
          intro i t ht
          obtain ⟨u,hu,reflect⟩ := conversion_list_left ih ht
          exact reflect _ (children i u hu)
  | nil => exact .nil
  | cons _ _ ih ihts => exact .cons ih ihts

theorem IndexChecked.source_indFree (h : IndexChecked globals ctx source normal) : IndFree source := by
  obtain ⟨_, expansion, typed, _, _⟩ := h
  exact expansion_indFree_source expansion (hasType_indFree typed)

theorem IndexChecked.normal_indFree (h : IndexChecked globals ctx source normal) : IndFree normal := by
  obtain ⟨_, _, _, _, typed⟩ := h
  exact hasType_indFree typed

theorem IndexChecked.source_scoped (h : IndexChecked globals ctx source normal) : source.Scoped ctx.length := by
  obtain ⟨_, expansion, typed, _, _⟩ := h
  exact expansion_scoped_source expansion _ typed.term_scoped

theorem IndexChecked.normal_typed (h : IndexChecked globals ctx source normal) : HasType ctx true normal .u64 := by
  obtain ⟨_,_,_,_,typed⟩ := h
  exact typed

theorem IndicesChecked.source_indFree (h : IndicesChecked globals ctx source normal) :
    ∀ x ∈ source, IndFree x := by
  induction h with
  | nil => simp
  | cons head tail ih => simpa only [List.mem_cons, forall_eq_or_imp] using And.intro head.source_indFree ih

theorem IndicesChecked.normal_typed (h : IndicesChecked globals ctx source normal) :
    ∀ x ∈ normal, HasType ctx true x .u64 := by
  induction h with
  | nil => simp
  | cons head tail ih => simpa only [List.mem_cons, forall_eq_or_imp] using And.intro head.normal_typed ih

/-- A positive telescope has only complete recursive family domains. A family
beneath an arrow, an argument or another field constructor cannot pass. -/
inductive Positive (self : Nat) : Term → Prop where
  | result : (∀ x ∈ xs, IndFree x) → Positive self (.node (.ind self xs.length) xs)
  | ordinary : IndFree domain → Positive self rest → Positive self (.pi erased domain rest)
  | recursive : (∀ x ∈ xs, IndFree x) → Positive self rest →
      Positive self (.pi erased (.node (.ind self xs.length) xs) rest)

theorem TelescopeChecked.positive (h : TelescopeChecked globals self declaration fields source signature) :
    Positive self source := by
  induction h with
  | field checked rest ih =>
      cases checked with
      | ordinary expansion formed _ _ _ =>
          exact .ordinary (expansion_indFree_source expansion (binder_indFree formed)) ih
      | recursive count size indices _ _ =>
          rw [← size] at count
          subst count
          exact .recursive indices.source_indFree ih
  | result count size indices _ =>
      rw [← size] at count
      subst count
      exact .result indices.source_indFree

/-- Stored ordinary domains are formed types; recursive domains carry fully
typed U64 indices and the native proof/data erasure policy. -/
inductive FieldFormed (self : Nat) (declaration : Declaration) (ctx : Context) : Field → Prop where
  | ordinary : Binder ctx erased domain sort →
      FieldFormed self declaration ctx ⟨erased,domain,none⟩
  | recursive : xs.length = declaration.arity → (∀ x ∈ xs, HasType ctx true x .u64) →
      erased = !declaration.data →
      FieldFormed self declaration ctx ⟨erased,.node (.ind self declaration.arity) xs,some xs⟩

inductive FieldsFormed (self : Nat) (declaration : Declaration) : List Field → Prop where
  | empty : FieldsFormed self declaration []
  | append : FieldsFormed self declaration fields → FieldFormed self declaration (fieldContext fields) field →
      FieldsFormed self declaration (fields ++ [field])

structure SignatureFormed (self : Nat) (declaration : Declaration) (signature : Signature) : Prop where
  fields : FieldsFormed self declaration signature.fields
  arity : signature.result.length = declaration.arity
  result : ∀ x ∈ signature.result, HasType (fieldContext signature.fields) true x .u64

theorem FieldChecked.formed (h : FieldChecked globals self declaration ctx erased source field) :
    FieldFormed self declaration ctx field := by
  cases h with
  | ordinary _ _ _ formed _ => exact .ordinary formed
  | recursive count size indices policy _ =>
      subst count
      exact .recursive (indices.length.symm.trans size) indices.normal_typed policy

theorem TelescopeChecked.formed
    (h : TelescopeChecked globals self declaration fields source signature)
    (prior : FieldsFormed self declaration fields) : SignatureFormed self declaration signature := by
  induction h with
  | field checked rest ih => exact ih (.append prior checked.formed)
  | result count size indices _ =>
      exact ⟨prior,indices.length.symm.trans size,indices.normal_typed⟩

theorem FieldFormed.scoped (h : FieldFormed self declaration ctx field) : field.domain.Scoped ctx.length := by
  cases h with
  | ordinary formed => cases formed with | intro typed _ => exact typed.term_scoped
  | recursive _ indices _ =>
      apply Term.Scoped.node
      intro i t ht
      change t.Scoped (ctx.length + 0)
      exact (indices t (List.mem_of_getElem? ht)).term_scoped

theorem FieldChecked.source_scoped
    (h : FieldChecked globals self declaration ctx erased source field) : source.Scoped ctx.length := by
  cases h with
  | ordinary expansion formed _ _ _ =>
      cases formed with | intro typed _ => exact expansion_scoped_source expansion _ typed.term_scoped
  | recursive _ _ indices _ _ =>
      apply Term.Scoped.node
      intro i t ht
      change t.Scoped (ctx.length + 0)
      obtain ⟨normal,_,checked⟩ := indices.left ht
      exact checked.source_scoped

private theorem pi_scoped (ha : A.Scoped depth) (hb : B.Scoped (depth+1)) :
    (Term.pi erased A B).Scoped depth := by
  apply Term.Scoped.node
  intro i t ht
  cases i with
  | zero => simpa [Op.binders] using (Option.some.inj ht ▸ ha)
  | succ i =>
      cases i with
      | zero => simpa [Op.binders] using (Option.some.inj ht ▸ hb)
      | succ i => simp at ht

theorem TelescopeChecked.scoped
    (h : TelescopeChecked globals self declaration fields source signature) : source.Scoped fields.length := by
  induction h with
  | field checked rest ih =>
      apply pi_scoped
      · simpa only [fieldContext_length] using checked.source_scoped
      · simpa only [List.length_append,List.length_singleton] using ih
  | result _ _ indices _ =>
      apply Term.Scoped.node
      intro i t ht
      obtain ⟨normal,_,checked⟩ := indices.left ht
      simpa only [Op.binders,Nat.add_zero,fieldContext_length] using checked.source_scoped

theorem FamilyChecked.constructors_positive (h : FamilyChecked globals earlier source entry) :
    ∀ t ∈ source.constructors, Positive earlier.size t := by
  intro t ht
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp ht
  obtain ⟨signature,_,checked⟩ := h.signatures.left hi
  exact checked.positive

theorem FamilyChecked.constructors_closed (h : FamilyChecked globals earlier source entry) :
    ∀ t ∈ source.constructors, t.Scoped 0 := by
  intro t ht
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp ht
  obtain ⟨signature,_,checked⟩ := h.signatures.left hi
  exact checked.scoped

theorem FamilyChecked.signatures_formed (h : FamilyChecked globals earlier source entry) :
    ∀ signature ∈ entry.signatures, SignatureFormed earlier.size source signature := by
  intro signature ht
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp ht
  obtain ⟨t,_,checked⟩ := h.signatures.right hi
  exact checked.formed .empty


private theorem conversion_list_length (h : Conversion.ListRel R xs ys) : xs.length = ys.length := by
  induction h <;> simp_all

/-- Graph arity checks cannot be bypassed by transparent global expansion. -/
theorem expansion_wellFormed_source (h : GlobalEnvironment.Expansion globals t u) :
    u.WellFormed → t.WellFormed := by
  induction h using GlobalEnvironment.Expansion.rec
    (motive_2 := fun xs ys _ => Conversion.ListRel (fun t u => u.WellFormed → t.WellFormed) xs ys) with
  | var => intro _; trivial
  | global => intro _; simp [Term.WellFormed,Op.arity]
  | node op _ _ ih =>
      intro hu
      simp only [Term.WellFormed] at hu ⊢
      refine ⟨(conversion_list_length ih).trans hu.1,?_⟩
      intro t ht
      obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp ht
      obtain ⟨u,hu',reflect⟩ := conversion_list_left ih hi
      exact reflect (hu.2 u (List.mem_of_getElem? hu'))
  | nil => exact .nil
  | cons _ _ ih ihts => exact .cons ih ihts

theorem IndexChecked.source_wellFormed (h : IndexChecked globals ctx source normal) : source.WellFormed := by
  obtain ⟨_, expansion, typed, _, _⟩ := h
  exact expansion_wellFormed_source expansion typed.term_wellFormed

theorem FieldChecked.source_wellFormed
    (h : FieldChecked globals self declaration ctx erased source field) : source.WellFormed := by
  cases h with
  | ordinary expansion formed _ _ _ =>
      cases formed with | intro typed _ => exact expansion_wellFormed_source expansion typed.term_wellFormed
  | recursive count size indices _ _ =>
      simp only [Term.WellFormed,Op.arity]
      refine ⟨size.trans count.symm,?_⟩
      intro t ht
      obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp ht
      obtain ⟨normal,_,checked⟩ := indices.left hi
      exact checked.source_wellFormed

theorem TelescopeChecked.wellFormed
    (h : TelescopeChecked globals self declaration fields source signature) : source.WellFormed := by
  induction h with
  | field checked rest ih =>
      simpa [Term.WellFormed,Op.arity] using And.intro checked.source_wellFormed ih
  | result count size indices _ =>
      simp only [Term.WellFormed,Op.arity]
      refine ⟨size.trans count.symm,?_⟩
      intro t ht
      obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp ht
      obtain ⟨normal,_,checked⟩ := indices.left hi
      exact checked.source_wellFormed

theorem FamilyChecked.constructors_wellFormed (h : FamilyChecked globals earlier source entry) :
    ∀ t ∈ source.constructors, t.WellFormed := by
  intro t ht
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp ht
  obtain ⟨signature,_,checked⟩ := h.signatures.left hi
  exact checked.wellFormed

/-- Sequential family checks never consume a caller-supplied signature. -/
inductive SequentiallyChecked (globals : GlobalEnvironment.Environment) : List Declaration → Environment → Prop where
  | empty : SequentiallyChecked globals [] #[]
  | append : SequentiallyChecked globals raw earlier → FamilyChecked globals earlier source entry →
      SequentiallyChecked globals (raw ++ [source]) (earlier.push entry)

def checkFamiliesFrom (fuel : Nat) (globals : GlobalEnvironment.Environment) (earlier : Environment) :
    List Declaration → Option Environment
  | [] => some earlier
  | source :: sources => do
      let entry ← checkFamily fuel globals earlier source
      checkFamiliesFrom fuel globals (earlier.push entry) sources

def checkFamilies (fuel : Nat) (globals : GlobalEnvironment.Environment) (sources : List Declaration) :
    Option Environment := checkFamiliesFrom fuel globals #[] sources

theorem checkFamiliesFrom_sound (history : SequentiallyChecked globals raw earlier)
    (h : checkFamiliesFrom fuel globals earlier sources = some result) :
    SequentiallyChecked globals (raw ++ sources) result := by
  induction sources generalizing raw earlier with
  | nil => simp only [checkFamiliesFrom, Option.some.injEq] at h; subst result; simpa using history
  | cons source sources ih =>
      simp only [checkFamiliesFrom] at h
      cases he : checkFamily fuel globals earlier source with
      | none => simp [he] at h
      | some entry =>
          simp only [he, Bind.bind, Option.bind] at h
          simpa only [List.append_assoc,List.singleton_append] using
            ih (.append history (checkFamily_sound he)) h

theorem checkFamilies_sound (h : checkFamilies fuel globals sources = some result) :
    SequentiallyChecked globals sources result := by
  simpa only [List.nil_append] using checkFamiliesFrom_sound SequentiallyChecked.empty h

abbrev ProgramEnvironment := Jihoo.NativeKernel.Environment

/-- The independent mixed declaration judgment records the actual prefix at
both kinds of admission. Family visibility is checked by FamilyChecked.Metadata. -/
inductive ProgramChecked : List Definitions.Definition → List Declaration → ProgramEnvironment → Prop where
  | empty : ProgramChecked [] [] ⟨#[],#[]⟩
  | definition : ProgramChecked definitions families env →
      GlobalEnvironment.Expansion env.globals source.type expanded.type →
      GlobalEnvironment.Expansion env.globals source.value expanded.value → Definitions.Valid expanded →
      ProgramChecked (definitions ++ [source]) families ⟨env.globals.push expanded,env.families⟩
  | family : ProgramChecked definitions families env → FamilyChecked env.globals env.families source entry →
      ProgramChecked definitions (families ++ [source]) ⟨env.globals,env.families.push entry⟩

inductive Event where
  | definition (source : Definitions.Definition)
  | family (source : Declaration)
  deriving Repr

def eventDefinitions : List Event → List Definitions.Definition
  | [] => []
  | .definition source :: events => source :: eventDefinitions events
  | .family _ :: events => eventDefinitions events

def eventFamilies : List Event → List Declaration
  | [] => []
  | .definition _ :: events => eventFamilies events
  | .family source :: events => source :: eventFamilies events

/-- The family `globals` field places it after exactly that many definitions.
Backward declarations and declarations after the final definition reject. -/
def schedule : Nat → Nat → List Definitions.Definition → List Declaration → Option (List Event)
  | 0, _, _, _ => none
  | fuel + 1, index, definitions, families =>
      match families with
      | source :: families =>
          if source.globals = index then do
            let events ← schedule fuel index definitions families
            some (.family source :: events)
          else if index < source.globals then
            match definitions with
            | [] => none
            | definition :: definitions => do
                let events ← schedule fuel (index+1) definitions (source :: families)
                some (.definition definition :: events)
          else none
      | [] =>
          match definitions with
          | [] => some []
          | source :: definitions => do
              let events ← schedule fuel (index+1) definitions []
              some (.definition source :: events)

def checkEvents (fuel : Nat) (env : ProgramEnvironment) : List Event → Option ProgramEnvironment
  | [] => some env
  | .definition source :: events => do
      let expanded ← GlobalEnvironment.checkDeclaration fuel env.globals source
      checkEvents fuel ⟨env.globals.push expanded,env.families⟩ events
  | .family source :: events => do
      let entry ← checkFamily fuel env.globals env.families source
      checkEvents fuel ⟨env.globals,env.families.push entry⟩ events

def checkProgram (fuel : Nat) (definitions : List Definitions.Definition) (families : List Declaration) :
    Option ProgramEnvironment := do
  let events ← schedule (definitions.length + families.length + 1) 0 definitions families
  checkEvents fuel ⟨#[],#[]⟩ events


theorem schedule_sound
    (h : schedule budget index definitions families = some events) :
    eventDefinitions events = definitions ∧ eventFamilies events = families := by
  induction budget generalizing index definitions families events with
  | zero => simp [schedule] at h
  | succ budget ih =>
      cases families with
      | nil =>
          cases definitions with
          | nil =>
              simp only [schedule,Option.some.injEq] at h
              subst events
              exact ⟨rfl,rfl⟩
          | cons source definitions =>
              simp only [schedule] at h
              cases hs : schedule budget (index+1) definitions [] with
              | none => simp [hs] at h
              | some rest =>
                  simp only [hs,Bind.bind,Option.bind,Option.some.injEq] at h
                  subst events
                  obtain ⟨defs,fams⟩ := ih hs
                  exact ⟨by simp only [eventDefinitions,defs], by simp only [eventFamilies,fams]⟩
      | cons source families =>
          simp only [schedule] at h
          split at h
          · cases hs : schedule budget index definitions families with
            | none => simp [hs] at h
            | some rest =>
                simp only [hs,Bind.bind,Option.bind,Option.some.injEq] at h
                subst events
                obtain ⟨defs,fams⟩ := ih hs
                exact ⟨defs,by simp only [eventFamilies,fams]⟩
          · split at h
            · cases definitions with
              | nil => contradiction
              | cons definition definitions =>
                  simp only at h
                  cases hs : schedule budget (index+1) definitions (source :: families) with
                  | none => simp [hs] at h
                  | some rest =>
                      simp only [hs,Bind.bind,Option.bind,Option.some.injEq] at h
                      subst events
                      obtain ⟨defs,fams⟩ := ih hs
                      exact ⟨by simp only [eventDefinitions,defs],fams⟩
            · contradiction

theorem checkEvents_sound (history : ProgramChecked definitions families env)
    (h : checkEvents fuel env events = some result) :
    ProgramChecked (definitions ++ eventDefinitions events) (families ++ eventFamilies events) result := by
  induction events generalizing definitions families env with
  | nil =>
      simp only [checkEvents,Option.some.injEq] at h
      subst result
      simpa only [eventDefinitions,eventFamilies,List.append_nil] using history
  | cons event events ih =>
      cases event with
      | definition source =>
          simp only [checkEvents] at h
          cases he : GlobalEnvironment.checkDeclaration fuel env.globals source with
          | none => simp [he] at h
          | some expanded =>
              simp only [he,Bind.bind,Option.bind] at h
              obtain ⟨type,value,valid⟩ := GlobalEnvironment.checkDeclaration_sound he
              simpa only [eventDefinitions,eventFamilies,List.append_assoc,List.singleton_append] using
                ih (.definition history type value valid) h
      | family source =>
          simp only [checkEvents] at h
          cases he : checkFamily fuel env.globals env.families source with
          | none => simp [he] at h
          | some entry =>
              simp only [he,Bind.bind,Option.bind] at h
              simpa only [eventDefinitions,eventFamilies,List.append_assoc,List.singleton_append] using
                ih (.family history (checkFamily_sound he)) h

/-- Whole-program acceptance establishes the mixed declaration judgment from
an empty global/family environment, including each family's actual visibility. -/
theorem checkProgram_sound
    (h : checkProgram fuel definitions families = some result) : ProgramChecked definitions families result := by
  unfold checkProgram at h
  cases hs : schedule (definitions.length + families.length + 1) 0 definitions families with
  | none => simp [hs] at h
  | some events =>
      simp only [hs,Bind.bind,Option.bind] at h
      obtain ⟨defs,fams⟩ := schedule_sound hs
      simpa only [List.nil_append,defs,fams] using checkEvents_sound ProgramChecked.empty h

theorem ProgramChecked.globalHistory (h : ProgramChecked definitions families env) :
    GlobalEnvironment.SequentiallyChecked definitions env.globals := by
  induction h with
  | empty => exact .empty
  | definition _ type value valid ih => exact .append ih type value valid
  | family _ _ ih => exact ih

theorem ProgramChecked.familyLength (h : ProgramChecked definitions families env) :
    env.families.size = families.length := by
  induction h <;> simp_all

/-- Every visible family was checked at its own family ID and against a
separately checked global prefix. No external signatures enter this theorem. -/
theorem ProgramChecked.family_prefix (h : ProgramChecked definitions families env)
    {i : Nat} {entry : CheckedFamily} (found : env.families[i]? = some entry) :
    ∃ prefixDefinitions prefixFamilies globals earlier source,
      ProgramChecked prefixDefinitions prefixFamilies ⟨globals,earlier⟩ ∧ earlier.size = i ∧
      FamilyChecked globals earlier source entry := by
  induction h with
  | empty => simp at found
  | definition history _ _ _ ih => exact ih found
  | @family definitions families env source added history checked ih =>
      have inside : i < env.families.size + 1 := by
        obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp found
        simpa only [Array.size_push] using bound
      by_cases earlier : i < env.families.size
      · have old : env.families[i]? = some entry := by
          rw [Array.getElem?_eq_getElem earlier]
          simpa only [Array.getElem?_push_lt earlier] using found
        exact ih old
      · have same : i = env.families.size := by omega
        subst i
        rw [Array.getElem?_push_size] at found
        cases found
        exact ⟨definitions, families, env.globals, env.families, source, history, rfl, checked⟩

theorem ProgramChecked.family_entries (h : ProgramChecked definitions families env)
    {i : Nat} {entry : CheckedFamily} (found : env.families[i]? = some entry) :
    ∃ prefixDefinitions globals earlier source,
      GlobalEnvironment.SequentiallyChecked prefixDefinitions globals ∧ earlier.size = i ∧
      FamilyChecked globals earlier source entry := by
  obtain ⟨definitions,_,globals,earlier,source,history,size,checked⟩ := h.family_prefix found
  exact ⟨definitions,globals,earlier,source,history.globalHistory,size,checked⟩

theorem ProgramChecked.family_safety (h : ProgramChecked definitions families env)
    {i : Nat} {entry : CheckedFamily} (found : env.families[i]? = some entry) :
    ∀ t ∈ entry.declaration.constructors, Positive i t ∧ t.Scoped 0 ∧ t.WellFormed := by
  obtain ⟨_,_,_,source,_,same,checked⟩ := h.family_entries found
  rw [checked.declaration]
  intro t ht
  exact ⟨by simpa only [same] using checked.constructors_positive t ht,
    checked.constructors_closed t ht,checked.constructors_wellFormed t ht⟩

end Jihoo.NativeKernel.FamilyEnvironment
