import Jihoo.QuantityAliases

/-! Quantity projection from checked, normalized binder-domain classifications.
This module does not prove that Core.check/normal produce these classifications.
The test driver obtains them from actual checked lambda annotations. Formation,
normalization, family classification and type-argument admissibility remain the
trusted implementation/specification boundary, not caller-chosen mode flags. -/
namespace Jihoo.Quantity.Binders

/-- A summary of a formed, normalized domain. `proof` means its inferred sort
is Prop; `other` includes functions, universes and neutral type expressions.
These summaries alone do not prove unrestricted values cannot contain owners. -/
inductive Domain where
  | proof | index | scalar | flatData | boxedData | buffer | back | borrow | other
  deriving DecidableEq, Repr

structure Capability where
  mode : BinderMode
  lendable : Bool
  deriving DecidableEq, Repr

/-- Match the specified binder erasure restrictions before classifying runtime
ownership. In particular, erased boxed data is not a runtime owner and Back is
linear but cannot be lent. -/
def classify (erased : Bool) : Domain → Option Capability
  | .proof => if erased then some ⟨.erased, false⟩ else none
  | .index | .flatData => some ⟨if erased then .erased else .unrestricted, false⟩
  | .boxedData => some ⟨if erased then .erased else .linear, !erased⟩
  | .buffer => if erased then none else some ⟨.linear, true⟩
  | .back => if erased then none else some ⟨.linear, false⟩
  | .borrow => if erased then none else some ⟨.borrowed, false⟩
  | .scalar | .other => if erased then none else some ⟨.unrestricted, false⟩

/-- Declarative binder permission, independently stated as cases of the spec. -/
inductive Permitted : Bool → Domain → Capability → Prop where
  | proof : Permitted true .proof ⟨.erased, false⟩
  | erasedIndex : Permitted true .index ⟨.erased, false⟩
  | erasedFlat : Permitted true .flatData ⟨.erased, false⟩
  | erasedBoxed : Permitted true .boxedData ⟨.erased, false⟩
  | index : Permitted false .index ⟨.unrestricted, false⟩
  | scalar : Permitted false .scalar ⟨.unrestricted, false⟩
  | flat : Permitted false .flatData ⟨.unrestricted, false⟩
  | boxed : Permitted false .boxedData ⟨.linear, true⟩
  | buffer : Permitted false .buffer ⟨.linear, true⟩
  | back : Permitted false .back ⟨.linear, false⟩
  | borrow : Permitted false .borrow ⟨.borrowed, false⟩
  | other : Permitted false .other ⟨.unrestricted, false⟩

theorem classify_sound (h : classify erased domain = some capability) :
    Permitted erased domain capability := by
  cases domain <;> cases erased <;> simp_all [classify] <;> cases h <;> constructor

theorem classify_complete (h : Permitted erased domain capability) :
    classify erased domain = some capability := by cases h <;> rfl

theorem lendable_iff (h : classify erased domain = some capability) :
    capability.lendable = true ↔ erased = false ∧ (domain = .buffer ∨ domain = .boxedData) := by
  cases classify_sound h <;> simp

theorem lendable_linear (h : classify erased domain = some capability)
    (hl : capability.lendable = true) : capability.mode = .linear := by
  cases classify_sound h <;> simp_all

structure Binding where
  erased : Bool
  domain : Domain
  deriving DecidableEq, Repr

/-- The consumer cannot request a mode different from the domain's capability. -/
def projectScope (binding : Binding) (body : Control) : Option Control := do
  let capability ← classify binding.erased binding.domain
  pure (.scope capability.mode body)

theorem projectScope_origin (h : projectScope binding body = some projected) :
    ∃ capability, Permitted binding.erased binding.domain capability ∧
      projected = .scope capability.mode body := by
  unfold projectScope at h
  cases hc : classify binding.erased binding.domain <;> simp_all
  exact ⟨_, classify_sound hc, h.symm⟩

/-- A telescope is projected from the actual binding descriptors; no mode
vector is accepted from its consumer. -/
def capabilities (bindings : List Binding) : Option (List Capability) :=
  bindings.mapM fun b => classify b.erased b.domain

inductive PermittedBindings : List Binding → List Capability → Prop where
  | nil : PermittedBindings [] []
  | cons : Permitted b.erased b.domain c → PermittedBindings bs cs →
      PermittedBindings (b :: bs) (c :: cs)

theorem PermittedBindings.length_eq (h : PermittedBindings bs cs) : bs.length = cs.length := by
  induction h <;> simp_all

theorem capabilities_origin (h : capabilities bindings = some caps) :
    PermittedBindings bindings caps := by
  induction bindings generalizing caps with
  | nil => simp [capabilities] at h; subst caps; exact .nil
  | cons b bs ih =>
      simp only [capabilities, List.mapM_cons] at h
      cases hc : classify b.erased b.domain with
      | none => simp [hc] at h
      | some c =>
          cases ht : capabilities bs with
          | none => simp only [capabilities] at ht; simp [hc, ht] at h
          | some cs =>
              have tail := ih ht
              simp only [capabilities] at ht
              simp [hc, ht] at h
              subst caps
              exact .cons (classify_sound hc) tail

def projectTelescope (bindings : List Binding) (body : Control) : Option Control := do
  let caps ← capabilities bindings
  pure (.scopes (caps.map Capability.mode) body)

theorem projectTelescope_origin (h : projectTelescope bindings body = some projected) :
    ∃ caps, PermittedBindings bindings caps ∧
      projected = .scopes (caps.map Capability.mode) body := by
  unfold projectTelescope at h
  cases hc : capabilities bindings <;> simp_all
  exact ⟨_, capabilities_origin hc, h.symm⟩

theorem projected_telescope_outer
    (h : projectTelescope bindings body = some projected)
    (checked : projected.demand r = some n) : body.demand (r + bindings.length) = some n := by
  obtain ⟨caps, formed, rfl⟩ := projectTelescope_origin h
  have ho := scopes_outer checked
  simpa [formed.length_eq] using ho

/-- A returned-owner alias must refer to an existing runtime owned binding.
Context entries must be authentic checked-domain summaries; this function does
not authenticate a supplied context or establish a borrow lease. -/
def projectAlias (context : List Binding) (owner : Nat) (body : Control) : Option Control := do
  let _ ← capabilities context
  let binding ← context[owner]?
  let capability ← classify binding.erased binding.domain
  if capability.lendable then some (.alias owner body) else none

theorem projectAlias_context (h : projectAlias context owner body = some projected) :
    ∃ caps, PermittedBindings context caps := by
  unfold projectAlias at h
  cases hc : capabilities context <;> simp_all
  exact ⟨_, capabilities_origin hc⟩

theorem projectAlias_origin (h : projectAlias context owner body = some projected) :
    ∃ binding, context[owner]? = some binding ∧ binding.erased = false ∧
      (binding.domain = .buffer ∨ binding.domain = .boxedData) ∧
      projected = .alias owner body := by
  unfold projectAlias at h
  cases hctx : capabilities context <;> simp_all
  cases hb : context[owner]? <;> simp_all
  case some binding =>
    cases hc : classify binding.erased binding.domain <;> simp_all
    case some capability =>
      exact (lendable_iff hc).mp h.1

theorem projected_alias_finished (h : projectAlias context owner body = some projected)
    (checked : projected.demand r = some n) (run : Finishes body xs) :
    (xs.map (openOwner owner)).count r = n := by
  obtain ⟨_, _, _, _, rfl⟩ := projectAlias_origin h
  exact alias_finished checked run

theorem projected_alias_prefix (h : projectAlias context owner body = some projected)
    (checked : projected.demand r = some n) (run : Prefix body xs) :
    (xs.map (openOwner owner)).count r ≤ n := by
  obtain ⟨_, _, _, _, rfl⟩ := projectAlias_origin h
  exact alias_prefix checked run

-- Linear is necessary, not sufficient, for a lend: Back is the counterexample.
example : classify false .back = some ⟨.linear, false⟩ := rfl
example : projectAlias [⟨false, .back⟩] 0 (.use 0) = none := rfl
example : projectAlias [⟨true, .boxedData⟩] 0 (.use 0) = none := rfl
example : projectAlias [⟨false, .borrow⟩] 0 (.use 0) = none := rfl
example : projectAlias [⟨false, .buffer⟩] 1 (.use 0) = none := rfl
example : projectAlias [⟨false, .buffer⟩] 0 (.branch (.use 0) (.use 1)) =
    some (.alias 0 (.branch (.use 0) (.use 1))) := rfl

-- An invalid unselected binding still rejects the complete context.
example : projectAlias [⟨false, .buffer⟩, ⟨true, .buffer⟩] 0 (.use 0) = none := rfl
example : projectAlias [⟨false, .scalar⟩, ⟨false, .buffer⟩] 0 (.use 0) = none := rfl
example : projectTelescope [⟨false, .index⟩, ⟨true, .proof⟩, ⟨false, .buffer⟩]
    (.seq (.use 0) (.use 3)) = some
      (.scopes [.unrestricted, .erased, .linear] (.seq (.use 0) (.use 3))) := rfl
example : projectTelescope [⟨true, .buffer⟩] .pure = none := rfl

/-- Test-only enumeration for comparison with actual checked-Core observations. -/
def domains : List Domain := [.proof, .index, .scalar, .flatData, .boxedData,
  .buffer, .back, .borrow, .other]

def modeCode : BinderMode → Nat
  | .erased => 0 | .linear => 1 | .unrestricted => 2 | .borrowed => 3

end Jihoo.Quantity.Binders
