import Jihoo.NativeEnvironmentConversionNormalizer
import Jihoo.NativeEnvironmentConversionPolicies
import Jihoo.NativeACUInjectivityAPI
import Jihoo.NativeCheckerSoundness

/-! The same native judgment uses genuine environment-indexed ACU and delta
conversion. The bounded implementation proves every comparison through actual
forward equations; environment invariants are required only by metatheory. -/
namespace Jihoo.NativeKernel.Environment.Conversion

abbrev Conv := EnvironmentDelta.Basis.Conv
abbrev ListRel := NativeKernel.Conversion.ListRel
abbrev Closed := EnvironmentDelta.Basis.Closed
abbrev treeSize := NativeKernel.Conversion.treeSize
abbrev treeDepth := NativeKernel.Conversion.treeDepth
abbrev substitutionSafe := NativeKernel.Conversion.substitutionSafe
abbrev normalize? := EnvironmentDelta.Basis.normalize?
abbrev normalize := EnvironmentDelta.Basis.normalize
abbrev equal := EnvironmentDelta.Basis.equal
abbrev normalize?_sound := @EnvironmentDelta.Basis.normalize?_sound
abbrev normalize?_forward := @EnvironmentDelta.Basis.normalize?_forward
abbrev normalize_sound := @EnvironmentDelta.Basis.normalize_sound
abbrev equal_sound := @EnvironmentDelta.Basis.equal_sound

theorem ofLegacy (h : NativeKernel.Conversion.Conv a b) : Conv env a b := .legacy h

end Jihoo.NativeKernel.Environment.Conversion
namespace Jihoo.NativeKernel.Environment

/- Unresolved Global nodes are never treated as plain runtime types. The
checked admission path expands globals; standalone policy checks reject them. -/
mutual
  def globalFree : Term → Bool
    | .var _ => true
    | .node (.global _) _ => false
    | .node _ xs => globalFreeArgs xs
  termination_by t => sizeOf t
  decreasing_by all_goals simp_wf; all_goals omega

  def globalFreeArgs : List Term → Bool
    | [] => true
    | x::xs => globalFree x && globalFreeArgs xs
  termination_by xs => sizeOf xs
  decreasing_by all_goals simp_wf; all_goals omega
end

theorem globalFree_correct (term : Term) : globalFree term = true ↔ GlobalEnvironment.GlobalFree term := by
  induction term using Term.rec
    (motive_2 := fun terms => globalFreeArgs terms = true ↔ ∀ term ∈ terms, GlobalEnvironment.GlobalFree term) with
  | var => simp only [globalFree,GlobalEnvironment.GlobalFree]
  | node op terms children =>
      cases op <;> simp_all [globalFree,GlobalEnvironment.GlobalFree,GlobalEnvironment.ordinary]
  | nil => simp [globalFreeArgs]
  | cons term terms head tail => simp_all [globalFreeArgs,List.mem_cons,Bool.and_eq_true]

def pureBinderAllowed (env : Environment) (erased : Bool) (domain : Term) (sort : SortTag) : Prop :=
  if erased then sort = .prop ∨ Conversion.Conv env domain .u64 else sort ≠ .prop

theorem pureBinderAllowed_ofLegacy (h : NativeKernel.binderAllowed erased domain sort) :
    pureBinderAllowed env erased domain sort := by
  cases erased with
  | false => exact h
  | true => rcases h with hp | hu; exact Or.inl hp; exact Or.inr (.legacy hu)

theorem pureBinderAllowed_renaming (closed : Conversion.Closed env)
    (h : pureBinderAllowed env erased domain sort) (ρ : Nat → Nat) :
    pureBinderAllowed env erased (domain.rename ρ) sort := by
  cases erased with
  | false => exact h
  | true =>
      rcases h with hp | hu
      · exact Or.inl hp
      · exact Or.inr (by simpa only [Term.rename, renameArgs] using hu.renaming ρ closed)

theorem pureBinderAllowed_substitution (closed : Conversion.Closed env)
    (h : pureBinderAllowed env erased domain sort) (σ : Nat → Term) :
    pureBinderAllowed env erased (domain.subst σ) sort := by
  cases erased with
  | false => exact h
  | true =>
      rcases h with hp | hu
      · exact Or.inl hp
      · exact Or.inr (by simpa only [Term.subst, substArgs] using hu.substitution σ closed)

abbrev nonFunction := EnvironmentDelta.Basis.NonFunction

def absurdAllowed (env : Environment) (ghost : Bool) (term : Term) : Prop :=
  ghost = true ∨ nonFunction env term

def loopMotiveAllowed (env : Environment) (ghost proof : Bool) (motive : Term) : Prop :=
  ghost = true ∨ proof = true ∨ ∃ normal, Conversion.Conv env motive normal ∧ scalarLoopMotive normal = true

theorem loopMotiveAllowed_ofLegacy (h : NativeKernel.loopMotiveAllowed ghost proof motive) :
    loopMotiveAllowed env ghost proof motive := by
  rcases h with hg | hp | ⟨normal, hc, hs⟩
  · exact Or.inl hg
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr ⟨normal, .legacy hc, hs⟩)

theorem nonFunctionHead_full (h : NativeKernel.nonFunctionHead term = true) : nonFunction env term :=
  EnvironmentDelta.Basis.NonFunction.ofHead (EnvironmentDelta.Basis.legacy_nonFunctionHead h)

end Jihoo.NativeKernel.Environment
