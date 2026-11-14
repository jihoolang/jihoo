import Jihoo.NativeACUBoundedNormalizer
import Jihoo.NativeKernelEnvironment
import Jihoo.NativeCheckerSoundness

/-! Concrete full native conversion for the existing environment judgment.
The alias is the actual proved ACU.Conv relation. This module supplies the
bounded converter and honest conservative policies for unresolved globals. -/
namespace Jihoo.NativeKernel

namespace ACU

private theorem Arithmetic.variable_node_separate (rigid : fullRigid op = true) :
    ¬ Arithmetic (.var x) (.node op xs) := by
  intro h
  have flat : arithmeticFlatten (.node op xs) = [.node op xs] := by
    have hrigid := (Bool.and_eq_true_iff.mp rigid).2
    cases op <;> simp_all only [arithmeticRigid,Bool.false_eq_true,arithmeticFlatten]
  have model := h.model
  unfold ArithmeticModel at model
  simp only [arithmeticFlatten,flat] at model
  have atom := model.singleton ArithmeticAtom.refl ArithmeticAtom.symm ArithmeticAtom.trans
  cases atom

theorem Conv.full_variable_node_separate (rigid : fullRigid op = true) : ¬ Conv (.var x) (.node op xs) := by
  intro h
  obtain ⟨c,hc,kc⟩ := h.church_rosser_modulo_arithmetic
  have varView := hc.variable_shape (.refl _)
  obtain ⟨ys,node,_⟩ := kc.rigid_shape rigid (.refl _)
  exact Arithmetic.variable_node_separate rigid (varView.symm.trans node)

-- Familiar theorem names are retained for clients of the existing judgment.
theorem Conv.pi_injective (h : Conv (.pi e A B) (.pi e' A' B')) :
    e = e' ∧ Conv A A' ∧ Conv B B' := h.full_pi_injective
theorem Conv.sort_injective {s r : SortTag} (h : Conv s.term r.term) : s = r := h.full_sort_injective
theorem Conv.array_injective (h : Conv (.array a) (.array b)) : Conv a b := h.full_array_injective
theorem Conv.eq_injective (h : Conv (.eq a b) (.eq a' b')) : Conv a a' ∧ Conv b b' := h.full_eq_injective
theorem Conv.lt_injective (h : Conv (.lt a b) (.lt a' b')) : Conv a a' ∧ Conv b b' := h.full_lt_injective
theorem Conv.refine_injective (h : Conv (.refine a) (.refine b)) : Conv a b := h.full_refine_injective
theorem Conv.natural_injective (h : Conv (.natural a) (.natural b)) : a = b := h.full_natural_injective

end ACU
namespace Environment.Conversion

abbrev Conv := ACU.Conv
abbrev ListRel := Jihoo.NativeKernel.Conversion.ListRel
abbrev treeSize := Jihoo.NativeKernel.Conversion.treeSize
abbrev treeDepth := Jihoo.NativeKernel.Conversion.treeDepth
abbrev substitutionSafe := Jihoo.NativeKernel.Conversion.substitutionSafe

/-- Every old conversion remains available through the concrete ACU base. -/
theorem ofLegacy (h : Jihoo.NativeKernel.Conversion.Conv a b) : Conv a b := .legacy h

/-- Head exposure propagates bounded failure explicitly. -/
def normalize? (fuel : Nat) (t : Term) : Option Term := ACU.Bounded.kit.normalize (min fuel 128) 200000 t

/-- Total policy helper: a refused normalization retains its original term.
The fallback is the identity conversion, never an assumed normalized result.
Executable head exposure itself uses normalize? and fails on refusal. -/
def normalize (fuel : Nat) (t : Term) : Term := (normalize? fuel t).getD t

def equal (fuel : Nat) (a b : Term) : Bool := ACU.Bounded.kit.equal (min fuel 128) 200000 a b

theorem normalize?_sound (h : normalize? fuel t = some u) : Conv t u := ACU.Bounded.kit.normalizationSound h

theorem normalize?_forward (h : normalize? fuel t = some u) : ACU.MixedRed t u := ACU.Bounded.kit.normalizationForward h

theorem normalize_sound (fuel : Nat) (t : Term) : Conv t (normalize fuel t) := by
  unfold normalize
  cases h : normalize? fuel t with
  | none => exact .refl _
  | some u => exact normalize?_sound h

theorem equal_sound (h : equal fuel a b = true) : Conv a b := ACU.Bounded.kit.equalitySound h

end Environment.Conversion
namespace Environment

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

def pureBinderAllowed (erased : Bool) (domain : Term) (sort : SortTag) : Prop :=
  if erased then sort = .prop ∨ Conversion.Conv domain .u64 else sort ≠ .prop

theorem pureBinderAllowed_ofLegacy (h : Jihoo.NativeKernel.binderAllowed erased domain sort) :
    pureBinderAllowed erased domain sort := by
  cases erased with
  | false => exact h
  | true => rcases h with hp | hu; exact Or.inl hp; exact Or.inr (.legacy hu)

theorem pureBinderAllowed_renaming (h : pureBinderAllowed erased domain sort) (ρ : Nat → Nat) :
    pureBinderAllowed erased (domain.rename ρ) sort := by
  cases erased with
  | false => exact h
  | true =>
      rcases h with hp | hu
      · exact Or.inl hp
      · exact Or.inr (by simpa only [Term.rename,renameArgs] using hu.renaming ρ)

theorem pureBinderAllowed_substitution (h : pureBinderAllowed erased domain sort) (σ : Nat → Term) :
    pureBinderAllowed erased (domain.subst σ) sort := by
  cases erased with
  | false => exact h
  | true =>
      rcases h with hp | hu
      · exact Or.inl hp
      · exact Or.inr (by simpa only [Term.subst,substArgs] using hu.substitution σ)

/-- Every conversion quantified by this runtime guard is actual full ACU. -/
def nonFunction (t : Term) : Prop := ∀ e A B, ¬ Conversion.Conv t (.pi e A B)
def absurdAllowed (ghost : Bool) (t : Term) : Prop := ghost = true ∨ nonFunction t

def loopMotiveAllowed (ghost proof : Bool) (motive : Term) : Prop :=
  ghost = true ∨ proof = true ∨ ∃ normal, Conversion.Conv motive normal ∧ scalarLoopMotive normal = true

theorem loopMotiveAllowed_ofLegacy (h : Jihoo.NativeKernel.loopMotiveAllowed ghost proof motive) :
    loopMotiveAllowed ghost proof motive := by
  rcases h with hg | hp | ⟨normal,hc,hs⟩
  · exact Or.inl hg
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr ⟨normal,.legacy hc,hs⟩)

theorem nonFunctionHead_full (h : nonFunctionHead t = true) : nonFunction t := by
  intro e A B converted
  fun_cases nonFunctionHead t <;> simp_all only [nonFunctionHead,Bool.false_eq_true]
  all_goals first
    | exact ACU.Conv.full_variable_node_separate rfl converted
    | exact ACU.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same) converted

end Environment
end Jihoo.NativeKernel
