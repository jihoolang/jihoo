import Jihoo.NativeACUForwardConfluence

/-! Typing-independent names for proved actual ACU shape and injectivity facts. -/
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

end Jihoo.NativeKernel
