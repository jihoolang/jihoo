import Jihoo.NativeACUConfluence

namespace Jihoo.NativeKernel.ACU.Examples

private def zero : Term := .node (.natural 0) []
private def one : Term := .node (.natural 1) []
private def plus (a b : Term) : Term := .node .uadd [a,b]

/-- Balanced oversized arithmetic is derived, never encoded as invalid Natural. -/
theorem max_plus_one_balanced :
    Conv (plus (.node (.natural (2^64-1)) []) one)
      (plus (.node (.natural (2^63)) []) (.node (.natural (2^63)) [])) :=
  Conv.affine_equal (by cbv)

theorem generic_non_affine_atoms_commute (f a : Term) :
    Conv (plus (.node .app [f,a]) one) (plus one (.node .app [f,a])) := .comm _ _

/-- Zero elimination can reveal a beta redex in a function position. This is
one of the overlaps a full legacy/modulo proof must handle explicitly. -/
theorem zero_reveals_beta (e : Bool) (A body a : Term) :
    Conv (.node .app [plus (.node (.lam e) [A,body]) zero,a]) (body.subst (single a)) :=
  (Conv.node .app (.cons (.zero _) (.cons (.refl a) .nil))).trans
    (.legacy (.beta e A body a))

theorem full_substitution_can_leave_affine_fragment (σ : Nat → Term) :
    Conv ((plus (.var 0) (.var 1)).subst σ) ((plus (.var 1) (.var 0)).subst σ) :=
  (Conv.comm (.var 0) (.var 1)).substitution σ

theorem under_lam_capture_safe (ρ : Nat → Nat) (A a b : Term) :
    Conv ((Term.node (.lam false) [A,plus a b]).rename ρ)
      ((Term.node (.lam false) [A,plus b a]).rename ρ) :=
  (Conv.node (.lam false) (.cons (.refl A) (.cons (.comm a b) .nil))).renaming ρ

theorem pure_quotient_pi_injective
    (h : Theory (.node (.pi e) [A,B]) (.node (.pi e') [A',B'])) :
    e = e' ∧ Theory A A' ∧ Theory B B' := h.pi_injective

theorem pure_quotient_disjoint : ¬ Theory (.node .u64 []) (.node .i64 []) := by
  intro h
  have eq := (h.rigid_node_injective (by simp [flatten]) (by simp [flatten])).1
  cases eq

theorem branch_unit_common_forward_reduct (a b : Term) :
    Join (plus (plus a zero) b) (plus b (plus zero a)) := by
  apply Theory.church_rosser
  exact (Theory.addCong (.zero a) (.refl b)).trans
    ((Theory.comm a b).trans (Theory.addCong (.refl b) (Theory.zero_left a).symm))

theorem quotient_children_remain_native (A b c : Term) :
    Theory (.node (.pi true) [A,plus b c]) (.node (.pi true) [A,plus c b]) :=
  .node (.pi true) (.cons (.refl A) (.cons (.comm b c) .nil))

theorem real_forward_fork_joins (a b : Term) : Join (plus a b) (plus b a) :=
  Red.confluence (Red.zeroRight (plus a b))
    ((Red.comm (plus a b) zero).trans
      ((Red.zeroLeft (plus a b)).trans (Red.comm a b)))

theorem malformed_uadd_is_an_atom (a : Term) : flatten (.node .uadd [a]) = [.node .uadd [a]] := by
  simp only [flatten]

end Jihoo.NativeKernel.ACU.Examples
