import Jihoo.NativeACULegacyTransport

namespace Jihoo.NativeKernel.ACU.LegacyTransportExamples

private def zero : Term := .natural 0
private def wrap (t : Term) : Term := .uadd t zero

theorem beta_exposed_inside_additive_function (e : Bool) (A body arg : Term) :
    ∃ result, MixedRed (.app (wrap (.lam e A body)) arg) result ∧
      Arithmetic (body.subst (single arg)) result := by
  apply Computes.transport (.beta e A body arg)
  exact Arithmetic.node .app (.cons (Arithmetic.zero _).symm (.cons (.refl _) .nil))

theorem proof_projection_exposed_inside_additive_pack (p a q : Term) :
    ∃ result, MixedRed (.proof (wrap (.pack p a q))) result ∧ Arithmetic q result := by
  apply Computes.transport (.proofPack p a q)
  exact Arithmetic.node .proof (.cons (Arithmetic.zero _).symm .nil)

theorem literal_recovery_has_forward_derivation :
    ArithmeticRed (.uadd (.natural 2) (.natural 3)) (.natural 5) :=
  (Arithmetic.add 2 3 (by decide)).symm.recover_natural

theorem all_root_rules_have_forward_transport (root : Computes a b)
    (h : Arithmetic a a') :
    ∃ b', MixedRed a' b' ∧ Arithmetic b b' := root.transport h

theorem quotient_instantiation_accepts_arbitrary_terms (body : Term) (a : Term) :
    Arithmetic (body.subst (single (wrap a))) (body.subst (single a)) :=
  Arithmetic.instantiate (.refl body) (Arithmetic.zero a)

end Jihoo.NativeKernel.ACU.LegacyTransportExamples
