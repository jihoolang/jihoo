import Jihoo.NativeConfluence

/-! A precise boundary for importing native proof-irrelevant comparison into
untyped conversion. Arbitrary Pack-proof equality plus generic Proof congruence
and projection would equate every raw term. Typed irrelevance needs its own
formation premises and cannot be added as an unconditional Conv constructor. -/
namespace Jihoo.NativeKernel.IrrelevanceBoundary

open Conversion

def PackProofIrrelevant (R : Term → Term → Prop) : Prop :=
  ∀ p a q r, R (.pack p a q) (.pack p a r)

def ProofCongruent (R : Term → Term → Prop) : Prop :=
  ∀ {a b}, R a b → R (.proof a) (.proof b)

theorem arbitrary_pack_irrelevance_collapses
    (R : Term → Term → Prop)
    (symmetric : ∀ {a b}, R a b → R b a)
    (transitive : ∀ {a b c}, R a b → R b c → R a c)
    (projects : ∀ p a q, R (.proof (.pack p a q)) q)
    (congruent : ProofCongruent R)
    (irrelevant : PackProofIrrelevant R) : ∀ a b, R a b := by
  intro a b
  exact transitive (symmetric (projects .u64 (.natural 0) a))
    (transitive (congruent (irrelevant .u64 (.natural 0) a b))
      (projects .u64 (.natural 0) b))

theorem current_conversion_has_proof_congruence : ProofCongruent Conv := by
  intro a b h
  exact .node .proof (.cons h .nil)

theorem arbitrary_pack_irrelevance_rejected : ¬ PackProofIrrelevant Conv := by
  intro irrelevant
  have total := arbitrary_pack_irrelevance_collapses Conv Conv.symm Conv.trans
    Conv.proofPack current_conversion_has_proof_congruence irrelevant
  exact Conv.u64_i64_separate (total .u64 .i64)

end Jihoo.NativeKernel.IrrelevanceBoundary
