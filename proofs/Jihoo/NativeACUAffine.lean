import Jihoo.NativeACU
import Jihoo.NativeAffineSum

/-! Explicit conversion derivations for affine canonicalization. No rule infers
conversion from semantic equality: every equation is built from ACU congruence
and the old bounded-literal addition rule. All intermediate literals are valid.
Unary expansions are proof intermediates, never executable normalizer output. -/
namespace Jihoo.NativeKernel.ACU

open Conversion (ListRel)
open AffineSum

/-- A proof-oriented right fold. The executable normalizer emits compact trees. -/
def sumTerms : List Term → Term
  | [] => .node (.natural 0) []
  | a :: xs => .node .uadd [a,sumTerms xs]

theorem Conv.sumTerms_append (xs ys : List Term) :
    Conv (.node .uadd [sumTerms xs,sumTerms ys]) (sumTerms (xs ++ ys)) := by
  induction xs with
  | nil => exact .zero_left _
  | cons x xs ih =>
      exact (Conv.assoc x (sumTerms xs) (sumTerms ys)).trans (.addCong (.refl x) ih)

theorem Conv.sumTerms_perm {xs ys : List Term} (h : xs.Perm ys) :
    Conv (sumTerms xs) (sumTerms ys) := by
  induction h with
  | nil => exact .refl _
  | cons x _ ih => exact .addCong (.refl x) ih
  | swap a b xs =>
      exact (Conv.assoc b a (sumTerms xs)).symm.trans
        ((Conv.addCong (Conv.comm b a) (.refl _)).trans (.assoc a b (sumTerms xs)))
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The existing bounded addition suffices to unfold every valid literal into
ones. In particular no invalid Natural(2^64) is postulated along this proof. -/
theorem Conv.literal_ones (n : Nat) (bound : n < wordLimit) :
    Conv (.node (.natural n) []) (sumTerms (List.replicate n (.node (.natural 1) []))) := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
      have small : n < wordLimit := by omega
      have folded := Conversion.Conv.add n 1 bound
      exact (Conv.legacy folded).symm.trans
        ((Conv.comm _ _).trans (Conv.addCong (.refl _) (ih small)))

private theorem shuffle_blocks (as bs cs ds : List Term) :
    ((as ++ bs) ++ (cs ++ ds)).Perm ((as ++ cs) ++ (bs ++ ds)) := by
  simpa only [List.append_assoc] using
    ((List.perm_append_comm (l₁ := bs) (l₂ := cs)).append_right ds).append_left as

/-- The canonical coefficient representation used only to construct proofs. -/
def linear (f : Form) : Term :=
  sumTerms (f.variables.map Term.var ++ List.replicate f.constant (.node (.natural 1) []))

/-- Flattening preserves every variable occurrence and unfolds each leaf only
under its own U64 bound, rather than folding the total into an invalid payload. -/
theorem Conv.affine_collect (e : Expr) (valid : e.Valid) :
    Conv e.toTerm (sumTerms (e.variables.map Term.var ++
      List.replicate e.constant (.node (.natural 1) []))) := by
  induction e with
  | var x => exact (Conv.zero (.var x)).symm
  | literal n => exact Conv.literal_ones n valid
  | add a b ia ib =>
      apply (Conv.addCong (ia valid.1) (ib valid.2)).trans
      apply (Conv.sumTerms_append _ _).trans
      apply Conv.sumTerms_perm
      simpa only [Expr.variables, Expr.constant, List.map_append, List.replicate_append_replicate] using
        shuffle_blocks (a.variables.map Term.var) (List.replicate a.constant (.node (.natural 1) []))
          (b.variables.map Term.var) (List.replicate b.constant (.node (.natural 1) []))

/-- Ascending variable sort is justified by explicit commutative-monoid steps. -/
theorem Conv.affine_linear (e : Expr) (valid : e.Valid) : Conv e.toTerm (linear (normalize e)) := by
  apply (Conv.affine_collect e valid).trans
  apply Conv.sumTerms_perm
  exact ((sortVariables_perm e.variables).symm.map Term.var).append_right _

/-- Actual executable affine normalization has an explicit conversion proof in
the isolated ACU extension. Its semantic completeness theorem is not a premise. -/
theorem Conv.affine_normalize (e : Expr) (valid : e.Valid) : Conv e.toTerm (normalize e).emit := by
  have outputValid := (normalize e).emitExpr_valid (normalize_payload valid)
  have out := Conv.affine_linear (normalize e).emitExpr outputValid
  rw [normalize_emitExpr _ (normalize_sorted e)] at out
  exact (Conv.affine_linear e valid).trans out.symm

theorem Conv.affine_canonical {t : Term} {f : Form} (h : canonical t = some f) : Conv t f.emit := by
  obtain ⟨e, _, he, valid, rfl⟩ := canonical_spec h
  rw [← he]
  exact Conv.affine_normalize e valid

/-- A checker could use this theorem only after ACU conversion is admitted by a
separately justified typing judgment; the existing checker remains unchanged. -/
theorem Conv.affine_equal {a b : Term} (h : equal a b = true) : Conv a b := by
  unfold equal at h
  split at h
  · rename_i fa fb ha hb
    have same : fa = fb := of_decide_eq_true h
    subst fb
    exact (Conv.affine_canonical ha).trans (Conv.affine_canonical hb).symm
  · simp at h

end Jihoo.NativeKernel.ACU
