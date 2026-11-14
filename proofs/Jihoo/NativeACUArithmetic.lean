import Jihoo.NativeACUTheory

/-! Arithmetic additive quotient on full native syntax. Bounded literal folding
is included explicitly. Valid literals are modeled by finite multisets of one;
invalid literal payloads remain distinct opaque atoms. This is an independent
layer, not a new rule in shared typing or Conversion.Conv. -/
namespace Jihoo.NativeKernel.ACU

open Conversion (ListRel)
open AffineSum (wordLimit)

inductive Arithmetic : Term → Term → Prop where
  | refl (t : Term) : Arithmetic t t
  | symm : Arithmetic a b → Arithmetic b a
  | trans : Arithmetic a b → Arithmetic b c → Arithmetic a c
  | node (op : Op) : ListRel Arithmetic xs ys → Arithmetic (.node op xs) (.node op ys)
  | assoc (a b c : Term) :
      Arithmetic (.node .uadd [.node .uadd [a,b],c]) (.node .uadd [a,.node .uadd [b,c]])
  | comm (a b : Term) : Arithmetic (.node .uadd [a,b]) (.node .uadd [b,a])
  | zero (a : Term) : Arithmetic (.node .uadd [a,.node (.natural 0) []]) a
  | add (m n : Nat) : m+n < wordLimit →
      Arithmetic (.node .uadd [.node (.natural m) [],.node (.natural n) []])
        (.node (.natural (m+n)) [])

theorem Arithmetic.toConv (h : Arithmetic a b) : Conv a b := by
  induction h using Arithmetic.rec (motive_2 := fun xs ys _ => ListRel Conv xs ys) with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ia ib => exact ia.trans ib
  | node op _ ih => exact .node op ih
  | assoc a b c => exact .assoc a b c
  | comm a b => exact .comm a b
  | zero a => exact .zero a
  | add m n h => exact .legacy (.add m n h)
  | nil => exact .nil
  | cons _ _ ia ib => exact .cons ia ib

theorem Arithmetic.renaming (h : Arithmetic a b) (ρ : Nat → Nat) : Arithmetic (a.rename ρ) (b.rename ρ) := by
  induction h using Arithmetic.rec
    (motive_2 := fun xs ys _ => ∀ op offset ρ,
      ListRel Arithmetic (renameArgs op ρ offset xs) (renameArgs op ρ offset ys)) generalizing ρ with
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih ρ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ ρ) (ih₂ ρ)
  | node op _ ih => simpa only [Term.rename] using Arithmetic.node op (ih op 0 ρ)
  | assoc a b c =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
        Arithmetic.assoc (a.rename ρ) (b.rename ρ) (c.rename ρ)
  | comm a b =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using Arithmetic.comm (a.rename ρ) (b.rename ρ)
  | zero a =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using Arithmetic.zero (a.rename ρ)
  | add m n h =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using Arithmetic.add m n h
  | nil => simp [renameArgs]; exact .nil
  | cons _ _ ihx ihxs =>
      rename_i op offset ρ
      simp only [renameArgs]
      exact .cons (ihx _) (ihxs op (offset+1) ρ)

theorem Arithmetic.substitution (h : Arithmetic a b) (σ : Nat → Term) : Arithmetic (a.subst σ) (b.subst σ) := by
  induction h using Arithmetic.rec
    (motive_2 := fun xs ys _ => ∀ op offset σ,
      ListRel Arithmetic (substArgs op σ offset xs) (substArgs op σ offset ys)) generalizing σ with
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih σ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ σ) (ih₂ σ)
  | node op _ ih => simpa only [Term.subst] using Arithmetic.node op (ih op 0 σ)
  | assoc a b c =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using
        Arithmetic.assoc (a.subst σ) (b.subst σ) (c.subst σ)
  | comm a b =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using Arithmetic.comm (a.subst σ) (b.subst σ)
  | zero a =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using Arithmetic.zero (a.subst σ)
  | add m n h =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using Arithmetic.add m n h
  | nil => simp [substArgs]; exact .nil
  | cons _ _ ihx ihxs =>
      rename_i op offset σ
      simp only [substArgs]
      exact .cons (ihx _) (ihxs op (offset+1) σ)


private theorem listRel_refl (r : ∀ x, R x x) (xs : List Term) : ListRel R xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (r x) ih

private theorem listRel_symm (s : ∀ {x y}, R x y → R y x) (h : ListRel R xs ys) :
    ListRel R ys xs := by
  induction h with
  | nil => exact .nil
  | cons h _ ia => exact .cons (s h) ia

private theorem listRel_trans (t : ∀ {x y z}, R x y → R y z → R x z)
    (h : ListRel R xs ys) (k : ListRel R ys zs) : ListRel R xs zs := by
  induction h generalizing zs with
  | nil => cases k; exact .nil
  | cons h hs ih => cases k with | cons k ks => exact .cons (t h k) (ih ks)

private theorem listRel_append (h : ListRel R xs ys) (k : ListRel R us vs) :
    ListRel R (xs ++ us) (ys ++ vs) := by
  induction h with
  | nil => exact k
  | cons h _ ih => exact .cons h ih

private theorem listRel_length (h : ListRel R xs ys) : xs.length = ys.length := by
  induction h <;> simp_all

/-- Valid word literals become unary one-spines only in the proof model.
The executable normalizer continues to use compact balanced constants. -/
def arithmeticFlatten : Term → List Term
  | .node .uadd [a,b] => arithmeticFlatten a ++ arithmeticFlatten b
  | .node (.natural n) [] =>
      if n < wordLimit then List.replicate n (.node (.natural 1) []) else [.node (.natural n) []]
  | t => [t]
termination_by t => sizeOf t
decreasing_by all_goals simp_wf; all_goals omega

inductive ArithmeticAtom : Term → Term → Prop where
  | var (x : Nat) : ArithmeticAtom (.var x) (.var x)
  | node (op : Op) : ListRel Arithmetic xs ys → ArithmeticAtom (.node op xs) (.node op ys)

theorem ArithmeticAtom.refl (t : Term) : ArithmeticAtom t t := by
  cases t with
  | var x => exact .var x
  | node op xs => exact .node op (listRel_refl Arithmetic.refl xs)

theorem ArithmeticAtom.symm (h : ArithmeticAtom a b) : ArithmeticAtom b a := by
  cases h with
  | var x => exact .var x
  | node op h => exact .node op (listRel_symm Arithmetic.symm h)

theorem ArithmeticAtom.trans (h : ArithmeticAtom a b) (k : ArithmeticAtom b c) : ArithmeticAtom a c := by
  cases h with
  | var x => cases k; exact .var x
  | node op h => cases k with | node _ k => exact .node op (listRel_trans Arithmetic.trans h k)

def ArithmeticModel (a b : Term) : Prop := Bag ArithmeticAtom (arithmeticFlatten a) (arithmeticFlatten b)

private theorem ArithmeticModel.node (op : Op) (h : ListRel Arithmetic xs ys)
    (ih : ListRel ArithmeticModel xs ys) : ArithmeticModel (.node op xs) (.node op ys) := by
  have atom : Bag ArithmeticAtom [.node op xs] [.node op ys] := .pointwise (.cons (.node op h) .nil)
  unfold ArithmeticModel
  cases op <;> try (simpa only [arithmeticFlatten] using atom)
  case uadd =>
    cases h with
    | nil => simpa only [arithmeticFlatten] using atom
    | cons ha hs =>
        cases hs with
        | nil => simpa only [arithmeticFlatten] using atom
        | cons hb hs =>
            cases hs with
            | nil =>
                cases ih with
                | cons ia is => cases is with | cons ib is =>
                    simpa only [arithmeticFlatten] using Bag.append ArithmeticAtom.refl ia ib
            | cons hc hs => simpa only [arithmeticFlatten] using atom
  case natural n =>
    cases h with
    | nil => exact .refl _
    | cons ha hs => simpa only [arithmeticFlatten] using atom

/-- Genuine arithmetic quotient semantics, with no postulated interpretation. -/
theorem Arithmetic.model (h : Arithmetic a b) : ArithmeticModel a b := by
  induction h using Arithmetic.rec
    (motive_2 := fun xs ys _ => ListRel ArithmeticModel xs ys) with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ia ib => exact ia.trans ib
  | node op h ih => exact ArithmeticModel.node op h ih
  | assoc a b c => simp only [ArithmeticModel, arithmeticFlatten, List.append_assoc]; exact .refl _
  | comm a b => simp only [ArithmeticModel, arithmeticFlatten]; exact .perm List.perm_append_comm
  | zero a =>
      have bound : 0 < wordLimit := by decide
      simp only [ArithmeticModel, arithmeticFlatten, bound, ↓reduceIte, List.replicate_zero,
        List.append_nil]
      exact .refl _
  | add m n h =>
      have hm : m < wordLimit := by omega
      have hn : n < wordLimit := by omega
      simp only [ArithmeticModel, arithmeticFlatten, hm, hn, h, ↓reduceIte,
        List.replicate_append_replicate]
      exact .refl _
  | nil => exact .nil
  | cons _ _ ia ib => exact .cons ia ib

theorem Arithmetic.rigid_node_injective (h : Arithmetic (.node op xs) (.node op' ys))
    (left : arithmeticFlatten (.node op xs) = [.node op xs])
    (right : arithmeticFlatten (.node op' ys) = [.node op' ys]) :
    op = op' ∧ ListRel Arithmetic xs ys := by
  have hm := h.model
  unfold ArithmeticModel at hm
  rw [left,right] at hm
  have ha := hm.singleton ArithmeticAtom.refl ArithmeticAtom.symm ArithmeticAtom.trans
  cases ha with
  | node op h => exact ⟨rfl,h⟩

theorem Arithmetic.pi_injective
    (h : Arithmetic (.node (.pi e) [A,B]) (.node (.pi e') [A',B'])) :
    e = e' ∧ Arithmetic A A' ∧ Arithmetic B B' := by
  obtain ⟨eq,kids⟩ := h.rigid_node_injective
    (by simp only [arithmeticFlatten]) (by simp only [arithmeticFlatten])
  cases eq
  cases kids with
  | cons ha hs => cases hs with | cons hb _ => exact ⟨rfl,ha,hb⟩

theorem Arithmetic.addCong (ha : Arithmetic a a') (hb : Arithmetic b b') :
    Arithmetic (.node .uadd [a,b]) (.node .uadd [a',b']) :=
  .node .uadd (.cons ha (.cons hb .nil))

theorem Arithmetic.zero_left (a : Term) : Arithmetic (.node .uadd [.node (.natural 0) [],a]) a :=
  (Arithmetic.comm _ _).trans (.zero a)

theorem Arithmetic.sumTerms_append (xs ys : List Term) :
    Arithmetic (.node .uadd [sumTerms xs,sumTerms ys]) (sumTerms (xs ++ ys)) := by
  induction xs with
  | nil => exact .zero_left _
  | cons x xs ih =>
      exact (Arithmetic.assoc x (sumTerms xs) (sumTerms ys)).trans (.addCong (.refl x) ih)

theorem Arithmetic.sumTerms_perm {xs ys : List Term} (h : xs.Perm ys) :
    Arithmetic (sumTerms xs) (sumTerms ys) := by
  induction h with
  | nil => exact .refl _
  | cons x _ ih => exact .addCong (.refl x) ih
  | swap a b xs =>
      exact (Arithmetic.assoc b a (sumTerms xs)).symm.trans
        ((Arithmetic.addCong (Arithmetic.comm b a) (.refl _)).trans (.assoc a b (sumTerms xs)))
  | trans _ _ ia ib => exact ia.trans ib

theorem Arithmetic.literal_ones (n : Nat) (bound : n < wordLimit) :
    Arithmetic (.node (.natural n) []) (sumTerms (List.replicate n (.node (.natural 1) []))) := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
      have small : n < wordLimit := by omega
      exact (Arithmetic.add n 1 bound).symm.trans
        ((Arithmetic.comm _ _).trans (Arithmetic.addCong (.refl _) (ih small)))

theorem Arithmetic.flatten (t : Term) : Arithmetic t (sumTerms (arithmeticFlatten t)) := by
  fun_induction arithmeticFlatten t with
  | case1 a b ia ib => exact (Arithmetic.addCong ia ib).trans (Arithmetic.sumTerms_append _ _)
  | case2 n bound => exact Arithmetic.literal_ones n bound
  | case3 n _ => exact (Arithmetic.zero (.node (.natural n) [])).symm
  | case4 t _ _ => exact (Arithmetic.zero t).symm

theorem ArithmeticAtom.toArithmetic (h : ArithmeticAtom a b) : Arithmetic a b := by
  cases h with
  | var x => exact .refl _
  | node op h => exact .node op h

theorem Bag.toArithmetic (h : Bag ArithmeticAtom xs ys) : Arithmetic (sumTerms xs) (sumTerms ys) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ia ib => exact ia.trans ib
  | perm h => exact Arithmetic.sumTerms_perm h
  | pointwise h =>
      induction h with
      | nil => exact .refl _
      | cons ha hs ih => exact .addCong ha.toArithmetic ih

theorem ArithmeticModel.complete (h : ArithmeticModel a b) : Arithmetic a b :=
  (Arithmetic.flatten a).trans (h.toArithmetic.trans (Arithmetic.flatten b).symm)

theorem arithmetic_iff_model (a b : Term) : Arithmetic a b ↔ ArithmeticModel a b :=
  ⟨Arithmetic.model,ArithmeticModel.complete⟩

private theorem shuffle_blocks (as bs cs ds : List Term) :
    ((as ++ bs) ++ (cs ++ ds)).Perm ((as ++ cs) ++ (bs ++ ds)) := by
  simpa only [List.append_assoc] using
    ((List.perm_append_comm (l₁ := bs) (l₂ := cs)).append_right ds).append_left as

open AffineSum

/-- Flattening preserves every variable occurrence and unfolds each leaf only
under its own U64 bound, rather than folding the total into an invalid payload. -/
theorem Arithmetic.affine_collect (e : Expr) (valid : e.Valid) :
    Arithmetic e.toTerm (sumTerms (e.variables.map Term.var ++
      List.replicate e.constant (.node (.natural 1) []))) := by
  induction e with
  | var x => exact (Arithmetic.zero (.var x)).symm
  | literal n => exact Arithmetic.literal_ones n valid
  | add a b ia ib =>
      apply (Arithmetic.addCong (ia valid.1) (ib valid.2)).trans
      apply (Arithmetic.sumTerms_append _ _).trans
      apply Arithmetic.sumTerms_perm
      simpa only [Expr.variables, Expr.constant, List.map_append, List.replicate_append_replicate] using
        shuffle_blocks (a.variables.map Term.var) (List.replicate a.constant (.node (.natural 1) []))
          (b.variables.map Term.var) (List.replicate b.constant (.node (.natural 1) []))

/-- Ascending variable sort is justified by explicit commutative-monoid steps. -/
theorem Arithmetic.affine_linear (e : Expr) (valid : e.Valid) : Arithmetic e.toTerm (linear (normalize e)) := by
  apply (Arithmetic.affine_collect e valid).trans
  apply Arithmetic.sumTerms_perm
  exact ((sortVariables_perm e.variables).symm.map Term.var).append_right _

/-- Actual executable affine normalization has an explicit conversion proof in
the isolated ACU extension. Its semantic completeness theorem is not a premise. -/
theorem Arithmetic.affine_normalize (e : Expr) (valid : e.Valid) : Arithmetic e.toTerm (normalize e).emit := by
  have outputValid := (normalize e).emitExpr_valid (normalize_payload valid)
  have out := Arithmetic.affine_linear (normalize e).emitExpr outputValid
  rw [normalize_emitExpr _ (normalize_sorted e)] at out
  exact (Arithmetic.affine_linear e valid).trans out.symm

theorem Arithmetic.affine_canonical {t : Term} {f : Form} (h : canonical t = some f) : Arithmetic t f.emit := by
  obtain ⟨e, _, he, valid, rfl⟩ := canonical_spec h
  rw [← he]
  exact Arithmetic.affine_normalize e valid

/-- A checker could use this theorem only after ACU conversion is admitted by a
separately justified typing judgment; the existing checker remains unchanged. -/
theorem Arithmetic.affine_equal {a b : Term} (h : equal a b = true) : Arithmetic a b := by
  unfold equal at h
  split at h
  · rename_i fa fb ha hb
    have same : fa = fb := of_decide_eq_true h
    subst fb
    exact (Arithmetic.affine_canonical ha).trans (Arithmetic.affine_canonical hb).symm
  · simp at h


private theorem natural_atom_payload {m n : Nat}
    (h : ArithmeticAtom (.node (.natural m) []) (.node (.natural n) [])) : m = n := by
  cases h
  rfl

/-- Arithmetic quotienting never identifies different natural payloads, even
when malformed oversized literals appear in untyped full native terms. -/
theorem Arithmetic.natural_injective
    (h : Arithmetic (.node (.natural m) []) (.node (.natural n) [])) : m = n := by
  have model := h.model
  have len := model.length
  unfold ArithmeticModel at model len
  by_cases hm : m < wordLimit <;> by_cases hn : n < wordLimit
  · simpa only [arithmeticFlatten, hm, hn, ↓reduceIte, List.length_replicate] using len
  · have em : m = 1 := by
      simpa only [arithmeticFlatten, hm, hn, ↓reduceIte, List.length_replicate, List.length_singleton] using len
    subst m
    simp only [arithmeticFlatten, hm, hn, ↓reduceIte, List.replicate_succ,
      List.replicate_zero] at model
    exact natural_atom_payload (model.singleton ArithmeticAtom.refl ArithmeticAtom.symm ArithmeticAtom.trans)
  · have en : n = 1 := by
      simpa only [arithmeticFlatten, hm, hn, ↓reduceIte, List.length_replicate, List.length_singleton] using len.symm
    subst n
    simp only [arithmeticFlatten, hm, hn, ↓reduceIte, List.replicate_succ,
      List.replicate_zero] at model
    exact natural_atom_payload (model.singleton ArithmeticAtom.refl ArithmeticAtom.symm ArithmeticAtom.trans)
  · simp only [arithmeticFlatten, hm, hn, ↓reduceIte] at model
    exact natural_atom_payload (model.singleton ArithmeticAtom.refl ArithmeticAtom.symm ArithmeticAtom.trans)

/-- A rigid node remains exposable after arbitrary arithmetic quotient changes,
including additive zero wrappers around the entire node. Unlike injectivity,
this theorem does not assume the other endpoint has a node head already. -/
theorem Arithmetic.expose_node (h : Arithmetic (.node op xs) t)
    (atomic : arithmeticFlatten (.node op xs) = [.node op xs]) :
    ∃ ys, Arithmetic t (.node op ys) ∧ ListRel Arithmetic xs ys := by
  have model := h.model
  unfold ArithmeticModel at model
  rw [atomic] at model
  obtain ⟨zs,hp,hr⟩ := model.matching ArithmeticAtom.refl ArithmeticAtom.symm ArithmeticAtom.trans
  have eq : zs = [.node op xs] := (List.singleton_perm.mp hp).symm
  rw [eq] at hr
  generalize ht : arithmeticFlatten t = ts at hr
  cases hr with
  | cons atom tail =>
      cases tail
      cases atom with
      | node op kids =>
          refine ⟨_,?_,kids⟩
          have normal := Arithmetic.flatten t
          rw [ht] at normal
          exact normal.trans (.zero _)

theorem Arithmetic.pi_view
    (h : Arithmetic (.node (.pi e) [A,B]) t) :
    ∃ A' B', Arithmetic t (.node (.pi e) [A',B']) ∧ Arithmetic A A' ∧ Arithmetic B B' := by
  obtain ⟨ys,exposed,kids⟩ := h.expose_node (by simp only [arithmeticFlatten])
  cases kids with
  | cons ha hs => cases hs with
    | cons hb hs => cases hs; exact ⟨_,_,exposed,ha,hb⟩

end Jihoo.NativeKernel.ACU
