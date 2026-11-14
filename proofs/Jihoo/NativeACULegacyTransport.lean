import Jihoo.NativeACUArithmeticConfluence
import Jihoo.NativeConfluence

/-! Forward transport of legacy computation through additive quotient changes.
The arithmetic model is used only through proved theorems; all displayed
computations remain finite derivations on native syntax. -/
namespace Jihoo.NativeKernel.ACU

open Conversion (ListRel)

private theorem lift_arithmetic {σ τ : Nat → Term}
    (h : ∀ x, Arithmetic (σ x) (τ x)) (n : Nat) :
    ∀ x, Arithmetic (liftSub n σ x) (liftSub n τ x) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro x
      cases x with
      | zero => exact .refl _
      | succ x => exact (ih x).renaming Nat.succ

/-- Arbitrary related substitutions preserve arithmetic quotienting, including
at binder edges and when replacements contain beta redexes or observing nodes. -/
theorem Arithmetic.subst_congr {σ τ : Nat → Term}
    (hσ : ∀ x, Arithmetic (σ x) (τ x)) (t : Term) :
    Arithmetic (t.subst σ) (t.subst τ) := by
  induction t using Term.rec
    (motive_2 := fun xs => ∀ op offset σ τ, (∀ x, Arithmetic (σ x) (τ x)) →
      ListRel Arithmetic (substArgs op σ offset xs) (substArgs op τ offset xs)) generalizing σ τ with
  | var x => simp only [Term.subst]; exact hσ x
  | node op xs ih => simpa only [Term.subst] using Arithmetic.node op (ih op 0 σ τ hσ)
  | nil => intros; simp [substArgs]; exact .nil
  | cons x xs ihx ihxs =>
      rename_i op offset σ τ h
      simp only [substArgs]
      exact .cons (ihx (lift_arithmetic h (op.binders offset))) (ihxs op (offset+1) σ τ h)

theorem Arithmetic.instantiate (hb : Arithmetic body body') (ha : Arithmetic a a') :
    Arithmetic (body.subst (single a)) (body'.subst (single a')) := by
  apply (hb.substitution (single a)).trans
  apply Arithmetic.subst_congr
  intro x
  cases x with
  | zero => exact ha
  | succ x => exact .refl _

/-- Operators whose complete outer node survives forward arithmetic reduction.
This includes every non-additive legacy computation head and every data head it
observes. Natural literals have a separate recovery theorem. -/
def arithmeticRigid : Op → Bool
  | .uadd | .natural _ => false
  | _ => true

private theorem listRed_refl (xs : List Term) : ListRel ArithmeticRed xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (.refl x) ih

private theorem listRed_trans (h : ListRel ArithmeticRed xs ys)
    (k : ListRel ArithmeticRed ys zs) : ListRel ArithmeticRed xs zs := by
  induction h generalizing zs with
  | nil => cases k; exact .nil
  | cons h hs ih => cases k with | cons k ks => exact .cons (h.trans k) (ih ks)

/-- Unlike a quotient exposure proposition, this result displays a forward
arithmetic computation from the original node to the exposed node. -/
theorem ArithmeticRed.rigid_shape (h : ArithmeticRed t u) :
    ∀ {op xs}, arithmeticRigid op = true → t = .node op xs →
      ∃ ys, u = .node op ys ∧ ListRel ArithmeticRed xs ys := by
  induction h using ArithmeticRed.rec
    (motive_2 := fun _ _ _ => True) with
  | refl t => intro op xs _ eq; exact ⟨xs,eq,listRed_refl xs⟩
  | trans h k ih ik =>
      intro op xs hr eq
      obtain ⟨ys,ey,hy⟩ := ih hr eq
      obtain ⟨zs,ez,hz⟩ := ik hr ey
      exact ⟨zs,ez,listRed_trans hy hz⟩
  | node op kids _ =>
      intro op' xs hr eq
      cases eq
      exact ⟨_,rfl,kids⟩
  | assocRight | assocLeft | comm | zeroRight | zeroLeft | literalAdd =>
      intro op xs hr eq
      cases eq
      contradiction
  | literalSplit n bound =>
      intro op xs hr eq
      cases eq
      contradiction
  | nil => trivial
  | cons => trivial

private theorem listRel_one (h : ListRel R [a] ys) : ∃ b, ys = [b] ∧ R a b := by
  cases h with
  | cons h hs => cases hs; exact ⟨_,rfl,h⟩

private theorem listRel_two (h : ListRel R [a,b] ys) :
    ∃ a' b', ys = [a',b'] ∧ R a a' ∧ R b b' := by
  cases h with
  | cons ha hs =>
      obtain ⟨b',rfl,hb⟩ := listRel_one hs
      exact ⟨_,_,rfl,ha,hb⟩

private theorem listRel_three (h : ListRel R [a,b,c] ys) :
    ∃ a' b' c', ys = [a',b',c'] ∧ R a a' ∧ R b b' ∧ R c c' := by
  cases h with
  | cons ha hs =>
      obtain ⟨b',c',rfl,hb,hc⟩ := listRel_two hs
      exact ⟨_,_,_,rfl,ha,hb,hc⟩

private theorem listRel_four (h : ListRel R [a,b,c,d] ys) :
    ∃ a' b' c' d', ys = [a',b',c',d'] ∧ R a a' ∧ R b b' ∧ R c c' ∧ R d d' := by
  cases h with
  | cons ha hs =>
      obtain ⟨b',c',d',rfl,hb,hc,hd⟩ := listRel_three hs
      exact ⟨_,_,_,_,rfl,ha,hb,hc,hd⟩

private theorem atom_natural_exact (h : ArithmeticAtom (.node (.natural n) []) t) :
    t = .node (.natural n) [] := by
  cases h with
  | node _ hs => cases hs; rfl

private theorem replicas_exact (h : ListRel ArithmeticAtom (List.replicate n (.node (.natural 1) [])) xs) :
    xs = List.replicate n (.node (.natural 1) []) := by
  induction n generalizing xs with
  | zero => cases h; rfl
  | succ n ih =>
      cases h with
      | cons ha hs => rw [atom_natural_exact ha,ih hs]; rfl

/-- Folding a proof-model one-spine never constructs an oversized payload. -/
theorem ArithmeticRed.ones_fold (n : Nat) (bound : n < AffineSum.wordLimit) :
    ArithmeticRed (compact (List.replicate n (.node (.natural 1) []))) (.node (.natural n) []) := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
      cases n with
      | zero => exact .refl _
      | succ n =>
          have smaller : n+1 < AffineSum.wordLimit := by omega
          apply (ArithmeticRed.addCong (.refl _) (ih smaller)).trans
          simpa only [Nat.add_comm 1 (n+1)] using ArithmeticRed.literalAdd 1 (n+1) (by omega)

/-- If a literal is hidden by any finite arithmetic quotient change, it can be
recovered by an actual forward arithmetic derivation. Payloads outside U64 stay
opaque, so this theorem does not assume malformed literals denote large sums. -/
theorem Arithmetic.recover_natural (h : Arithmetic (.node (.natural n) []) t) :
    ArithmeticRed t (.node (.natural n) []) := by
  have hm := h.model
  unfold ArithmeticModel at hm
  obtain ⟨xs,hp,hr⟩ := hm.matching ArithmeticAtom.refl ArithmeticAtom.symm ArithmeticAtom.trans
  by_cases bound : n < AffineSum.wordLimit
  · simp only [arithmeticFlatten,bound,↓reduceIte] at hp
    have ex : xs = List.replicate n (.node (.natural 1) []) := List.perm_replicate.mp hp.symm
    rw [ex] at hr
    have et := replicas_exact hr
    have forward := ArithmeticRed.flatten t
    rw [et] at forward
    exact forward.trans (ArithmeticRed.ones_fold n bound)
  · simp only [arithmeticFlatten,bound,↓reduceIte] at hp
    have ex : xs = [.node (.natural n) []] := (List.singleton_perm.mp hp).symm
    rw [ex] at hr
    obtain ⟨u,eu,hu⟩ := listRel_one hr
    have eu' := atom_natural_exact hu
    have forward := ArithmeticRed.flatten t
    rw [eu,eu'] at forward
    exact forward

/-- A rigid node hidden behind additive units is exposed by forward arithmetic
steps, with all of its original children reduced in parallel along the way. -/
theorem Arithmetic.forward_node (h : Arithmetic (.node op xs) t)
    (rigid : arithmeticRigid op = true) :
    ∃ ys, ArithmeticRed t (.node op ys) ∧ ListRel ArithmeticRed xs ys := by
  obtain ⟨u,hu,htu⟩ := h.church_rosser
  obtain ⟨ys,eq,kids⟩ := hu.rigid_shape rigid rfl
  rw [eq] at htu
  exact ⟨ys,htu,kids⟩

/-- The computation roots already present in legacy native conversion. Bounded
addition is in Arithmetic itself, rather than an additional quotient root. -/
inductive Computes : Term → Term → Prop where
  | beta (e : Bool) (A body a : Term) :
      Computes (.app (.lam e A body) a) (body.subst (single a))
  | sub (a b : Nat) (p : Term) : b ≤ a → a < 2^64 →
      Computes (.usub (.natural a) (.natural b) p) (.natural (a-b))
  | read (count : Nat) (xs : List Term) (k : Nat) (p v : Term) : xs[k]? = some v →
      Computes (.index (.elements count xs) (.natural k) p) v
  | witnessPack (p a q : Term) : Computes (.witness (.pack p a q)) a
  | proofPack (p a q : Term) : Computes (.proof (.pack p a q)) q
  | derefBorrow (a : Term) : Computes (.node .deref [.node .borrow [a]]) a
  | borrowDeref (a : Term) : Computes (.node .borrow [.node .deref [a]]) a
  | transportRefl (f a p : Term) : Computes (.transport f (.refl a) p) p
  | ifLtTrue (m n : Nat) (yes no : Term) : m < n →
      Computes (.ifLt (.natural m) (.natural n) yes no)
        (yes.subst (single (.decide (.natural m) (.natural n))))
  | ifLtFalse (m n : Nat) (yes no : Term) : n ≤ m →
      Computes (.ifLt (.natural m) (.natural n) yes no) no
  | ifEqTrue (n : Nat) (yes no : Term) :
      Computes (.ifEq (.natural n) (.natural n) yes no)
        (yes.subst (single (.refl (.natural n))))
  | ifEqFalse (m n : Nat) (yes no : Term) : m ≠ n →
      Computes (.ifEq (.natural m) (.natural n) yes no) no

theorem Computes.toConv (h : Computes a b) : Conv a b := by
  apply Conv.legacy
  cases h with
  | beta e A body a => exact .beta e A body a
  | sub a b p hb ha => exact .sub a b p hb ha
  | read count xs k p v selected => exact .read count xs k p _ selected
  | witnessPack p a q => exact .witnessPack p _ q
  | proofPack p a q => exact .proofPack p a _
  | derefBorrow a => exact .derefBorrow _
  | borrowDeref a => exact .borrowDeref _
  | transportRefl f a p => exact .transportRefl f a _
  | ifLtTrue m n yes no h => exact .ifLtTrue m n yes no h
  | ifLtFalse m n yes no h => exact .ifLtFalse m n yes _ h
  | ifEqTrue n yes no => exact .ifEqTrue n yes no
  | ifEqFalse m n yes no h => exact .ifEqFalse m n yes _ h

/-- Genuine forward computation: ACU and bounded literal arithmetic run in
ArithmeticRed's declared directions; every legacy root contracts forward. -/
inductive MixedRed : Term → Term → Prop where
  | refl (t : Term) : MixedRed t t
  | trans : MixedRed a b → MixedRed b c → MixedRed a c
  | node (op : Op) : ListRel MixedRed xs ys → MixedRed (.node op xs) (.node op ys)
  | arithmetic : ArithmeticRed a b → MixedRed a b
  | compute : Computes a b → MixedRed a b

theorem MixedRed.toConv (h : MixedRed a b) : Conv a b := by
  induction h using MixedRed.rec
    (motive_2 := fun xs ys _ => ListRel Conv xs ys) with
  | refl => exact .refl _
  | trans _ _ ia ib => exact ia.trans ib
  | node op _ ih => exact .node op ih
  | arithmetic h => exact h.toArithmetic.toConv
  | compute h => exact h.toConv
  | nil => exact .nil
  | cons _ _ ia ib => exact .cons ia ib

private theorem listRel_lookup {k : Nat} (h : ListRel R xs ys) (selected : xs[k]? = some v) :
    ∃ w, ys[k]? = some w ∧ R v w := by
  induction h generalizing k with
  | nil => simp at selected
  | cons ha hs ih =>
      cases k with
      | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at selected; subst v; exact ⟨_,rfl,ha⟩
      | succ k => exact ih selected

/-- Every legacy root contraction can be transported past an arbitrary
arithmetic-equivalent source using forward computations. The resulting output
is arithmetic-equivalent to the original output, with no affine restriction on
bodies, arguments, proof fields, or selected elements. -/
theorem Computes.transport (root : Computes a b) (eqv : Arithmetic a a') :
    ∃ b', MixedRed a' b' ∧ Arithmetic b b' := by
  cases root with
  | beta e A body arg =>
      obtain ⟨ys,forward,kids⟩ := eqv.forward_node rfl
      obtain ⟨f',arg',rfl,hf,ha⟩ := listRel_two kids
      obtain ⟨zs,ef,inner⟩ := hf.rigid_shape rfl rfl
      obtain ⟨A',body',rfl,hA,hb⟩ := listRel_two inner
      rw [ef] at forward
      exact ⟨_,(MixedRed.arithmetic forward).trans (.compute (.beta e A' body' arg')),
        Arithmetic.instantiate hb.toArithmetic ha.toArithmetic⟩
  | sub m n p bound valid =>
      obtain ⟨ys,forward,kids⟩ := eqv.forward_node rfl
      obtain ⟨m',n',p',rfl,hm,hn,hp⟩ := listRel_three kids
      have recover := ArithmeticRed.node .usub (.cons hm.toArithmetic.recover_natural
        (.cons hn.toArithmetic.recover_natural (.cons (.refl p') .nil)))
      exact ⟨_,(MixedRed.arithmetic (forward.trans recover)).trans (.compute (.sub m n p' bound valid)),.refl _⟩
  | read count xs k p v selected =>
      obtain ⟨ys,forward,kids⟩ := eqv.forward_node rfl
      obtain ⟨es',k',p',rfl,he,hk,hp⟩ := listRel_three kids
      obtain ⟨xs',ee,inner⟩ := he.rigid_shape rfl rfl
      obtain ⟨v',selected',hv⟩ := listRel_lookup inner selected
      rw [ee] at forward
      have recover := ArithmeticRed.node .index (.cons (.refl (.elements count xs'))
        (.cons hk.toArithmetic.recover_natural (.cons (.refl p') .nil)))
      exact ⟨_,(MixedRed.arithmetic (forward.trans recover)).trans
        (.compute (.read count xs' k p' v' selected')),hv.toArithmetic⟩
  | witnessPack p a q =>
      obtain ⟨ys,forward,kids⟩ := eqv.forward_node rfl
      obtain ⟨pack',rfl,hpack⟩ := listRel_one kids
      obtain ⟨zs,ep,inner⟩ := hpack.rigid_shape rfl rfl
      obtain ⟨p',a',q',rfl,hp,ha,hq⟩ := listRel_three inner
      rw [ep] at forward
      exact ⟨_,(MixedRed.arithmetic forward).trans (.compute (.witnessPack p' a' q')),ha.toArithmetic⟩
  | proofPack p a q =>
      obtain ⟨ys,forward,kids⟩ := eqv.forward_node rfl
      obtain ⟨pack',rfl,hpack⟩ := listRel_one kids
      obtain ⟨zs,ep,inner⟩ := hpack.rigid_shape rfl rfl
      obtain ⟨p',a',q',rfl,hp,ha,hq⟩ := listRel_three inner
      rw [ep] at forward
      exact ⟨_,(MixedRed.arithmetic forward).trans (.compute (.proofPack p' a' q')),hq.toArithmetic⟩
  | derefBorrow a =>
      obtain ⟨ys,forward,kids⟩ := eqv.forward_node rfl
      obtain ⟨borrow',rfl,hborrow⟩ := listRel_one kids
      obtain ⟨zs,eb,inner⟩ := hborrow.rigid_shape rfl rfl
      obtain ⟨a',rfl,ha⟩ := listRel_one inner
      rw [eb] at forward
      exact ⟨_,(MixedRed.arithmetic forward).trans (.compute (.derefBorrow a')),ha.toArithmetic⟩
  | borrowDeref a =>
      obtain ⟨ys,forward,kids⟩ := eqv.forward_node rfl
      obtain ⟨deref',rfl,hderef⟩ := listRel_one kids
      obtain ⟨zs,ed,inner⟩ := hderef.rigid_shape rfl rfl
      obtain ⟨a',rfl,ha⟩ := listRel_one inner
      rw [ed] at forward
      exact ⟨_,(MixedRed.arithmetic forward).trans (.compute (.borrowDeref a')),ha.toArithmetic⟩
  | transportRefl f a p =>
      obtain ⟨ys,forward,kids⟩ := eqv.forward_node rfl
      obtain ⟨f',r',p',rfl,hf,hr,hp⟩ := listRel_three kids
      obtain ⟨zs,er,inner⟩ := hr.rigid_shape rfl rfl
      obtain ⟨a',rfl,ha⟩ := listRel_one inner
      rw [er] at forward
      exact ⟨_,(MixedRed.arithmetic forward).trans (.compute (.transportRefl f' a' p')),hp.toArithmetic⟩
  | ifLtTrue m n yes no bound =>
      obtain ⟨ys,forward,kids⟩ := eqv.forward_node rfl
      obtain ⟨m',n',yes',no',rfl,hm,hn,hy,hnn⟩ := listRel_four kids
      have recover := ArithmeticRed.node .ifLt (.cons hm.toArithmetic.recover_natural
        (.cons hn.toArithmetic.recover_natural (.cons (.refl yes') (.cons (.refl no') .nil))))
      exact ⟨_,(MixedRed.arithmetic (forward.trans recover)).trans (.compute (.ifLtTrue m n yes' no' bound)),
        Arithmetic.instantiate hy.toArithmetic (.refl _)⟩
  | ifLtFalse m n yes no bound =>
      obtain ⟨ys,forward,kids⟩ := eqv.forward_node rfl
      obtain ⟨m',n',yes',no',rfl,hm,hn,hy,hnn⟩ := listRel_four kids
      have recover := ArithmeticRed.node .ifLt (.cons hm.toArithmetic.recover_natural
        (.cons hn.toArithmetic.recover_natural (.cons (.refl yes') (.cons (.refl no') .nil))))
      exact ⟨_,(MixedRed.arithmetic (forward.trans recover)).trans
        (.compute (.ifLtFalse m n yes' no' bound)),hnn.toArithmetic⟩
  | ifEqTrue n yes no =>
      obtain ⟨ys,forward,kids⟩ := eqv.forward_node rfl
      obtain ⟨m',n',yes',no',rfl,hm,hn,hy,hnn⟩ := listRel_four kids
      have recover := ArithmeticRed.node .ifEq (.cons hm.toArithmetic.recover_natural
        (.cons hn.toArithmetic.recover_natural (.cons (.refl yes') (.cons (.refl no') .nil))))
      exact ⟨_,(MixedRed.arithmetic (forward.trans recover)).trans (.compute (.ifEqTrue n yes' no')),
        Arithmetic.instantiate hy.toArithmetic (.refl _)⟩
  | ifEqFalse m n yes no apart =>
      obtain ⟨ys,forward,kids⟩ := eqv.forward_node rfl
      obtain ⟨m',n',yes',no',rfl,hm,hn,hy,hnn⟩ := listRel_four kids
      have recover := ArithmeticRed.node .ifEq (.cons hm.toArithmetic.recover_natural
        (.cons hn.toArithmetic.recover_natural (.cons (.refl yes') (.cons (.refl no') .nil))))
      exact ⟨_,(MixedRed.arithmetic (forward.trans recover)).trans
        (.compute (.ifEqFalse m n yes' no' apart)),hnn.toArithmetic⟩

end Jihoo.NativeKernel.ACU
