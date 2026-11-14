import Jihoo.NativeACULegacyTransport

/-! Parallel native computation on the proved arithmetic quotient. Arithmetic
is an explicit finite relation; it is not an assumed semantic equivalence. -/
namespace Jihoo.NativeKernel.ACU

open Conversion (ListRel)

private theorem listRel_perm_left (p : xs.Perm zs) (h : ListRel R xs ys) :
    ∃ ws, ys.Perm ws ∧ ListRel R zs ws := by
  induction p generalizing ys with
  | nil => cases h; exact ⟨[],.nil,.nil⟩
  | cons x p ih =>
      cases h with
      | cons hx hs =>
          obtain ⟨ws,hp,hr⟩ := ih hs
          exact ⟨_::ws,hp.cons _,.cons hx hr⟩
  | swap x y xs =>
      cases h with
      | cons hx hs => cases hs with
        | cons hy hs => exact ⟨_,List.Perm.swap _ _ _,.cons hy (.cons hx hs)⟩
  | trans p q ip iq =>
      obtain ⟨ws,hp,hr⟩ := ip h
      obtain ⟨vs,hq,hs⟩ := iq hr
      exact ⟨vs,hp.trans hq,hs⟩

private theorem listRel_append (h : ListRel R xs ys) (k : ListRel R us vs) :
    ListRel R (xs ++ us) (ys ++ vs) := by
  induction h with
  | nil => exact k
  | cons ha hs ih => exact .cons ha ih

private theorem listRel_length (h : ListRel R xs ys) : xs.length = ys.length := by
  induction h <;> simp_all

mutual
  /-- Each displayed additive atom performs one parallel native computation;
  arbitrary arithmetic changes before and after it are retained explicitly. -/
  inductive QPar : Term → Term → Prop where
    | intro : (arithmeticFlatten a).Perm xs → ListRel QAtom xs ys →
        Arithmetic b (sumTerms ys) → QPar a b

  /-- Native parallel roots inspect constructors modulo proved Arithmetic.
  The node case follows every child, including binder and proof fields. -/
  inductive QAtom : Term → Term → Prop where
    | var (x : Nat) : QAtom (.var x) (.var x)
    | node (op : Op) : ListRel QPar xs ys → QAtom (.node op xs) (.node op ys)
    | beta (e : Bool) (A body : Term) : Arithmetic f (.lam e A body) →
        QPar body body' → QPar a a' → QAtom (.app f a) (body'.subst (single a'))
    | sub (m n : Nat) (p : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
        n ≤ m → m < 2^64 → QAtom (.usub a b p) (.natural (m-n))
    | read (count : Nat) (k : Nat) (p : Term) : Arithmetic a (.elements count xs) →
        Arithmetic index (.natural k) → ListRel QPar xs ys → ys[k]? = some v →
        QAtom (.index a index p) v
    | witnessPack (p a q : Term) : Arithmetic t (.pack p a q) → QPar a a' → QAtom (.witness t) a'
    | proofPack (p a q : Term) : Arithmetic t (.pack p a q) → QPar q q' → QAtom (.proof t) q'
    | derefBorrow (a : Term) : Arithmetic t (.node .borrow [a]) → QPar a a' →
        QAtom (.node .deref [t]) a'
    | borrowDeref (a : Term) : Arithmetic t (.node .deref [a]) → QPar a a' →
        QAtom (.node .borrow [t]) a'
    | transportRefl (a : Term) : Arithmetic eq (.refl a) → QPar p p' →
        QAtom (.transport f eq p) p'
    | ifLtTrue (m n : Nat) (no : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
        m < n → QPar yes yes' →
        QAtom (.ifLt a b yes no) (yes'.subst (single (.decide (.natural m) (.natural n))))
    | ifLtFalse (m n : Nat) (yes : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
        n ≤ m → QPar no no' → QAtom (.ifLt a b yes no) no'
    | ifEqTrue (n : Nat) (no : Term) : Arithmetic a (.natural n) → Arithmetic b (.natural n) →
        QPar yes yes' → QAtom (.ifEq a b yes no) (yes'.subst (single (.refl (.natural n))))
    | ifEqFalse (m n : Nat) (yes : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
        m ≠ n → QPar no no' → QAtom (.ifEq a b yes no) no'
end

private theorem listQAtom_replicate_one (n : Nat) :
    ListRel QAtom (List.replicate n (.natural 1)) (List.replicate n (.natural 1)) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons (.node _ .nil) ih

private theorem listQPar_refl_nil : ListRel QPar [] [] := .nil

theorem QPar.output (h : QPar a b) (eqv : Arithmetic b b') : QPar a b' := by
  cases h with
  | intro p hs out => exact .intro p hs (eqv.symm.trans out)

/-- Parallel reduction follows the binary additive constructor by concatenating
its finite atom derivations; no uniqueness of a bag ordering is assumed. -/
theorem QPar.addCong (ha : QPar a a') (hb : QPar b b') : QPar (.uadd a b) (.uadd a' b') := by
  cases ha with
  | intro pa hsa ea => cases hb with
    | intro pb hsb eb =>
        exact .intro (by simpa only [Term.uadd,arithmeticFlatten] using pa.append pb) (listRel_append hsa hsb)
          ((Arithmetic.addCong ea eb).trans (Arithmetic.sumTerms_append _ _))

/-- Parallel node congruence includes malformed arities without treating a
literal carrying children as a scalar value. -/
theorem QPar.node (op : Op) (h : ListRel QPar xs ys) : QPar (.node op xs) (.node op ys) := by
  have atom := QAtom.node op h
  have single : ListRel QAtom [.node op xs] [.node op ys] := .cons atom .nil
  have output : Arithmetic (.node op ys) (sumTerms [.node op ys]) := (Arithmetic.zero _).symm
  cases op <;> try (exact .intro (by simp only [arithmeticFlatten]; exact .refl _) single output)
  case uadd =>
    cases h with
    | nil => exact .intro (by simp only [arithmeticFlatten]; exact .refl _) single output
    | cons ha hs => cases hs with
      | nil => exact .intro (by simp only [arithmeticFlatten]; exact .refl _) single output
      | cons hb hs => cases hs with
        | nil => exact ha.addCong hb
        | cons hc hs => exact .intro (by simp only [arithmeticFlatten]; exact .refl _) single output
  case natural n =>
    cases h with
    | nil =>
        by_cases bound : n < AffineSum.wordLimit
        · exact .intro (.refl _) (by simpa only [arithmeticFlatten,bound,↓reduceIte] using listQAtom_replicate_one n)
            (Arithmetic.flatten _)
        · exact .intro (.refl _) (by simpa only [arithmeticFlatten,bound,↓reduceIte] using single)
            (Arithmetic.flatten _)
    | cons ha hs => exact .intro (by simp only [arithmeticFlatten]; exact .refl _) single output

theorem QPar.refl (t : Term) : QPar t t := by
  induction t using Term.rec (motive_2 := fun xs => ListRel QPar xs xs) with
  | var x => exact .intro (by simp only [arithmeticFlatten]; exact .refl _) (.cons (QAtom.var x) .nil) (Arithmetic.zero _).symm
  | node op xs ih => exact .node op ih
  | nil => exact .nil
  | cons x xs ix is => exact .cons ix is

theorem QPar.arithmetic (h : Arithmetic a b) : QPar a b := (QPar.refl a).output h

private theorem listArithmetic_one (h : ListRel Arithmetic [a] ys) : ∃ b, ys = [b] ∧ Arithmetic a b := by
  cases h with | cons h hs => cases hs; exact ⟨_,rfl,h⟩

private theorem listArithmetic_two (h : ListRel Arithmetic [a,b] ys) :
    ∃ a' b', ys = [a',b'] ∧ Arithmetic a a' ∧ Arithmetic b b' := by
  cases h with | cons ha hs =>
    obtain ⟨b',rfl,hb⟩ := listArithmetic_one hs
    exact ⟨_,_,rfl,ha,hb⟩

private theorem listArithmetic_three (h : ListRel Arithmetic [a,b,c] ys) :
    ∃ a' b' c', ys = [a',b',c'] ∧ Arithmetic a a' ∧ Arithmetic b b' ∧ Arithmetic c c' := by
  cases h with | cons ha hs =>
    obtain ⟨b',c',rfl,hb,hc⟩ := listArithmetic_two hs
    exact ⟨_,_,_,rfl,ha,hb,hc⟩

private theorem listArithmetic_four (h : ListRel Arithmetic [a,b,c,d] ys) :
    ∃ a' b' c' d', ys = [a',b',c',d'] ∧ Arithmetic a a' ∧ Arithmetic b b' ∧ Arithmetic c c' ∧ Arithmetic d d' := by
  cases h with | cons ha hs =>
    obtain ⟨b',c',d',rfl,hb,hc,hd⟩ := listArithmetic_three hs
    exact ⟨_,_,_,_,rfl,ha,hb,hc,hd⟩

/-- Parallel computation is well defined for every arithmetic-equivalent
representative of its source, with exactly the same displayed output. -/
theorem QPar.input (h : QPar a b) : ∀ {a'}, Arithmetic a a' → QPar a' b := by
  induction h using QPar.rec
    (motive_2 := fun x y _ => ∀ {z}, ArithmeticAtom x z → QAtom z y)
    (motive_3 := fun xs ys _ => ∀ {zs}, ListRel ArithmeticAtom xs zs → ListRel QAtom zs ys)
    (motive_4 := fun xs ys _ => ∀ {zs}, ListRel Arithmetic xs zs → ListRel QPar zs ys) with
  | intro p hs out ih =>
      intro a' eqv
      obtain ⟨zs,hp,hr⟩ := eqv.model.matching ArithmeticAtom.refl ArithmeticAtom.symm ArithmeticAtom.trans
      obtain ⟨ws,wp,wr⟩ := listRel_perm_left (hp.symm.trans p) hr
      exact .intro wp (ih wr) out
  | var x => rename_i z eqv; cases eqv; exact .var x
  | node op hs ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids => exact .node op (ih kids)
  | beta e A body view hb ha ihb iha =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨f',a',rfl,hf,haa⟩ := listArithmetic_two kids
          exact .beta e A body (hf.symm.trans view) hb (iha haa)
  | sub m n p left right bound valid =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨a',b',p',rfl,ha,hb,hp⟩ := listArithmetic_three kids
          exact .sub m n p' (ha.symm.trans left) (hb.symm.trans right) bound valid
  | read count k p arr index hs selected ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨a',i',p',rfl,ha,hi,hp⟩ := listArithmetic_three kids
          exact .read count k p' (ha.symm.trans arr) (hi.symm.trans index) hs selected
  | witnessPack p a q view ha ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨t',rfl,ht⟩ := listArithmetic_one kids
          exact .witnessPack p a q (ht.symm.trans view) ha
  | proofPack p a q view hq ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨t',rfl,ht⟩ := listArithmetic_one kids
          exact .proofPack p a q (ht.symm.trans view) hq
  | derefBorrow a view ha ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨t',rfl,ht⟩ := listArithmetic_one kids
          exact .derefBorrow a (ht.symm.trans view) ha
  | borrowDeref a view ha ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨t',rfl,ht⟩ := listArithmetic_one kids
          exact .borrowDeref a (ht.symm.trans view) ha
  | transportRefl a view hp ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨f',r',p',rfl,hf,hr,hpp⟩ := listArithmetic_three kids
          exact .transportRefl a (hr.symm.trans view) (ih hpp)
  | ifLtTrue m n no left right bound hy ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨a',b',yes',no',rfl,ha,hb,hyes,hno⟩ := listArithmetic_four kids
          exact .ifLtTrue m n no' (ha.symm.trans left) (hb.symm.trans right) bound (ih hyes)
  | ifLtFalse m n yes left right bound hn ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨a',b',yes',no',rfl,ha,hb,hyes,hno⟩ := listArithmetic_four kids
          exact .ifLtFalse m n yes' (ha.symm.trans left) (hb.symm.trans right) bound (ih hno)
  | ifEqTrue n no left right hy ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨a',b',yes',no',rfl,ha,hb,hyes,hno⟩ := listArithmetic_four kids
          exact .ifEqTrue n no' (ha.symm.trans left) (hb.symm.trans right) (ih hyes)
  | ifEqFalse m n yes left right bound hn ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨a',b',yes',no',rfl,ha,hb,hyes,hno⟩ := listArithmetic_four kids
          exact .ifEqFalse m n yes' (ha.symm.trans left) (hb.symm.trans right) bound (ih hno)
  | nil => rename_i zs hs; cases hs; exact .nil
  | cons h hs ih is => rename_i zs kids; cases kids with | cons k ks => exact .cons (ih k) (is ks)
  | _ =>
      rename_i zs kids
      cases kids
      all_goals first
        | exact .nil
        | rename_i k ks; exact .cons (by apply_assumption; exact k) (by apply_assumption; exact ks)

theorem QPar.sumTerms (h : ListRel QPar xs ys) : QPar (ACU.sumTerms xs) (ACU.sumTerms ys) := by
  induction h with
  | nil => exact .refl _
  | cons h hs ih => exact h.addCong ih

theorem QPar.ofAtom (h : QAtom a b) (atomic : arithmeticFlatten a = [a]) : QPar a b :=
   .intro (by simpa only [atomic] using List.Perm.refl [a]) (.cons h .nil) (Arithmetic.zero _).symm

private theorem rename_sumTerms (xs : List Term) (ρ : Nat → Nat) :
    (sumTerms xs).rename ρ = sumTerms (xs.map (Term.rename ρ)) := by
  induction xs with
  | nil => simp only [sumTerms,List.map_nil,Term.rename,renameArgs]
  | cons x xs ih => simp only [sumTerms,Term.rename,renameArgs,Op.binders,liftRenaming,List.map_cons,ih]

private theorem subst_sumTerms (xs : List Term) (σ : Nat → Term) :
    (sumTerms xs).subst σ = sumTerms (xs.map (Term.subst σ)) := by
  induction xs with
  | nil => simp only [sumTerms,List.map_nil,Term.subst,substArgs]
  | cons x xs ih => simp only [sumTerms,Term.subst,substArgs,Op.binders,liftSub,List.map_cons,ih]

private theorem rename_natural (h : Arithmetic a (.natural n)) (ρ : Nat → Nat) :
    Arithmetic (a.rename ρ) (.natural n) := by
  simpa only [Term.rename,renameArgs] using h.renaming ρ

/-- Quotient parallel computation is stable under capture-safe renaming. -/
theorem QPar.renaming (h : QPar a b) (ρ : Nat → Nat) : QPar (a.rename ρ) (b.rename ρ) := by
  induction h using QPar.rec
    (motive_2 := fun x y _ => ∀ ρ, QPar (x.rename ρ) (y.rename ρ))
    (motive_3 := fun xs ys _ => ∀ ρ, ListRel QPar (xs.map (Term.rename ρ)) (ys.map (Term.rename ρ)))
    (motive_4 := fun xs ys _ => ∀ op offset ρ,
      ListRel QPar (renameArgs op ρ offset xs) (renameArgs op ρ offset ys)) generalizing ρ with
  | intro p hs out ih =>
      have input := ((Arithmetic.flatten _).trans (Arithmetic.sumTerms_perm p)).renaming ρ
      have output := out.renaming ρ
      rw [rename_sumTerms] at input output
      exact ((QPar.sumTerms (ih ρ)).input input.symm).output output.symm
  | var x => rename_i ρ; exact .refl _
  | node op hs ih => rename_i ρ; simpa only [Term.rename] using QPar.node op (ih op 0 ρ)
  | beta e A body view hb ha ib ia =>
      rename_i ρ
      apply QPar.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming,Term.rename_instantiate] using
        QAtom.beta e (A.rename ρ) (body.rename (Indexed.liftRenaming ρ))
          (by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using view.renaming ρ)
          (ib (Indexed.liftRenaming ρ)) (ia ρ)
  | sub m n p left right bound valid =>
      rename_i ρ
      apply QPar.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        QAtom.sub m n (p.rename ρ) (rename_natural left ρ) (rename_natural right ρ) bound valid
  | read count k p arr index hs selected ih =>
      rename_i ρ
      apply QPar.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        QAtom.read count k (p.rename ρ) (by simpa only [Term.rename,Conversion.renameArgs_elements] using arr.renaming ρ)
          (rename_natural index ρ) (by simpa only [Conversion.renameArgs_elements] using ih (.elements count) 0 ρ)
          (by simp only [List.getElem?_map,selected,Option.map_some])
  | witnessPack p a q view ha ih =>
      rename_i ρ
      apply QPar.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        QAtom.witnessPack (p.rename ρ) (a.rename ρ) (q.rename ρ)
          (by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using view.renaming ρ) (ih ρ)
  | proofPack p a q view ha ih =>
      rename_i ρ
      apply QPar.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        QAtom.proofPack (p.rename ρ) (a.rename ρ) (q.rename ρ)
          (by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using view.renaming ρ) (ih ρ)
  | derefBorrow a view ha ih =>
      rename_i ρ
      apply QPar.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        QAtom.derefBorrow (a.rename ρ)
          (by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using view.renaming ρ) (ih ρ)
  | borrowDeref a view ha ih =>
      rename_i ρ
      apply QPar.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        QAtom.borrowDeref (a.rename ρ)
          (by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using view.renaming ρ) (ih ρ)
  | transportRefl a view hp ih =>
      rename_i ρ
      apply QPar.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        QAtom.transportRefl (a.rename ρ)
          (by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using view.renaming ρ) (ih ρ)
  | ifLtTrue m n no left right bound hy ih =>
      rename_i ρ
      apply QPar.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming,Term.rename_instantiate] using
        QAtom.ifLtTrue m n (no.rename ρ) (rename_natural left ρ) (rename_natural right ρ) bound (ih (Indexed.liftRenaming ρ))
  | ifLtFalse m n yes left right bound hn ih =>
      rename_i ρ
      apply QPar.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        QAtom.ifLtFalse m n (yes.rename (Indexed.liftRenaming ρ)) (rename_natural left ρ) (rename_natural right ρ) bound (ih ρ)
  | ifEqTrue n no left right hy ih =>
      rename_i ρ
      apply QPar.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming,Term.rename_instantiate] using
        QAtom.ifEqTrue n (no.rename ρ) (rename_natural left ρ) (rename_natural right ρ) (ih (Indexed.liftRenaming ρ))
  | ifEqFalse m n yes left right bound hn ih =>
      rename_i ρ
      apply QPar.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        QAtom.ifEqFalse m n (yes.rename (Indexed.liftRenaming ρ)) (rename_natural left ρ) (rename_natural right ρ) bound (ih ρ)
  | nil => rename_i ρ; exact .nil
  | cons h hs ih is => rename_i ρ; exact .cons (ih ρ) (is ρ)
  | _ =>
      rename_i op
      intro offset ρ
      simp only [renameArgs]
      first
        | exact .nil
        | apply ListRel.cons
          · apply_assumption
          · apply_assumption

private theorem lift_qpar {σ τ : Nat → Term} (h : ∀ x, QPar (σ x) (τ x)) (n : Nat) :
    ∀ x, QPar (liftSub n σ x) (liftSub n τ x) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro x
      cases x with
      | zero => exact .refl _
      | succ x => exact (ih x).renaming Nat.succ

private theorem subst_natural (h : Arithmetic a (.natural n)) (σ : Nat → Term) :
    Arithmetic (a.subst σ) (.natural n) := by
  simpa only [Term.subst,substArgs] using h.substitution σ

/-- Joint parallel substitution on all native terms, with lifted substitutions
at every binding edge. No affine-fragment substitution premise is used. -/
theorem QPar.substitution {σ τ : Nat → Term} (h : QPar a b) (hσ : ∀ x, QPar (σ x) (τ x)) :
    QPar (a.subst σ) (b.subst τ) := by
  induction h using QPar.rec
    (motive_2 := fun x y _ => ∀ σ τ, (∀ i, QPar (σ i) (τ i)) → QPar (x.subst σ) (y.subst τ))
    (motive_3 := fun xs ys _ => ∀ σ τ, (∀ i, QPar (σ i) (τ i)) →
      ListRel QPar (xs.map (Term.subst σ)) (ys.map (Term.subst τ)))
    (motive_4 := fun xs ys _ => ∀ op offset σ τ, (∀ i, QPar (σ i) (τ i)) →
      ListRel QPar (substArgs op σ offset xs) (substArgs op τ offset ys)) generalizing σ τ with
  | intro p hs out ih =>
      have input := ((Arithmetic.flatten _).trans (Arithmetic.sumTerms_perm p)).substitution σ
      have output := out.substitution τ
      rw [subst_sumTerms] at input output
      exact ((QPar.sumTerms (ih σ τ hσ)).input input.symm).output output.symm
  | var x => rename_i σ τ hσ; simpa only [Term.subst] using hσ x
  | node op hs ih => rename_i σ τ hσ; simpa only [Term.subst] using QPar.node op (ih op 0 σ τ hσ)
  | beta e A body view hb ha ib ia =>
      rename_i σ τ hσ
      apply QPar.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub,Term.subst_instantiate] using
        QAtom.beta e (A.subst σ) (body.subst (liftSubOne σ))
          (by simpa only [Term.subst,substArgs,Op.binders,liftSub] using view.substitution σ)
          (ib (lift_qpar hσ 1)) (ia hσ)
  | sub m n p left right bound valid =>
      rename_i σ τ hσ
      apply QPar.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        QAtom.sub m n (p.subst σ) (subst_natural left σ) (subst_natural right σ) bound valid
  | read count k p arr index hs selected ih =>
      rename_i σ τ hσ
      apply QPar.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        QAtom.read count k (p.subst σ) (by simpa only [Term.subst,Conversion.substArgs_elements] using arr.substitution σ)
          (subst_natural index σ) (by simpa only [Conversion.substArgs_elements] using ih (.elements count) 0 σ τ hσ)
          (by simp only [List.getElem?_map,selected,Option.map_some])
  | witnessPack p a q view ha ih =>
      rename_i σ τ hσ
      apply QPar.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        QAtom.witnessPack (p.subst σ) (a.subst σ) (q.subst σ)
          (by simpa only [Term.subst,substArgs,Op.binders,liftSub] using view.substitution σ) (ih hσ)
  | proofPack p a q view ha ih =>
      rename_i σ τ hσ
      apply QPar.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        QAtom.proofPack (p.subst σ) (a.subst σ) (q.subst σ)
          (by simpa only [Term.subst,substArgs,Op.binders,liftSub] using view.substitution σ) (ih hσ)
  | derefBorrow a view ha ih =>
      rename_i σ τ hσ
      apply QPar.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        QAtom.derefBorrow (a.subst σ)
          (by simpa only [Term.subst,substArgs,Op.binders,liftSub] using view.substitution σ) (ih hσ)
  | borrowDeref a view ha ih =>
      rename_i σ τ hσ
      apply QPar.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        QAtom.borrowDeref (a.subst σ)
          (by simpa only [Term.subst,substArgs,Op.binders,liftSub] using view.substitution σ) (ih hσ)
  | transportRefl a view hp ih =>
      rename_i σ τ hσ
      apply QPar.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        QAtom.transportRefl (a.subst σ)
          (by simpa only [Term.subst,substArgs,Op.binders,liftSub] using view.substitution σ) (ih hσ)
  | ifLtTrue m n no left right bound hy ih =>
      rename_i σ τ hσ
      apply QPar.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub,Term.subst_instantiate] using
        QAtom.ifLtTrue m n (no.subst σ) (subst_natural left σ) (subst_natural right σ) bound (ih (lift_qpar hσ 1))
  | ifLtFalse m n yes left right bound hn ih =>
      rename_i σ τ hσ
      apply QPar.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        QAtom.ifLtFalse m n (yes.subst (liftSubOne σ)) (subst_natural left σ) (subst_natural right σ) bound (ih hσ)
  | ifEqTrue n no left right hy ih =>
      rename_i σ τ hσ
      apply QPar.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub,Term.subst_instantiate] using
        QAtom.ifEqTrue n (no.subst σ) (subst_natural left σ) (subst_natural right σ) (ih (lift_qpar hσ 1))
  | ifEqFalse m n yes left right bound hn ih =>
      rename_i σ τ hσ
      apply QPar.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        QAtom.ifEqFalse m n (yes.subst (liftSubOne σ)) (subst_natural left σ) (subst_natural right σ) bound (ih hσ)
  | nil => rename_i σ τ hσ; exact .nil
  | cons h hs ih is => rename_i σ τ hσ; exact .cons (ih σ τ hσ) (is σ τ hσ)
  | _ =>
      rename_i op offset σ
      intro τ hσ
      simp only [substArgs]
      first
        | exact .nil
        | apply ListRel.cons
          · apply_assumption; exact lift_qpar hσ _
          · apply_assumption; exact hσ

theorem QPar.instantiate (hb : QPar body body') (ha : QPar a a') :
    QPar (body.subst (single a)) (body'.subst (single a')) := by
  apply hb.substitution
  intro x
  cases x with
  | zero => exact ha
  | succ x => exact .refl _

private theorem listConv_sumTerms (h : ListRel Conv xs ys) : Conv (sumTerms xs) (sumTerms ys) := by
  induction h with
  | nil => exact .refl _
  | cons h hs ih => exact h.addCong ih

private theorem conv_instantiate (hb : Conv body body') (ha : Conv a a') :
    Conv (body.subst (single a)) (body'.subst (single a')) :=
  (hb.substitution (single a)).trans (Conv.instantiate_congr body' ha)

/-- Every quotient parallel derivation translates to the actual ACU.Conv
relation containing the legacy rules. No model reflection premise is used. -/
theorem QPar.toConv (h : QPar a b) : Conv a b := by
  induction h using QPar.rec
    (motive_2 := fun a b _ => Conv a b)
    (motive_3 := fun xs ys _ => ListRel Conv xs ys)
    (motive_4 := fun xs ys _ => ListRel Conv xs ys) with
  | intro p hs out ih =>
      exact (((Arithmetic.flatten _).trans (Arithmetic.sumTerms_perm p)).toConv.trans
        (listConv_sumTerms ih)).trans out.toConv.symm
  | var x => exact .refl _
  | node op hs ih => exact .node op ih
  | beta e A body view hb ha ib ia =>
      exact (Conv.node .app (.cons view.toConv (.cons (.refl _) .nil))).trans
        ((Conv.legacy (.beta e A body _)).trans (conv_instantiate ib ia))
  | sub m n p left right bound valid =>
      exact (Conv.node .usub (.cons left.toConv (.cons right.toConv (.cons (.refl _) .nil)))).trans
        (.legacy (.sub m n p bound valid))
  | read count k p arr index hs selected ih =>
      exact (Conv.node .index (.cons (arr.toConv.trans (.node (.elements count) ih))
        (.cons index.toConv (.cons (.refl _) .nil)))).trans (.legacy (.read count _ k p _ selected))
  | witnessPack p a q view ha ih =>
      exact (Conv.node .witness (.cons view.toConv .nil)).trans ((Conv.legacy (.witnessPack p a q)).trans ih)
  | proofPack p a q view ha ih =>
      exact (Conv.node .proof (.cons view.toConv .nil)).trans ((Conv.legacy (.proofPack p a q)).trans ih)
  | derefBorrow a view ha ih =>
      exact (Conv.node .deref (.cons view.toConv .nil)).trans ((Conv.legacy (.derefBorrow a)).trans ih)
  | borrowDeref a view ha ih =>
      exact (Conv.node .borrow (.cons view.toConv .nil)).trans ((Conv.legacy (.borrowDeref a)).trans ih)
  | transportRefl a view hp ih =>
      exact (Conv.node .transport (.cons (.refl _) (.cons view.toConv (.cons (.refl _) .nil)))).trans
        ((Conv.legacy (.transportRefl _ a _)).trans ih)
  | ifLtTrue m n no left right bound hy ih =>
      exact (Conv.node .ifLt (.cons left.toConv (.cons right.toConv (.cons (.refl _) (.cons (.refl _) .nil))))).trans
        ((Conv.legacy (.ifLtTrue m n _ no bound)).trans (conv_instantiate ih (.refl _)))
  | ifLtFalse m n yes left right bound hn ih =>
      exact (Conv.node .ifLt (.cons left.toConv (.cons right.toConv (.cons (.refl _) (.cons (.refl _) .nil))))).trans
        ((Conv.legacy (.ifLtFalse m n yes _ bound)).trans ih)
  | ifEqTrue n no left right hy ih =>
      exact (Conv.node .ifEq (.cons left.toConv (.cons right.toConv (.cons (.refl _) (.cons (.refl _) .nil))))).trans
        ((Conv.legacy (.ifEqTrue n _ no)).trans (conv_instantiate ih (.refl _)))
  | ifEqFalse m n yes left right bound hn ih =>
      exact (Conv.node .ifEq (.cons left.toConv (.cons right.toConv (.cons (.refl _) (.cons (.refl _) .nil))))).trans
        ((Conv.legacy (.ifEqFalse m n yes _ bound)).trans ih)
  | nil => exact .nil
  | cons h hs ih is => exact .cons ih is
  | _ => first | exact .nil | apply ListRel.cons <;> assumption

end Jihoo.NativeKernel.ACU
