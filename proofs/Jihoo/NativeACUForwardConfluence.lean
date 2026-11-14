import Jihoo.NativeACUFullConfluence

/-! Actual forward Church–Rosser for full native ACU conversion. Quotient
parallel derivations are realized as finite MixedRed computations, and their
remaining arithmetic endpoints are joined by the proved arithmetic CR theorem.
No reverse legacy contraction or additive zero insertion is a forward rule. -/
namespace Jihoo.NativeKernel.ACU

open Conversion (ListRel)

private theorem reorder (p : xs.Perm zs) (h : ListRel R xs ys) :
    ∃ ws, ys.Perm ws ∧ ListRel R zs ws := by
  induction p generalizing ys with
  | nil => cases h; exact ⟨[],.nil,.nil⟩
  | cons x p ih => cases h with
    | cons hx hs =>
        obtain ⟨ws,hp,hr⟩ := ih hs
        exact ⟨_::ws,hp.cons _,.cons hx hr⟩
  | swap x y xs => cases h with | cons hx hs => cases hs with
    | cons hy hs => exact ⟨_,List.Perm.swap _ _ _,.cons hy (.cons hx hs)⟩
  | trans p q ip iq =>
      obtain ⟨ws,hp,hr⟩ := ip h
      obtain ⟨vs,hq,hs⟩ := iq hr
      exact ⟨vs,hp.trans hq,hs⟩

private theorem one (h : ListRel R [a] ys) : ∃ b, ys = [b] ∧ R a b := by
  cases h with | cons h hs => cases hs; exact ⟨_,rfl,h⟩
private theorem two (h : ListRel R [a,b] ys) : ∃ a' b', ys = [a',b'] ∧ R a a' ∧ R b b' := by
  cases h with | cons ha hs =>
    obtain ⟨b',rfl,hb⟩ := one hs
    exact ⟨_,_,rfl,ha,hb⟩
private theorem three (h : ListRel R [a,b,c] ys) :
    ∃ a' b' c', ys = [a',b',c'] ∧ R a a' ∧ R b b' ∧ R c c' := by
  cases h with | cons ha hs =>
    obtain ⟨b',c',rfl,hb,hc⟩ := two hs
    exact ⟨_,_,_,rfl,ha,hb,hc⟩
private theorem four (h : ListRel R [a,b,c,d] ys) :
    ∃ a' b' c' d', ys = [a',b',c',d'] ∧ R a a' ∧ R b b' ∧ R c c' ∧ R d d' := by
  cases h with | cons ha hs =>
    obtain ⟨b',c',d',rfl,hb,hc,hd⟩ := three hs
    exact ⟨_,_,_,_,rfl,ha,hb,hc,hd⟩

private theorem lookup {k : Nat} (h : ListRel R xs ys) (selected : xs[k]? = some v) :
    ∃ w, ys[k]? = some w ∧ R v w := by
  induction h generalizing k with
  | nil => simp at selected
  | cons ha hs ih => cases k with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at selected; subst v; exact ⟨_,rfl,ha⟩
    | succ k => exact ih selected

private theorem arithmetic_sum (h : ListRel Arithmetic xs ys) : Arithmetic (sumTerms xs) (sumTerms ys) := by
  induction h with
  | nil => exact .refl _
  | cons h hs ih => exact h.addCong ih

private theorem sum_compact (xs : List Term) : Arithmetic (sumTerms xs) (compact xs) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih => cases xs with
    | nil => exact .zero x
    | cons y xs => exact .addCong (.refl x) ih

private theorem arithmetic_list (h : ListRel ArithmeticRed xs ys) : ListRel Arithmetic xs ys := by
  induction h with
  | nil => exact .nil
  | cons h hs ih => exact .cons h.toArithmetic ih

theorem MixedRed.compact_pointwise (h : ListRel MixedRed xs ys) : MixedRed (compact xs) (compact ys) := by
  induction h with
  | nil => exact .refl _
  | cons h hs ih => cases hs with
    | nil => exact h
    | cons hb hs => exact .node .uadd (.cons h (.cons ih .nil))

/-- Every quotient parallel computation has an actual forward realization up
to a proved arithmetic endpoint. The strengthened source quantifier handles
heads exposed by zero elimination, without inserting additive zeros anywhere. -/
theorem QPar.realize (h : QPar a b) : ∀ {a'}, Arithmetic a a' →
    ∃ c, MixedRed a' c ∧ Arithmetic b c := by
  induction h using QPar.rec
    (motive_2 := fun x y _ => ∀ {z}, ArithmeticAtom x z → ∃ c, MixedRed z c ∧ Arithmetic y c)
    (motive_3 := fun xs ys _ => ∀ {zs}, ListRel ArithmeticAtom xs zs →
      ∃ cs, ListRel MixedRed zs cs ∧ ListRel Arithmetic ys cs)
    (motive_4 := fun xs ys _ => ∀ {zs}, ListRel Arithmetic xs zs →
      ∃ cs, ListRel MixedRed zs cs ∧ ListRel Arithmetic ys cs) with
  | intro p hs out ih =>
      intro a' eqv
      obtain ⟨zs,hp,hr⟩ := eqv.model.matching ArithmeticAtom.refl ArithmeticAtom.symm ArithmeticAtom.trans
      obtain ⟨ws,wp,wr⟩ := reorder (hp.symm.trans p) hr
      obtain ⟨cs,hcs,ecs⟩ := ih wr
      exact ⟨compact cs,
        (MixedRed.arithmetic (ArithmeticRed.flatten a')).trans
          ((MixedRed.arithmetic (ArithmeticRed.compact_perm wp)).trans (MixedRed.compact_pointwise hcs)),
        out.trans ((arithmetic_sum ecs).trans (sum_compact cs))⟩
  | var x => rename_i z eqv; cases eqv; exact ⟨_,.refl _,.refl _⟩
  | node op hs ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨cs,hcs,ecs⟩ := ih kids
          exact ⟨_,.node op hcs,.node op ecs⟩
  | beta e A body view hb ha ib ia =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨fT,aT,rfl,hf,haa⟩ := two kids
          obtain ⟨ls,forward,inner⟩ := ((hf.symm.trans view).symm).forward_node rfl
          obtain ⟨A0,body0,rfl,hA,hbody⟩ := two inner
          obtain ⟨bodyC,hbodyC,ebodyC⟩ := ib hbody.toArithmetic
          obtain ⟨aC,haC,eaC⟩ := ia haa
          have function : MixedRed fT (.lam e A0 bodyC) :=
            (MixedRed.arithmetic forward).trans (.node (.lam e) (.cons (.refl A0) (.cons hbodyC .nil)))
          exact ⟨_,(MixedRed.node .app (.cons function (.cons haC .nil))).trans (.compute (.beta e A0 bodyC aC)),
            Arithmetic.instantiate ebodyC eaC⟩
  | sub m n p left right bound valid =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨aT,bT,pT,rfl,ha,hb,hp⟩ := three kids
          have ra := ((ha.symm.trans left).symm).recover_natural
          have rb := ((hb.symm.trans right).symm).recover_natural
          exact ⟨_,(MixedRed.node .usub (.cons (.arithmetic ra) (.cons (.arithmetic rb) (.cons (.refl pT) .nil)))).trans
            (.compute (.sub m n pT bound valid)),.refl _⟩
  | read count k p arr index hs selected ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨aT,iT,pT,rfl,ha,hi,hp⟩ := three kids
          obtain ⟨xs0,forward,inner⟩ := ((ha.symm.trans arr).symm).forward_node rfl
          obtain ⟨cs,hcs,ecs⟩ := ih (arithmetic_list inner)
          obtain ⟨c,selectedC,ec⟩ := lookup ecs selected
          have ra : MixedRed aT (.elements count cs) :=
            (MixedRed.arithmetic forward).trans (.node (.elements count) hcs)
          have rk := ((hi.symm.trans index).symm).recover_natural
          exact ⟨c,(MixedRed.node .index (.cons ra (.cons (.arithmetic rk) (.cons (.refl pT) .nil)))).trans
            (.compute (.read count cs k pT c selectedC)),ec⟩
  | witnessPack p a q view ha ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨tT,rfl,ht⟩ := one kids
          obtain ⟨xs0,forward,inner⟩ := ((ht.symm.trans view).symm).forward_node rfl
          obtain ⟨p0,a0,q0,rfl,hp,haa,hq⟩ := three inner
          obtain ⟨c,hc,ec⟩ := ih haa.toArithmetic
          exact ⟨c,((MixedRed.node .witness (.cons (.arithmetic forward) .nil)).trans
            (.compute (.witnessPack p0 a0 q0))).trans hc,ec⟩
  | proofPack p a q view hq ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨tT,rfl,ht⟩ := one kids
          obtain ⟨xs0,forward,inner⟩ := ((ht.symm.trans view).symm).forward_node rfl
          obtain ⟨p0,a0,q0,rfl,hp,ha,hqq⟩ := three inner
          obtain ⟨c,hc,ec⟩ := ih hqq.toArithmetic
          exact ⟨c,((MixedRed.node .proof (.cons (.arithmetic forward) .nil)).trans
            (.compute (.proofPack p0 a0 q0))).trans hc,ec⟩
  | derefBorrow a view ha ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨tT,rfl,ht⟩ := one kids
          obtain ⟨xs0,forward,inner⟩ := ((ht.symm.trans view).symm).forward_node rfl
          obtain ⟨a0,rfl,haa⟩ := one inner
          obtain ⟨c,hc,ec⟩ := ih haa.toArithmetic
          exact ⟨c,((MixedRed.node .deref (.cons (.arithmetic forward) .nil)).trans
            (.compute (.derefBorrow a0))).trans hc,ec⟩
  | borrowDeref a view ha ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨tT,rfl,ht⟩ := one kids
          obtain ⟨xs0,forward,inner⟩ := ((ht.symm.trans view).symm).forward_node rfl
          obtain ⟨a0,rfl,haa⟩ := one inner
          obtain ⟨c,hc,ec⟩ := ih haa.toArithmetic
          exact ⟨c,((MixedRed.node .borrow (.cons (.arithmetic forward) .nil)).trans
            (.compute (.borrowDeref a0))).trans hc,ec⟩
  | transportRefl a view hp ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨fT,rT,pT,rfl,hf,hr,hpp⟩ := three kids
          obtain ⟨xs0,forward,inner⟩ := ((hr.symm.trans view).symm).forward_node rfl
          obtain ⟨a0,rfl,haa⟩ := one inner
          obtain ⟨c,hc,ec⟩ := ih hpp
          exact ⟨c,((MixedRed.node .transport (.cons (.refl fT) (.cons (.arithmetic forward) (.cons (.refl pT) .nil)))).trans
            (.compute (.transportRefl fT a0 pT))).trans hc,ec⟩
  | ifLtTrue m n no left right bound hy ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨aT,bT,yesT,noT,rfl,ha,hb,hyes,hno⟩ := four kids
          obtain ⟨c,hc,ec⟩ := ih hyes
          have ra := ((ha.symm.trans left).symm).recover_natural
          have rb := ((hb.symm.trans right).symm).recover_natural
          exact ⟨_,(MixedRed.node .ifLt (.cons (.arithmetic ra) (.cons (.arithmetic rb) (.cons hc (.cons (.refl noT) .nil))))).trans
            (.compute (.ifLtTrue m n c noT bound)),Arithmetic.instantiate ec (.refl _)⟩
  | ifLtFalse m n yes left right bound hn ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨aT,bT,yesT,noT,rfl,ha,hb,hyes,hno⟩ := four kids
          obtain ⟨c,hc,ec⟩ := ih hno
          have ra := ((ha.symm.trans left).symm).recover_natural
          have rb := ((hb.symm.trans right).symm).recover_natural
          exact ⟨c,(MixedRed.node .ifLt (.cons (.arithmetic ra) (.cons (.arithmetic rb) (.cons (.refl yesT) (.cons hc .nil))))).trans
            (.compute (.ifLtFalse m n yesT c bound)),ec⟩
  | ifEqTrue n no left right hy ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨aT,bT,yesT,noT,rfl,ha,hb,hyes,hno⟩ := four kids
          obtain ⟨c,hc,ec⟩ := ih hyes
          have ra := ((ha.symm.trans left).symm).recover_natural
          have rb := ((hb.symm.trans right).symm).recover_natural
          exact ⟨_,(MixedRed.node .ifEq (.cons (.arithmetic ra) (.cons (.arithmetic rb) (.cons hc (.cons (.refl noT) .nil))))).trans
            (.compute (.ifEqTrue n c noT)),Arithmetic.instantiate ec (.refl _)⟩
  | ifEqFalse m n yes left right bound hn ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨aT,bT,yesT,noT,rfl,ha,hb,hyes,hno⟩ := four kids
          obtain ⟨c,hc,ec⟩ := ih hno
          have ra := ((ha.symm.trans left).symm).recover_natural
          have rb := ((hb.symm.trans right).symm).recover_natural
          exact ⟨c,(MixedRed.node .ifEq (.cons (.arithmetic ra) (.cons (.arithmetic rb) (.cons (.refl yesT) (.cons hc .nil))))).trans
            (.compute (.ifEqFalse m n yesT c bound)),ec⟩
  | nil => rename_i zs hs; cases hs; exact ⟨[],.nil,.nil⟩
  | cons h hs ih is =>
      rename_i zs kids
      cases kids with | cons k ks =>
        obtain ⟨c,hc,ec⟩ := ih k
        obtain ⟨cs,hcs,ecs⟩ := is ks
        exact ⟨c::cs,.cons hc hcs,.cons ec ecs⟩
  | _ =>
      first
        | rename_i zs kids; cases kids; exact ⟨[],.nil,.nil⟩
        | rename_i h hs ih is zs kids
          cases kids with | cons k ks =>
            obtain ⟨c,hc,ec⟩ := ih k
            obtain ⟨cs,hcs,ecs⟩ := is ks
            exact ⟨c::cs,.cons hc hcs,.cons ec ecs⟩

theorem QStar.realize (h : QStar a b) : ∀ {a'}, Arithmetic a a' →
    ∃ c, MixedRed a' c ∧ Arithmetic b c := by
  induction h with
  | refl => intro a' eqv; exact ⟨a',.refl _,eqv⟩
  | cons h hs ih =>
      intro a' eqv
      obtain ⟨c,hc,ec⟩ := h.realize eqv
      obtain ⟨d,hd,ed⟩ := ih ec
      exact ⟨d,hc.trans hd,ed⟩

/-- An actual common forward reduct using declared MixedRed rules. -/
def MixedJoin (a b : Term) : Prop := ∃ c, MixedRed a c ∧ MixedRed b c

/-- Full Church–Rosser on complete native syntax. Additive zero is eliminated
only; every legacy computation contracts forward. The conclusion is an actual
finite common reduct, with no residual quotient-equivalence endpoint. -/
theorem Conv.church_rosser (h : Conv a b) : MixedJoin a b := by
  obtain ⟨c,hc,kc⟩ := h.church_rosser_modulo_arithmetic
  obtain ⟨u,hu,eu⟩ := hc.realize (.refl _)
  obtain ⟨v,hv,ev⟩ := kc.realize (.refl _)
  obtain ⟨w,uw,vw⟩ := (eu.symm.trans ev).church_rosser
  exact ⟨w,hu.trans (.arithmetic uw),hv.trans (.arithmetic vw)⟩

theorem conv_iff_mixed_join (a b : Term) : Conv a b ↔ MixedJoin a b := by
  constructor
  · exact Conv.church_rosser
  · intro ⟨c,hc,kc⟩
    exact hc.toConv.trans kc.toConv.symm

theorem MixedRed.confluence (h : MixedRed a b) (k : MixedRed a c) : MixedJoin b c :=
  (h.toConv.symm.trans k.toConv).church_rosser

end Jihoo.NativeKernel.ACU
