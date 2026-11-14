import Jihoo.NativeACUParallel

/-! A finite induction measure for computation modulo native additive ACU. -/
namespace Jihoo.NativeKernel.ACU

open Conversion (ListRel)

/-- Additive units have zero weight; valid literal payloads contribute their
finite number of units. Non-additive syntax contributes one per constructor.
The measure is a proof device and never allocates unary literal lists. -/
def weight : Term → Nat
  | .var _ => 1
  | .node .uadd [a,b] => weight a + weight b
  | .node (.natural n) [] => if n < AffineSum.wordLimit then n else 1
  | .node _ xs => 1 + (xs.map weight).sum

/-- Every arithmetic equation preserves the induction measure, including
bounded folding and arbitrary changes beneath binders or proof fields. -/
theorem Arithmetic.weight_eq (h : Arithmetic a b) : weight a = weight b := by
  induction h using Arithmetic.rec
    (motive_2 := fun xs ys _ => (xs.map weight).sum = (ys.map weight).sum) with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ia ib => exact ia.trans ib
  | node op kids ih =>
      cases op <;> try (simpa only [weight] using congrArg (1+·) ih)
      case uadd =>
        cases kids with
        | nil => rfl
        | cons ha hs => cases hs with
          | nil => simpa only [weight] using congrArg (1+·) ih
          | cons hb hs => cases hs with
            | nil => simpa only [weight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using ih
            | cons hc hs => simpa only [weight] using congrArg (1+·) ih
      case natural n => cases kids with
        | nil => rfl
        | cons ha hs => simpa only [weight] using congrArg (1+·) ih
  | assoc => simp only [weight,Nat.add_assoc]
  | comm => simp only [weight,Nat.add_comm]
  | zero =>
      have bound : 0 < AffineSum.wordLimit := by decide
      simp only [weight,bound,↓reduceIte,Nat.add_zero]
  | add m n bound =>
      have hm : m < AffineSum.wordLimit := by omega
      have hn : n < AffineSum.wordLimit := by omega
      simp only [weight,hm,hn,bound,↓reduceIte]
  | nil => rfl
  | cons h hs ih is => simp only [List.map_cons,List.sum_cons,ih,is]

private theorem replica_weight (n : Nat) :
    ((List.replicate n (.node (.natural 1) [])).map weight).sum = n := by
  have bound : 1 < AffineSum.wordLimit := by decide
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.map_cons,List.sum_cons,weight,bound,↓reduceIte,ih]; omega

theorem weight_flatten (t : Term) : (arithmeticFlatten t |>.map weight).sum = weight t := by
  fun_induction arithmeticFlatten t with
  | case1 a b ia ib => simp only [List.map_append,List.sum_append,weight,ia,ib]
  | case2 n bound => simpa only [arithmeticFlatten,bound,↓reduceIte,weight] using replica_weight n
  | case3 n bound => simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  | case4 t h₁ h₂ => simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]

/-- Flattened atoms never retain an additive binary head. -/
def NonAddAtom : Term → Prop
  | .node .uadd [_,_] => False
  | _ => True

theorem flatten_nonadd (h : a ∈ arithmeticFlatten t) : NonAddAtom a := by
  fun_induction arithmeticFlatten t with
  | case1 x y ix iy =>
      simp only [List.mem_append] at h
      rcases h with hx | hy
      · exact ix hx
      · exact iy hy
  | case2 n bound => obtain ⟨_,rfl⟩ := List.mem_replicate.mp h; trivial
  | case3 n bound => simp only [List.mem_singleton] at h; subst a; trivial
  | case4 t h₁ h₂ =>
      simp only [List.mem_singleton] at h
      subst a
      cases t with
      | var => trivial
      | node op xs =>
          cases op <;> try trivial
          case uadd =>
            cases xs with
            | nil => trivial
            | cons x xs => cases xs with
              | nil => trivial
              | cons y xs => cases xs with
                | nil => exact False.elim (h₁ x y rfl)
                | cons => trivial

private theorem sum_member_le {ns : List Nat} {n : Nat} (h : n ∈ ns) : n ≤ ns.sum := by
  induction ns with
  | nil => simp at h
  | cons m ns ih =>
      simp only [List.mem_cons] at h
      simp only [List.sum_cons]
      rcases h with rfl | h
      · omega
      · have := ih h; omega

theorem weight_atom_le (h : a ∈ arithmeticFlatten t) : weight a ≤ weight t := by
  rw [← weight_flatten t]
  exact sum_member_le (by exact List.mem_map.mpr ⟨a,h,rfl⟩)

private theorem weight_child (atomic : NonAddAtom (.node op xs)) (h : x ∈ xs) :
    weight x < weight (.node op xs) := by
  have le : weight x ≤ (xs.map weight).sum := sum_member_le (List.mem_map.mpr ⟨x,h,rfl⟩)
  have lt : weight x < 1 + (xs.map weight).sum := by omega
  cases op <;> try (simpa only [weight] using lt)
  case natural n =>
    cases xs with
    | nil => simp at h
    | cons a xs => simpa only [weight] using lt
  case uadd =>
    cases xs with
    | nil => simp at h
    | cons a xs => cases xs with
      | nil => simpa only [weight] using lt
      | cons b xs => cases xs with
        | nil => exact False.elim atomic
        | cons c xs => simpa only [weight] using lt

private theorem arithmeticRigid_flatten (hr : arithmeticRigid op = true) (xs : List Term) :
    arithmeticFlatten (.node op xs) = [.node op xs] := by
  cases op <;> simp_all only [arithmeticRigid,Bool.false_eq_true,arithmeticFlatten]

private theorem list_one (h : ListRel R [a] ys) : ∃ b, ys = [b] ∧ R a b := by
  cases h with | cons h hs => cases hs; exact ⟨_,rfl,h⟩

private theorem list_two (h : ListRel R [a,b] ys) : ∃ a' b', ys = [a',b'] ∧ R a a' ∧ R b b' := by
  cases h with | cons ha hs =>
    obtain ⟨b',rfl,hb⟩ := list_one hs
    exact ⟨_,_,rfl,ha,hb⟩

private theorem list_three (h : ListRel R [a,b,c] ys) :
    ∃ a' b' c', ys = [a',b',c'] ∧ R a a' ∧ R b b' ∧ R c c' := by
  cases h with | cons ha hs =>
    obtain ⟨b',c',rfl,hb,hc⟩ := list_two hs
    exact ⟨_,_,_,rfl,ha,hb,hc⟩

private theorem list_four (h : ListRel R [a,b,c,d] ys) :
    ∃ a' b' c' d', ys = [a',b',c',d'] ∧ R a a' ∧ R b b' ∧ R c c' ∧ R d d' := by
  cases h with | cons ha hs =>
    obtain ⟨b',c',d',rfl,hb,hc,hd⟩ := list_three hs
    exact ⟨_,_,_,_,rfl,ha,hb,hc,hd⟩

theorem QPar.atom_view (h : QPar a b) (atomic : arithmeticFlatten a = [a]) :
    ∃ c, QAtom a c ∧ Arithmetic b c := by
  cases h with
  | intro p hs out =>
      rw [atomic] at p
      have ep : _ = [a] := (List.singleton_perm.mp p).symm
      rw [ep] at hs
      obtain ⟨c,rfl,hc⟩ := list_one hs
      exact ⟨c,hc,out.trans (.zero c)⟩

private theorem QPar.lam_inv (h : QPar (.lam e A body) t) :
    ∃ A' body', Arithmetic t (.lam e A' body') ∧ QPar A A' ∧ QPar body body' := by
  obtain ⟨c,hc,out⟩ := h.atom_view (by simp only [arithmeticFlatten])
  cases hc with
  | node op kids =>
      obtain ⟨A',body',rfl,hA,hbody⟩ := list_two kids
      exact ⟨A',body',out,hA,hbody⟩

private theorem QPar.elements_inv (h : QPar (.elements count xs) t) :
    ∃ ys, Arithmetic t (.elements count ys) ∧ ListRel QPar xs ys := by
  obtain ⟨c,hc,out⟩ := h.atom_view (by simp only [arithmeticFlatten])
  cases hc with
  | node op kids => exact ⟨_,out,kids⟩

private theorem QPar.pack_inv (h : QPar (.pack p a q) t) :
    ∃ p' a' q', Arithmetic t (.pack p' a' q') ∧ QPar p p' ∧ QPar a a' ∧ QPar q q' := by
  obtain ⟨c,hc,out⟩ := h.atom_view (by simp only [arithmeticFlatten])
  cases hc with
  | node op kids =>
      obtain ⟨p',a',q',rfl,hp,ha,hq⟩ := list_three kids
      exact ⟨_,_,_,out,hp,ha,hq⟩

private theorem QPar.refl_inv (h : QPar (.refl a) t) :
    ∃ a', Arithmetic t (.refl a') ∧ QPar a a' := by
  obtain ⟨c,hc,out⟩ := h.atom_view (by simp only [arithmeticFlatten])
  cases hc with
  | node op kids =>
      obtain ⟨a',rfl,ha⟩ := list_one kids
      exact ⟨a',out,ha⟩

private theorem qatom_natural_exact (h : QAtom (.natural n) t) : t = .natural n := by
  cases h with | node op hs => cases hs; rfl

private theorem qatom_replicas_exact (h : ListRel QAtom (List.replicate n (.natural 1)) xs) :
    xs = List.replicate n (.natural 1) := by
  induction n generalizing xs with
  | zero => cases h; rfl
  | succ n ih => cases h with | cons ha hs => rw [qatom_natural_exact ha,ih hs]; rfl

theorem QPar.natural_inv (h : QPar (.natural n) t) : Arithmetic t (.natural n) := by
  cases h with
  | intro p hs out =>
      by_cases bound : n < AffineSum.wordLimit
      · simp only [arithmeticFlatten,bound,↓reduceIte] at p
        have ep := List.perm_replicate.mp p.symm
        rw [ep] at hs
        have es := qatom_replicas_exact hs
        rw [es] at out
        exact out.trans (Arithmetic.literal_ones n bound).symm
      · simp only [arithmeticFlatten,bound,↓reduceIte] at p
        have ep := (List.singleton_perm.mp p).symm
        rw [ep] at hs
        obtain ⟨c,rfl,hc⟩ := list_one hs
        have ec := qatom_natural_exact hc
        rw [ec] at out
        exact out.trans (.zero _)

private theorem QPar.borrow_inv (h : QPar (.node .borrow [a]) t) :
    (∃ a', Arithmetic t (.node .borrow [a']) ∧ QPar a a') ∨
    (∃ b b', Arithmetic a (.node .deref [b]) ∧ QPar b b' ∧ Arithmetic t b') := by
  obtain ⟨c,hc,out⟩ := h.atom_view (by simp only [arithmeticFlatten])
  cases hc with
  | node op kids =>
      obtain ⟨a',rfl,ha⟩ := list_one kids
      exact .inl ⟨a',out,ha⟩
  | borrowDeref b view hb => exact .inr ⟨b,_,view,hb,out⟩

private theorem QPar.deref_inv (h : QPar (.node .deref [a]) t) :
    (∃ a', Arithmetic t (.node .deref [a']) ∧ QPar a a') ∨
    (∃ b b', Arithmetic a (.node .borrow [b]) ∧ QPar b b' ∧ Arithmetic t b') := by
  obtain ⟨c,hc,out⟩ := h.atom_view (by simp only [arithmeticFlatten])
  cases hc with
  | node op kids =>
      obtain ⟨a',rfl,ha⟩ := list_one kids
      exact .inl ⟨a',out,ha⟩
  | derefBorrow b view hb => exact .inr ⟨b,_,view,hb,out⟩

theorem Arithmetic.head_fields (h : Arithmetic (.node op xs) (.node op' ys))
    (left : arithmeticRigid op = true) (right : arithmeticRigid op' = true) :
    op = op' ∧ ListRel Arithmetic xs ys :=
  h.rigid_node_injective (arithmeticRigid_flatten left xs) (arithmeticRigid_flatten right ys)

private theorem observed_child_lt (view : Arithmetic t (.node op xs))
    (atomic : NonAddAtom (.node op xs)) (h : x ∈ xs) : weight x < weight t := by
  rw [view.weight_eq]
  exact weight_child atomic h

private theorem listQPar_input (eqv : ListRel Arithmetic xs ys) (h : ListRel QPar ys zs) : ListRel QPar xs zs := by
  induction eqv generalizing zs with
  | nil => cases h; exact .nil
  | cons e es ih => cases h with | cons h hs => exact .cons (h.input e.symm) (ih hs)

private theorem list_lookup {k : Nat} (h : ListRel R xs ys) (selected : xs[k]? = some v) :
    ∃ w, ys[k]? = some w ∧ R v w := by
  induction h generalizing k with
  | nil => simp at selected
  | cons ha hs ih =>
      cases k with
      | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at selected; subst v; exact ⟨_,rfl,ha⟩
      | succ k => exact ih selected

private def DiamondAt (t : Term) : Prop := ∀ u v, QPar t u → QPar t v → ∃ w, QPar u w ∧ QPar v w

private theorem list_parallel_join (hu : ListRel QPar xs ys) (hv : ListRel QPar xs zs)
    (ih : ∀ t ∈ xs, DiamondAt t) : ∃ ws, ListRel QPar ys ws ∧ ListRel QPar zs ws := by
  induction hu generalizing zs with
  | nil => cases hv; exact ⟨[],.nil,.nil⟩
  | cons hh hs rec => cases hv with
    | cons kh ks =>
        obtain ⟨w,hw,kw⟩ := ih _ (by simp) _ _ hh kh
        obtain ⟨ws,hws,kws⟩ := rec ks (fun t ht => ih t (by simp [ht]))
        exact ⟨w::ws,.cons hw hws,.cons kw kws⟩

private inductive QRoot : Term → Term → Prop where
  | beta (e : Bool) (A body : Term) : Arithmetic f (.lam e A body) →
      QPar body body' → QPar a a' → QRoot (.app f a) (body'.subst (single a'))
  | sub (m n : Nat) (p : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
      n ≤ m → m < 2^64 → QRoot (.usub a b p) (.natural (m-n))
  | read (count : Nat) (k : Nat) (p : Term) : Arithmetic a (.elements count xs) →
      Arithmetic index (.natural k) → ListRel QPar xs ys → ys[k]? = some v →
      QRoot (.index a index p) v
  | witnessPack (p a q : Term) : Arithmetic t (.pack p a q) → QPar a a' → QRoot (.witness t) a'
  | proofPack (p a q : Term) : Arithmetic t (.pack p a q) → QPar q q' → QRoot (.proof t) q'
  | derefBorrow (a : Term) : Arithmetic t (.node .borrow [a]) → QPar a a' →
      QRoot (.node .deref [t]) a'
  | borrowDeref (a : Term) : Arithmetic t (.node .deref [a]) → QPar a a' →
      QRoot (.node .borrow [t]) a'
  | transportRefl (a : Term) : Arithmetic eq (.refl a) → QPar p p' →
      QRoot (.transport f eq p) p'
  | ifLtTrue (m n : Nat) (no : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
      m < n → QPar yes yes' →
      QRoot (.ifLt a b yes no) (yes'.subst (single (.decide (.natural m) (.natural n))))
  | ifLtFalse (m n : Nat) (yes : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
      n ≤ m → QPar no no' → QRoot (.ifLt a b yes no) no'
  | ifEqTrue (n : Nat) (no : Term) : Arithmetic a (.natural n) → Arithmetic b (.natural n) →
      QPar yes yes' → QRoot (.ifEq a b yes no) (yes'.subst (single (.refl (.natural n))))
  | ifEqFalse (m n : Nat) (yes : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
      m ≠ n → QPar no no' → QRoot (.ifEq a b yes no) no'

private theorem QRoot.atom (h : QRoot a b) : QAtom a b := by
  cases h <;> constructor <;> assumption

private theorem QRoot.parallel (h : QRoot a b) : QPar a b := by
  apply QPar.ofAtom h.atom
  cases h <;> simp only [arithmeticFlatten]

private theorem QAtom.view (h : QAtom t u) :
    (∃ x, t = .var x ∧ u = .var x) ∨
    (∃ op xs ys, t = .node op xs ∧ u = .node op ys ∧ ListRel QPar xs ys) ∨ QRoot t u := by
  cases h with
  | var x => exact .inl ⟨x,rfl,rfl⟩
  | node op hs => exact .inr (.inl ⟨op,_,_,rfl,rfl,hs⟩)
  | _ => exact .inr (.inr (by constructor <;> assumption))

private theorem QRoot.join (root : QRoot t u)
    (ih : ∀ s, weight s < weight t → DiamondAt s) (hv : QAtom t v) :
    ∃ w, QPar u w ∧ QPar v w := by
  cases root with
  | @beta f bodyU a aU e A body view hbU haU =>
      have bf : weight f < weight (.app f a) := weight_child (by trivial) (by simp)
      have bb : weight body < weight f := observed_child_lt view (by trivial) (by simp)
      have db := ih body (by omega)
      have da := ih a (weight_child (by trivial) (by simp))
      cases hv with
      | node op hsV =>
          obtain ⟨fV,aV,rfl,hfV,haV⟩ := list_two hsV
          obtain ⟨AV,bodyV,viewV,_,hbV⟩ := (hfV.input view).lam_inv
          obtain ⟨bodyW,hbUW,hbVW⟩ := db _ _ hbU hbV
          obtain ⟨aW,haUW,haVW⟩ := da _ _ haU haV
          exact ⟨_,hbUW.instantiate haUW,(QRoot.beta e AV bodyV viewV hbVW haVW).parallel⟩
      | beta eV AV bodyV viewV hbV haV =>
          obtain ⟨es,kids⟩ := (view.symm.trans viewV).head_fields rfl rfl
          cases es
          obtain ⟨_,_,eq,hA,hbody⟩ := list_two kids
          cases eq
          obtain ⟨bodyW,hbUW,hbVW⟩ := db _ _ hbU (hbV.input hbody.symm)
          obtain ⟨aW,haUW,haVW⟩ := da _ _ haU haV
          exact ⟨_,hbUW.instantiate haUW,hbVW.instantiate haVW⟩
  | @sub a b m n p left right bound valid =>
      cases hv with
      | node op hsV =>
          obtain ⟨aV,bV,pV,rfl,haV,hbV,_⟩ := list_three hsV
          exact ⟨_,.refl _,(QRoot.sub m n pV (haV.input left).natural_inv
            (hbV.input right).natural_inv bound valid).parallel⟩
      | sub mV nV p leftV rightV boundV validV =>
          have em := (left.symm.trans leftV).natural_injective
          have en := (right.symm.trans rightV).natural_injective
          subst mV; subst nV
          exact ⟨_,.refl _,.refl _⟩
  | @read a xs index ysU u count k p arr key hsU selectedU =>
      have ba : weight a < weight (.index a index p) := weight_child (by trivial) (by simp)
      have dx : ∀ x ∈ xs, DiamondAt x := by
        intro x hx
        have bx : weight x < weight a := observed_child_lt arr (by trivial) hx
        exact ih x (by omega)
      cases hv with
      | node op hsV =>
          obtain ⟨arrV,indexV,pV,rfl,harrV,hindexV,_⟩ := list_three hsV
          obtain ⟨ysV,viewV,hysV⟩ := (harrV.input arr).elements_inv
          obtain ⟨ws,hUW,hVW⟩ := list_parallel_join hsU hysV dx
          obtain ⟨w,hw,huw⟩ := list_lookup hUW selectedU
          exact ⟨w,huw,(QRoot.read count k pV viewV (hindexV.input key).natural_inv hVW hw).parallel⟩
      | read countV kV p arrV keyV hsV selectedV =>
          have ek := (key.symm.trans keyV).natural_injective
          subst kV
          obtain ⟨ec,kids⟩ := (arr.symm.trans arrV).head_fields rfl rfl
          cases ec
          obtain ⟨ws,hUW,hVW⟩ := list_parallel_join hsU (listQPar_input kids hsV) dx
          obtain ⟨w,hw,huw⟩ := list_lookup hUW selectedU
          obtain ⟨w',hw',hvw⟩ := list_lookup hVW selectedV
          have same := Option.some.inj (hw'.symm.trans hw)
          subst w'
          exact ⟨w,huw,hvw⟩
  | @witnessPack t aU p a q view haU =>
      have bt : weight t < weight (.witness t) := weight_child (by trivial) (by simp)
      have ba : weight a < weight t := observed_child_lt view (by trivial) (by simp)
      have da := ih a (by omega)
      cases hv with
      | node op hsV =>
          obtain ⟨packV,rfl,hpackV⟩ := list_one hsV
          obtain ⟨pV,aV,qV,viewV,_,haV,_⟩ := (hpackV.input view).pack_inv
          obtain ⟨w,huw,hvw⟩ := da _ _ haU haV
          exact ⟨w,huw,(QRoot.witnessPack pV aV qV viewV hvw).parallel⟩
      | witnessPack pV aV qV viewV haV =>
          obtain ⟨_,kids⟩ := (view.symm.trans viewV).head_fields rfl rfl
          obtain ⟨_,_,_,eq,_,ea,_⟩ := list_three kids
          cases eq
          exact da _ _ haU (haV.input ea.symm)
  | @proofPack t qU p a q view hqU =>
      have bt : weight t < weight (.proof t) := weight_child (by trivial) (by simp)
      have bq : weight q < weight t := observed_child_lt view (by trivial) (by simp)
      have dq := ih q (by omega)
      cases hv with
      | node op hsV =>
          obtain ⟨packV,rfl,hpackV⟩ := list_one hsV
          obtain ⟨pV,aV,qV,viewV,_,_,hqV⟩ := (hpackV.input view).pack_inv
          obtain ⟨w,huw,hvw⟩ := dq _ _ hqU hqV
          exact ⟨w,huw,(QRoot.proofPack pV aV qV viewV hvw).parallel⟩
      | proofPack pV aV qV viewV hqV =>
          obtain ⟨_,kids⟩ := (view.symm.trans viewV).head_fields rfl rfl
          obtain ⟨_,_,_,eq,_,_,eqv⟩ := list_three kids
          cases eq
          exact dq _ _ hqU (hqV.input eqv.symm)
  | @derefBorrow t aU a view haU =>
      have bt : weight t < weight (.node .deref [t]) := weight_child (by trivial) (by simp)
      have ba : weight a < weight t := observed_child_lt view (by trivial) (by simp)
      have da := ih a (by omega)
      cases hv with
      | node op hsV =>
          obtain ⟨borrowV,rfl,hborrowV⟩ := list_one hsV
          rcases (hborrowV.input view).borrow_inv with ⟨aV,viewV,haV⟩ | ⟨b,bV,viewA,hbV,outV⟩
          · obtain ⟨w,huw,hvw⟩ := da _ _ haU haV
            exact ⟨w,huw,(QRoot.derefBorrow aV viewV hvw).parallel⟩
          · have compared : QPar a (.node .deref [bV]) :=
              (QPar.node .deref (.cons hbV .nil)).input viewA.symm
            obtain ⟨w,huw,hvw⟩ := da _ _ haU compared
            exact ⟨w,huw,hvw.input (.node .deref (.cons outV.symm .nil))⟩
      | derefBorrow aV viewV haV =>
          obtain ⟨_,kids⟩ := (view.symm.trans viewV).head_fields rfl rfl
          obtain ⟨_,eq,ea⟩ := list_one kids
          cases eq
          exact da _ _ haU (haV.input ea.symm)
  | @borrowDeref t aU a view haU =>
      have bt : weight t < weight (.node .borrow [t]) := weight_child (by trivial) (by simp)
      have ba : weight a < weight t := observed_child_lt view (by trivial) (by simp)
      have da := ih a (by omega)
      cases hv with
      | node op hsV =>
          obtain ⟨derefV,rfl,hderefV⟩ := list_one hsV
          rcases (hderefV.input view).deref_inv with ⟨aV,viewV,haV⟩ | ⟨b,bV,viewA,hbV,outV⟩
          · obtain ⟨w,huw,hvw⟩ := da _ _ haU haV
            exact ⟨w,huw,(QRoot.borrowDeref aV viewV hvw).parallel⟩
          · have compared : QPar a (.node .borrow [bV]) :=
              (QPar.node .borrow (.cons hbV .nil)).input viewA.symm
            obtain ⟨w,huw,hvw⟩ := da _ _ haU compared
            exact ⟨w,huw,hvw.input (.node .borrow (.cons outV.symm .nil))⟩
      | borrowDeref aV viewV haV =>
          obtain ⟨_,kids⟩ := (view.symm.trans viewV).head_fields rfl rfl
          obtain ⟨_,eq,ea⟩ := list_one kids
          cases eq
          exact da _ _ haU (haV.input ea.symm)
  | @transportRefl eq p pU f a view hpU =>
      have dp := ih p (weight_child (by trivial) (by simp))
      cases hv with
      | node op hsV =>
          obtain ⟨fV,eV,pV,rfl,_,heV,hpV⟩ := list_three hsV
          obtain ⟨aV,viewV,_⟩ := (heV.input view).refl_inv
          obtain ⟨w,huw,hvw⟩ := dp _ _ hpU hpV
          exact ⟨w,huw,(QRoot.transportRefl aV viewV hvw).parallel⟩
      | transportRefl aV viewV hpV => exact dp _ _ hpU hpV
  | @ifLtTrue a b yes yesU m n no left right bound hyU =>
      have dy := ih yes (weight_child (by trivial) (by simp))
      cases hv with
      | node op hsV =>
          obtain ⟨aV,bV,yesV,noV,rfl,haV,hbV,hyV,_⟩ := list_four hsV
          obtain ⟨w,huw,hvw⟩ := dy _ _ hyU hyV
          exact ⟨_,huw.instantiate (.refl _),(QRoot.ifLtTrue m n noV
            (haV.input left).natural_inv (hbV.input right).natural_inv bound hvw).parallel⟩
      | ifLtTrue mV nV no leftV rightV boundV hyV =>
          have em := (left.symm.trans leftV).natural_injective
          have en := (right.symm.trans rightV).natural_injective
          subst mV; subst nV
          obtain ⟨w,huw,hvw⟩ := dy _ _ hyU hyV
          exact ⟨_,huw.instantiate (.refl _),hvw.instantiate (.refl _)⟩
      | ifLtFalse mV nV yes leftV rightV boundV hnV =>
          have em := (left.symm.trans leftV).natural_injective
          have en := (right.symm.trans rightV).natural_injective
          omega
  | @ifLtFalse a b no noU m n yes left right bound hnU =>
      have dn := ih no (weight_child (by trivial) (by simp))
      cases hv with
      | node op hsV =>
          obtain ⟨aV,bV,yesV,noV,rfl,haV,hbV,_,hnV⟩ := list_four hsV
          obtain ⟨w,huw,hvw⟩ := dn _ _ hnU hnV
          exact ⟨w,huw,(QRoot.ifLtFalse m n yesV
            (haV.input left).natural_inv (hbV.input right).natural_inv bound hvw).parallel⟩
      | ifLtTrue mV nV no leftV rightV boundV hyV =>
          have em := (left.symm.trans leftV).natural_injective
          have en := (right.symm.trans rightV).natural_injective
          omega
      | ifLtFalse mV nV yes leftV rightV boundV hnV => exact dn _ _ hnU hnV
  | @ifEqTrue a b yes yesU n no left right hyU =>
      have dy := ih yes (weight_child (by trivial) (by simp))
      cases hv with
      | node op hsV =>
          obtain ⟨aV,bV,yesV,noV,rfl,haV,hbV,hyV,_⟩ := list_four hsV
          obtain ⟨w,huw,hvw⟩ := dy _ _ hyU hyV
          exact ⟨_,huw.instantiate (.refl _),(QRoot.ifEqTrue n noV
            (haV.input left).natural_inv (hbV.input right).natural_inv hvw).parallel⟩
      | ifEqTrue nV no leftV rightV hyV =>
          have en := (left.symm.trans leftV).natural_injective
          subst nV
          obtain ⟨w,huw,hvw⟩ := dy _ _ hyU hyV
          exact ⟨_,huw.instantiate (.refl _),hvw.instantiate (.refl _)⟩
      | ifEqFalse mV nV yes leftV rightV apartV hnV =>
          have em := (left.symm.trans leftV).natural_injective
          have en := (right.symm.trans rightV).natural_injective
          exact False.elim (apartV (by omega))
  | @ifEqFalse a b no noU m n yes left right apart hnU =>
      have dn := ih no (weight_child (by trivial) (by simp))
      cases hv with
      | node op hsV =>
          obtain ⟨aV,bV,yesV,noV,rfl,haV,hbV,_,hnV⟩ := list_four hsV
          obtain ⟨w,huw,hvw⟩ := dn _ _ hnU hnV
          exact ⟨w,huw,(QRoot.ifEqFalse m n yesV
            (haV.input left).natural_inv (hbV.input right).natural_inv apart hvw).parallel⟩
      | ifEqTrue nV no leftV rightV hyV =>
          have em := (left.symm.trans leftV).natural_injective
          have en := (right.symm.trans rightV).natural_injective
          exact False.elim (apart (by omega))
      | ifEqFalse mV nV yes leftV rightV apartV hnV => exact dn _ _ hnU hnV

private theorem atom_diamond (atomic : NonAddAtom t)
    (ih : ∀ s, weight s < weight t → DiamondAt s) (hu : QAtom t u) (hv : QAtom t v) :
    ∃ w, QPar u w ∧ QPar v w := by
  rcases hu.view with ⟨x,rfl,rfl⟩ | ⟨op,xs,ys,rfl,rfl,hsU⟩ | rootU
  · cases hv
    exact ⟨_,.refl _,.refl _⟩
  · rcases hv.view with ⟨x,hx,_⟩ | ⟨op',xs',zs,he,rfl,hsV⟩ | rootV
    · cases hx
    · cases he
      have dx : ∀ x ∈ xs, DiamondAt x := by
        intro x hx
        exact ih x (weight_child atomic hx)
      obtain ⟨ws,hUW,hVW⟩ := list_parallel_join hsU hsV dx
      exact ⟨.node op ws,QPar.node op hUW,QPar.node op hVW⟩
    · obtain ⟨w,hvw,huw⟩ := rootV.join ih (.node op hsU)
      exact ⟨w,huw,hvw⟩
  · exact rootU.join ih hv

private theorem atom_list_join (hu : ListRel QAtom xs ys) (hv : ListRel QAtom xs zs)
    (ih : ∀ x ∈ xs, ∀ u v, QAtom x u → QAtom x v → ∃ w, QPar u w ∧ QPar v w) :
    ∃ ws, ListRel QPar ys ws ∧ ListRel QPar zs ws := by
  induction hu generalizing zs with
  | nil => cases hv; exact ⟨[],.nil,.nil⟩
  | cons hh hs rec => cases hv with
    | cons kh ks =>
        obtain ⟨w,hw,kw⟩ := ih _ (by simp) _ _ hh kh
        obtain ⟨ws,hws,kws⟩ := rec ks (fun t ht => ih t (by simp [ht]))
        exact ⟨w::ws,.cons hw hws,.cons kw kws⟩

private theorem reorder_atoms (p : xs.Perm zs) (h : ListRel QAtom xs ys) :
    ∃ ws, ys.Perm ws ∧ ListRel QAtom zs ws := by
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

/-- The full native parallel calculus has a diamond modulo explicit arithmetic
ACU derivations. Legacy beta, reading, both projections, inverse borrow/deref,
transport, and every selected branch rule participate in this same theorem. -/
theorem QPar.diamond (hu : QPar t u) (hv : QPar t v) : ∃ w, QPar u w ∧ QPar v w := by
  have all : ∀ n, ∀ t, weight t = n → DiamondAt t := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro t measure u v hu hv
        cases hu with
        | intro pu hsU outU => cases hv with
          | intro pv hsV outV =>
              obtain ⟨vs,permV,hsV'⟩ := reorder_atoms (pv.symm.trans pu) hsV
              have atomJoin : ∀ x ∈ arithmeticFlatten t, ∀ a b, QAtom x a → QAtom x b → ∃ w, QPar a w ∧ QPar b w := by
                intro x hx a b ha hb
                have mem : x ∈ arithmeticFlatten t := hx
                have bound := weight_atom_le mem
                apply atom_diamond (flatten_nonadd mem) _ ha hb
                intro s hs
                exact ih (weight s) (by omega) s rfl
              obtain ⟨ws,hUW,hVW⟩ := atom_list_join hsU hsV' (fun x hx => atomJoin x (pu.mem_iff.mpr hx))
              exact ⟨ACU.sumTerms ws,(QPar.sumTerms hUW).input outU.symm,
                (QPar.sumTerms hVW).input (outV.trans (Arithmetic.sumTerms_perm permV)).symm⟩
  exact all _ t rfl u v hu hv

abbrev QStar := Conversion.Closure QPar

theorem QStar.strip (hu : QStar t u) (hv : QPar t v) : ∃ w, QPar u w ∧ QStar v w := by
  induction hu generalizing v with
  | refl => exact ⟨v,hv,.refl⟩
  | cons ht hu ih =>
      obtain ⟨z,ha,hb⟩ := ht.diamond hv
      obtain ⟨w,hw,hs⟩ := ih ha
      exact ⟨w,hw,.cons hb hs⟩

theorem QStar.confluence (hu : QStar t u) (hv : QStar t v) : ∃ w, QStar u w ∧ QStar v w := by
  induction hv generalizing u with
  | refl => exact ⟨u,.refl,hu⟩
  | cons ht hv ih =>
      obtain ⟨z,huz,htz⟩ := hu.strip ht
      obtain ⟨w,hzw,hvw⟩ := ih htz
      exact ⟨w,.cons huz hzw,hvw⟩

end Jihoo.NativeKernel.ACU
