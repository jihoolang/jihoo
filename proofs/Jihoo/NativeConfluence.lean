import Jihoo.NativeTyping

/-! Parallel reduction for the complete native constructor vocabulary.
Generic node congruence follows every child edge; no typing restriction is used.
The dependency on NativeTyping supplies readable Term constructor aliases only.
-/
namespace Jihoo.NativeKernel.Conversion

inductive Par : Term → Term → Prop where
  | var (x : Nat) : Par (.var x) (.var x)
  | node (op : Op) : ListRel Par xs ys → Par (.node op xs) (.node op ys)
  | beta : Par body body' → Par a a' →
      Par (.app (.lam e A body) a) (body'.subst (single a'))
  | add (a b : Nat) : a + b < 2^64 → Par (.uadd (.natural a) (.natural b)) (.natural (a+b))
  | sub (a b : Nat) (p : Term) : b ≤ a → a < 2^64 →
      Par (.usub (.natural a) (.natural b) p) (.natural (a-b))
  | read (count : Nat) (k : Nat) (p : Term) : ListRel Par xs ys → ys[k]? = some v →
      Par (.index (.elements count xs) (.natural k) p) v
  | witnessPack : Par a a' → Par (.witness (.pack p a q)) a'
  | proofPack : Par q q' → Par (.proof (.pack p a q)) q'
  | derefBorrow : Par a a' → Par (.node .deref [.node .borrow [a]]) a'
  | borrowDeref : Par a a' → Par (.node .borrow [.node .deref [a]]) a'

  | transportRefl (f a : Term) : Par p p' → Par (.transport f (.refl a) p) p'
  | ifLtTrue (m n : Nat) (no : Term) : m < n → Par yes yes' →
      Par (.ifLt (.natural m) (.natural n) yes no)
        (yes'.subst (single (.decide (.natural m) (.natural n))))
  | ifLtFalse (m n : Nat) (yes : Term) : n ≤ m → Par no no' →
      Par (.ifLt (.natural m) (.natural n) yes no) no'
  | ifEqTrue (n : Nat) (no : Term) : Par yes yes' →
      Par (.ifEq (.natural n) (.natural n) yes no) (yes'.subst (single (.refl (.natural n))))
  | ifEqFalse (m n : Nat) (yes : Term) : m ≠ n → Par no no' →
      Par (.ifEq (.natural m) (.natural n) yes no) no'

 theorem Par.refl (t : Term) : Par t t := by
  induction t using Term.rec (motive_2 := fun xs => ListRel Par xs xs) with
  | var x => exact .var x
  | node op xs ih => exact .node op ih
  | nil => exact .nil
  | cons x xs ihx ihxs => exact .cons ihx ihxs

 theorem Par.renaming (h : Par a b) (ρ : Nat → Nat) : Par (a.rename ρ) (b.rename ρ) := by
  induction h using Par.rec
    (motive_2 := fun xs ys _ => ∀ op offset ρ,
      ListRel Par (renameArgs op ρ offset xs) (renameArgs op ρ offset ys)) generalizing ρ with
  | var => simp only [Term.rename]; exact .var _
  | node op _ ih => simpa only [Term.rename] using Par.node op (ih op 0 ρ)
  | beta _ _ ihb iha =>
      simp only [Term.rename, renameArgs, Op.binders, liftRenaming, Term.rename_instantiate]
      exact .beta (ihb (Indexed.liftRenaming ρ)) (iha ρ)
  | add a b bound =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using Par.add a b bound
  | sub a b p hb ha =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using Par.sub a b (p.rename ρ) hb ha
  | read count k p hxs selected ih =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
        Par.read count k (p.rename ρ) (ih (.elements count) 0 ρ)
          (by simp [List.getElem?_map, selected])
  | witnessPack _ ih =>
      simp only [Term.rename, renameArgs, Op.binders, liftRenaming]
      exact .witnessPack (ih ρ)
  | proofPack _ ih =>
      simp only [Term.rename, renameArgs, Op.binders, liftRenaming]
      exact .proofPack (ih ρ)
  | derefBorrow _ ih =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using Par.derefBorrow (ih ρ)
  | borrowDeref _ ih =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using Par.borrowDeref (ih ρ)
  | transportRefl f a _ ih =>
      simp only [Term.rename, renameArgs, Op.binders, liftRenaming]
      exact .transportRefl (f.rename ρ) (a.rename ρ) (ih ρ)
  | ifLtTrue m n no bound _ ih =>
      simp only [Term.rename, renameArgs, Op.binders, liftRenaming, Term.rename_instantiate]
      exact .ifLtTrue m n (no.rename ρ) bound (ih (Indexed.liftRenaming ρ))
  | ifLtFalse m n yes bound _ ih =>
      simp only [Term.rename, renameArgs, Op.binders, liftRenaming]
      exact .ifLtFalse m n (yes.rename (Indexed.liftRenaming ρ)) bound (ih ρ)
  | ifEqTrue n no _ ih =>
      simp only [Term.rename, renameArgs, Op.binders, liftRenaming, Term.rename_instantiate]
      exact .ifEqTrue n (no.rename ρ) (ih (Indexed.liftRenaming ρ))
  | ifEqFalse m n yes apart _ ih =>
      simp only [Term.rename, renameArgs, Op.binders, liftRenaming]
      exact .ifEqFalse m n (yes.rename (Indexed.liftRenaming ρ)) apart (ih ρ)
  | nil => simp [renameArgs]; exact .nil
  | cons _ _ ih₁ ih₂ =>
      rename_i op offset ρ
      simp only [renameArgs]
      exact .cons (ih₁ _) (ih₂ op (offset + 1) ρ)

private theorem lift_par {σ τ : Nat → Term} (h : ∀ x, Par (σ x) (τ x)) (n : Nat) :
    ∀ x, Par (liftSub n σ x) (liftSub n τ x) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro x
      cases x with
      | zero => exact .var 0
      | succ x => exact (ih x).renaming Nat.succ

 theorem Par.substitution {σ τ : Nat → Term} (h : Par a b) (hσ : ∀ x, Par (σ x) (τ x)) :
    Par (a.subst σ) (b.subst τ) := by
  induction h using Par.rec
    (motive_2 := fun xs ys _ => ∀ op offset σ τ, (∀ x, Par (σ x) (τ x)) →
      ListRel Par (substArgs op σ offset xs) (substArgs op τ offset ys)) generalizing σ τ with
  | var x => simpa only [Term.subst] using hσ x
  | node op _ ih => simpa only [Term.subst] using Par.node op (ih op 0 σ τ hσ)
  | beta _ _ ihb iha =>
      simp only [Term.subst, substArgs, Op.binders, liftSub, Term.subst_instantiate]
      exact .beta (ihb (lift_par hσ 1)) (iha hσ)
  | add a b bound =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using Par.add a b bound
  | sub a b p hb ha =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using Par.sub a b (p.subst σ) hb ha
  | read count k p hxs selected ih =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using
        Par.read count k (p.subst σ) (ih (.elements count) 0 σ τ hσ)
          (by simp [List.getElem?_map, selected])
  | witnessPack _ ih =>
      simp only [Term.subst, substArgs, Op.binders, liftSub]
      exact .witnessPack (ih hσ)
  | proofPack _ ih =>
      simp only [Term.subst, substArgs, Op.binders, liftSub]
      exact .proofPack (ih hσ)
  | derefBorrow _ ih =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using Par.derefBorrow (ih hσ)
  | borrowDeref _ ih =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using Par.borrowDeref (ih hσ)
  | transportRefl f a _ ih =>
      simp only [Term.subst, substArgs, Op.binders, liftSub]
      exact .transportRefl (f.subst σ) (a.subst σ) (ih hσ)
  | ifLtTrue m n no bound _ ih =>
      simp only [Term.subst, substArgs, Op.binders, liftSub, Term.subst_instantiate]
      exact .ifLtTrue m n (no.subst σ) bound (ih (lift_par hσ 1))
  | ifLtFalse m n yes bound _ ih =>
      simp only [Term.subst, substArgs, Op.binders, liftSub]
      exact .ifLtFalse m n (yes.subst (liftSubOne σ)) bound (ih hσ)
  | ifEqTrue n no _ ih =>
      simp only [Term.subst, substArgs, Op.binders, liftSub, Term.subst_instantiate]
      exact .ifEqTrue n (no.subst σ) (ih (lift_par hσ 1))
  | ifEqFalse m n yes apart _ ih =>
      simp only [Term.subst, substArgs, Op.binders, liftSub]
      exact .ifEqFalse m n (yes.subst (liftSubOne σ)) apart (ih hσ)
  | nil => simp [substArgs]; exact .nil
  | cons _ _ ih₁ ih₂ =>
      rename_i op offset σ τ hσ
      simp only [substArgs]
      exact .cons (ih₁ (lift_par hσ _)) (ih₂ op (offset + 1) σ τ hσ)

 theorem Par.instantiate (hb : Par body body') (ha : Par a a') :
    Par (body.subst (single a)) (body'.subst (single a')) := by
  apply hb.substitution
  intro x
  cases x with
  | zero => exact ha
  | succ x => exact .var x

/-- Root parallel contractions, separated from generic contextual reduction. -/
inductive Root : Term → Term → Prop where
  | beta : Par body body' → Par a a' →
      Root (.app (.lam e A body) a) (body'.subst (single a'))
  | add (a b : Nat) : a + b < 2^64 → Root (.uadd (.natural a) (.natural b)) (.natural (a+b))
  | sub (a b : Nat) (p : Term) : b ≤ a → a < 2^64 →
      Root (.usub (.natural a) (.natural b) p) (.natural (a-b))
  | read (count : Nat) (k : Nat) (p : Term) : ListRel Par xs ys → ys[k]? = some v →
      Root (.index (.elements count xs) (.natural k) p) v
  | witnessPack : Par a a' → Root (.witness (.pack p a q)) a'
  | proofPack : Par q q' → Root (.proof (.pack p a q)) q'
  | derefBorrow : Par a a' → Root (.node .deref [.node .borrow [a]]) a'
  | borrowDeref : Par a a' → Root (.node .borrow [.node .deref [a]]) a'

  | transportRefl (f a : Term) : Par p p' → Root (.transport f (.refl a) p) p'
  | ifLtTrue (m n : Nat) (no : Term) : m < n → Par yes yes' →
      Root (.ifLt (.natural m) (.natural n) yes no)
        (yes'.subst (single (.decide (.natural m) (.natural n))))
  | ifLtFalse (m n : Nat) (yes : Term) : n ≤ m → Par no no' →
      Root (.ifLt (.natural m) (.natural n) yes no) no'
  | ifEqTrue (n : Nat) (no : Term) : Par yes yes' →
      Root (.ifEq (.natural n) (.natural n) yes no) (yes'.subst (single (.refl (.natural n))))
  | ifEqFalse (m n : Nat) (yes : Term) : m ≠ n → Par no no' →
      Root (.ifEq (.natural m) (.natural n) yes no) no'

theorem Root.parallel (h : Root t u) : Par t u := by
  cases h <;> constructor <;> assumption

private theorem Par.view (h : Par t u) :
    (∃ x, t = .var x ∧ u = .var x) ∨
    (∃ op xs ys, t = .node op xs ∧ u = .node op ys ∧ ListRel Par xs ys) ∨ Root t u := by
  cases h with
  | var x => exact Or.inl ⟨x, rfl, rfl⟩
  | node op hs => exact Or.inr (Or.inl ⟨op, _, _, rfl, rfl, hs⟩)
  | _ => exact Or.inr (Or.inr (by constructor <;> assumption))

private theorem ListRel.nils (h : ListRel R [] ys) : ys = [] := by cases h; rfl

private theorem ListRel.one (h : ListRel R [a] ys) : ∃ b, ys = [b] ∧ R a b := by
  cases h with
  | cons ha hs => cases hs; exact ⟨_, rfl, ha⟩

private theorem ListRel.two (h : ListRel R [a,b] ys) :
    ∃ a' b', ys = [a',b'] ∧ R a a' ∧ R b b' := by
  cases h with
  | cons ha hs =>
      cases hs with
      | cons hb hs => cases hs; exact ⟨_, _, rfl, ha, hb⟩

private theorem ListRel.three (h : ListRel R [a,b,c] ys) :
    ∃ a' b' c', ys = [a',b',c'] ∧ R a a' ∧ R b b' ∧ R c c' := by
  cases h with
  | cons ha hs =>
      cases hs with
      | cons hb hs =>
          cases hs with
          | cons hc hs => cases hs; exact ⟨_, _, _, rfl, ha, hb, hc⟩

private theorem ListRel.four (h : ListRel R [a,b,c,d] ys) :
    ∃ a' b' c' d', ys = [a',b',c',d'] ∧ R a a' ∧ R b b' ∧ R c c' ∧ R d d' := by
  cases h with
  | cons ha hs =>
      obtain ⟨b',c',d',rfl,hb,hc,hd⟩ := hs.three
      exact ⟨_,_,_,_,rfl,ha,hb,hc,hd⟩

private theorem Par.lam_inv (h : Par (.lam e A body) t) :
    ∃ A' body', t = .lam e A' body' ∧ Par A A' ∧ Par body body' := by
  cases h with
  | node op hs =>
      obtain ⟨A', body', rfl, hA, hb⟩ := hs.two
      exact ⟨A', body', rfl, hA, hb⟩

private theorem Par.elements_inv (h : Par (.elements count xs) t) :
    ∃ ys, t = .elements count ys ∧ ListRel Par xs ys := by
  cases h with
  | node op hs => exact ⟨_, rfl, hs⟩

private theorem Par.pack_inv (h : Par (.pack p a q) t) :
    ∃ p' a' q', t = .pack p' a' q' ∧ Par p p' ∧ Par a a' ∧ Par q q' := by
  cases h with
  | node op hs =>
      obtain ⟨p', a', q', rfl, hp, ha, hq⟩ := hs.three
      exact ⟨p', a', q', rfl, hp, ha, hq⟩

private theorem Par.natural_inv (h : Par (.natural n) t) : t = .natural n := by
  cases h with
  | node op hs => cases hs; rfl

private theorem ListRel.lookup_right {k : Nat} (h : ListRel R xs ys) (selected : xs[k]? = some v) :
    ∃ w, ys[k]? = some w ∧ R v w := by
  induction h generalizing k with
  | nil => simp at selected
  | cons hr hs ih =>
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
          subst v
          exact ⟨_, rfl, hr⟩
      | succ k => exact ih selected

private def DiamondAt (t : Term) : Prop :=
  ∀ u v, Par t u → Par t v → ∃ w, Par u w ∧ Par v w

private theorem ListRel.parallel_join (hu : ListRel Par xs ys) (hv : ListRel Par xs zs)
    (ih : ∀ t ∈ xs, DiamondAt t) :
    ∃ ws, ListRel Par ys ws ∧ ListRel Par zs ws := by
  induction hu generalizing zs with
  | nil => cases hv; exact ⟨[], .nil, .nil⟩
  | cons hhead htail rec =>
      cases hv with
      | cons vhead vtail =>
          obtain ⟨w, huw, hvw⟩ := ih _ (by simp) _ _ hhead vhead
          obtain ⟨ws, hus, hvs⟩ := rec vtail (fun t ht => ih t (by simp [ht]))
          exact ⟨w :: ws, .cons huw hus, .cons hvw hvs⟩

private theorem Root.join (hr : Root t u)
    (ih : ∀ s, sizeOf s < sizeOf t → DiamondAt s) (hv : Par t v) :
    ∃ w, Par u w ∧ Par v w := by
  cases hr with
  | @beta body bodyU a aU e A hbU haU =>
      have db := ih body (by simp; omega)
      have da := ih a (by simp; omega)
      cases hv with
      | node op hsV =>
          obtain ⟨fV, aV, rfl, hfV, haV⟩ := hsV.two
          obtain ⟨AV, bodyV, rfl, _, hbV⟩ := hfV.lam_inv
          obtain ⟨bodyW, hbUW, hbVW⟩ := db _ _ hbU hbV
          obtain ⟨aW, haUW, haVW⟩ := da _ _ haU haV
          exact ⟨_, hbUW.instantiate haUW, .beta hbVW haVW⟩
      | beta hbV haV =>
          obtain ⟨bodyW, hbUW, hbVW⟩ := db _ _ hbU hbV
          obtain ⟨aW, haUW, haVW⟩ := da _ _ haU haV
          exact ⟨_, hbUW.instantiate haUW, hbVW.instantiate haVW⟩
  | add a b bound =>
      cases hv with
      | node op hsV =>
          obtain ⟨aV, bV, rfl, haV, hbV⟩ := hsV.two
          have ea := haV.natural_inv
          have eb := hbV.natural_inv
          subst aV; subst bV
          exact ⟨_, .refl _, .add a b bound⟩
      | add => exact ⟨_, .refl _, .refl _⟩
  | sub a b p lower upper =>
      cases hv with
      | node op hsV =>
          obtain ⟨aV, bV, pV, rfl, haV, hbV, _⟩ := hsV.three
          have ea := haV.natural_inv
          have eb := hbV.natural_inv
          subst aV; subst bV
          exact ⟨_, .refl _, .sub a b pV lower upper⟩
      | sub => exact ⟨_, .refl _, .refl _⟩
  | @read xs ysU u count k p hsU selectedU =>
      have dx : ∀ x ∈ xs, DiamondAt x := by
        intro x hx
        apply ih x
        have inside := List.sizeOf_lt_of_mem hx
        simp
        omega
      cases hv with
      | node op hsV =>
          obtain ⟨arrV, indexV, pV, rfl, harrV, hindexV, _⟩ := hsV.three
          obtain ⟨ysV, rfl, hysV⟩ := harrV.elements_inv
          have ei := hindexV.natural_inv
          subst indexV
          obtain ⟨ws, hUW, hVW⟩ := hsU.parallel_join hysV dx
          obtain ⟨w, hw, huw⟩ := hUW.lookup_right selectedU
          exact ⟨w, huw, .read count k pV hVW hw⟩
      | read count k p hsV selectedV =>
          obtain ⟨ws, hUW, hVW⟩ := hsU.parallel_join hsV dx
          obtain ⟨w, hw, huw⟩ := hUW.lookup_right selectedU
          obtain ⟨w', hw', hvw⟩ := hVW.lookup_right selectedV
          have same : w' = w := Option.some.inj (hw'.symm.trans hw)
          subst w'
          exact ⟨w, huw, hvw⟩
  | @witnessPack a aU p q haU =>
      have da := ih a (by simp; omega)
      cases hv with
      | node op hsV =>
          obtain ⟨packV, rfl, hpackV⟩ := hsV.one
          obtain ⟨pV, aV, qV, rfl, _, haV, _⟩ := hpackV.pack_inv
          obtain ⟨w, huw, hvw⟩ := da _ _ haU haV
          exact ⟨w, huw, .witnessPack hvw⟩
      | witnessPack haV => exact da _ _ haU haV
  | @proofPack q qU p a hqU =>
      have dq := ih q (by simp; omega)
      cases hv with
      | node op hsV =>
          obtain ⟨packV, rfl, hpackV⟩ := hsV.one
          obtain ⟨pV, aV, qV, rfl, _, _, hqV⟩ := hpackV.pack_inv
          obtain ⟨w, huw, hvw⟩ := dq _ _ hqU hqV
          exact ⟨w, huw, .proofPack hvw⟩
      | proofPack hqV => exact dq _ _ hqU hqV
  | @derefBorrow a aU haU =>
      have da := ih a (by simp; omega)
      cases hv with
      | node op hsV =>
          obtain ⟨borrowV, rfl, hborrowV⟩ := hsV.one
          cases hborrowV with
          | node op hsBorrow =>
              obtain ⟨aV, rfl, haV⟩ := hsBorrow.one
              obtain ⟨w, huw, hvw⟩ := da _ _ haU haV
              exact ⟨w, huw, .derefBorrow hvw⟩
          | borrowDeref hbV =>
              exact da _ _ haU (.node .deref (.cons hbV .nil))
      | derefBorrow haV => exact da _ _ haU haV
  | @borrowDeref a aU haU =>
      have da := ih a (by simp; omega)
      cases hv with
      | node op hsV =>
          obtain ⟨derefV, rfl, hderefV⟩ := hsV.one
          cases hderefV with
          | node op hsDeref =>
              obtain ⟨aV, rfl, haV⟩ := hsDeref.one
              obtain ⟨w, huw, hvw⟩ := da _ _ haU haV
              exact ⟨w, huw, .borrowDeref hvw⟩
          | derefBorrow hbV =>
              exact da _ _ haU (.node .borrow (.cons hbV .nil))
      | borrowDeref haV => exact da _ _ haU haV

  | @transportRefl p pU f a hpU =>
      have dp := ih p (by simp; omega)
      cases hv with
      | node op hsV =>
          obtain ⟨fV,eV,pV,rfl,_,heV,hpV⟩ := hsV.three
          cases heV with
          | node op hsRefl =>
              obtain ⟨aV,rfl,_⟩ := hsRefl.one
              obtain ⟨w,huw,hvw⟩ := dp _ _ hpU hpV
              exact ⟨w,huw,.transportRefl fV aV hvw⟩
      | transportRefl f a hpV => exact dp _ _ hpU hpV
  | @ifLtTrue yes yesU m n no bound hyU =>
      have dy := ih yes (by simp; omega)
      cases hv with
      | node op hsV =>
          obtain ⟨aV,bV,yesV,noV,rfl,haV,hbV,hyV,_⟩ := hsV.four
          have ea := haV.natural_inv
          have eb := hbV.natural_inv
          subst aV; subst bV
          obtain ⟨w,huw,hvw⟩ := dy _ _ hyU hyV
          exact ⟨_, huw.instantiate (.refl _), .ifLtTrue m n noV bound hvw⟩
      | ifLtTrue m n no boundV hyV =>
          obtain ⟨w,huw,hvw⟩ := dy _ _ hyU hyV
          exact ⟨_, huw.instantiate (.refl _), hvw.instantiate (.refl _)⟩
      | ifLtFalse m n yes reverse hnV => exact False.elim (by omega)
  | @ifLtFalse no noU m n yes bound hnU =>
      have dn := ih no (by simp; omega)
      cases hv with
      | node op hsV =>
          obtain ⟨aV,bV,yesV,noV,rfl,haV,hbV,_,hnV⟩ := hsV.four
          have ea := haV.natural_inv
          have eb := hbV.natural_inv
          subst aV; subst bV
          obtain ⟨w,huw,hvw⟩ := dn _ _ hnU hnV
          exact ⟨w,huw,.ifLtFalse m n yesV bound hvw⟩
      | ifLtTrue m n no forward hyV => exact False.elim (by omega)
      | ifLtFalse m n yes boundV hnV => exact dn _ _ hnU hnV
  | @ifEqTrue yes yesU n no hyU =>
      have dy := ih yes (by simp; omega)
      cases hv with
      | node op hsV =>
          obtain ⟨aV,bV,yesV,noV,rfl,haV,hbV,hyV,_⟩ := hsV.four
          have ea := haV.natural_inv
          have eb := hbV.natural_inv
          subst aV; subst bV
          obtain ⟨w,huw,hvw⟩ := dy _ _ hyU hyV
          exact ⟨_,huw.instantiate (.refl _),.ifEqTrue n noV hvw⟩
      | ifEqTrue n no hyV =>
          obtain ⟨w,huw,hvw⟩ := dy _ _ hyU hyV
          exact ⟨_,huw.instantiate (.refl _),hvw.instantiate (.refl _)⟩
      | ifEqFalse m n yes apart hnV => exact False.elim (apart rfl)
  | @ifEqFalse no noU m n yes apart hnU =>
      have dn := ih no (by simp; omega)
      cases hv with
      | node op hsV =>
          obtain ⟨aV,bV,yesV,noV,rfl,haV,hbV,_,hnV⟩ := hsV.four
          have ea := haV.natural_inv
          have eb := hbV.natural_inv
          subst aV; subst bV
          obtain ⟨w,huw,hvw⟩ := dn _ _ hnU hnV
          exact ⟨w,huw,.ifEqFalse m n yesV apart hvw⟩
      | ifEqTrue n no hyV => exact False.elim (apart rfl)
      | ifEqFalse m n yes apartV hnV => exact dn _ _ hnU hnV

/-- Full diamond property, including the two overlapping borrow/deref
cancellations. Strong induction exposes every strict source subterm. -/
theorem Par.diamond (hu : Par t u) (hv : Par t v) : ∃ w, Par u w ∧ Par v w := by
  have all : ∀ t, DiamondAt t := by
    have wf : WellFounded (fun a b : Term => sizeOf a < sizeOf b) := (measure sizeOf).wf
    intro t
    induction t using wf.induction with
    | h t ih =>
        intro u v hu hv
        rcases hu.view with ⟨x, rfl, rfl⟩ | ⟨op, xs, ys, rfl, rfl, hsU⟩ | rootU
        · cases hv
          exact ⟨_, .refl _, .refl _⟩
        · rcases hv.view with ⟨x, hx, _⟩ | ⟨op', xs', zs, he, rfl, hsV⟩ | rootV
          · cases hx
          · cases he
            have dx : ∀ x ∈ xs, DiamondAt x := by
              intro x hx
              apply ih x
              have inside := List.sizeOf_lt_of_mem hx
              simp
              omega
            obtain ⟨ws, hUW, hVW⟩ := hsU.parallel_join hsV dx
            exact ⟨.node op ws, .node op hUW, .node op hVW⟩
          · obtain ⟨w, hvw, huw⟩ := rootV.join ih (.node op hsU)
            exact ⟨w, huw, hvw⟩
        · exact rootU.join ih hv
  exact all t u v hu hv

/-- Reflexive-transitive closure, with no normalization assumption. -/
inductive Closure {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl : Closure R a a
  | cons : R a b → Closure R b c → Closure R a c

namespace Closure
variable {α β : Type} {R : α → α → Prop} {S : β → β → Prop}

theorem single (h : R a b) : Closure R a b := .cons h .refl

theorem trans (h : Closure R a b) (h' : Closure R b c) : Closure R a c := by
  induction h with
  | refl => exact h'
  | cons hab _ ih => exact .cons hab (ih h')

theorem map (f : α → β) (hf : ∀ {a b}, R a b → S (f a) (f b))
    (h : Closure R a b) : Closure S (f a) (f b) := by
  induction h with
  | refl => exact .refl
  | cons hab _ ih => exact .cons (hf hab) ih
end Closure

abbrev Star := Closure Par

theorem Star.strip (hu : Star t u) (hv : Par t v) :
    ∃ w, Par u w ∧ Star v w := by
  induction hu generalizing v with
  | refl => exact ⟨v, hv, .refl⟩
  | cons ht hs ih =>
      obtain ⟨q, hbq, hvq⟩ := ht.diamond hv
      obtain ⟨w, huw, hqw⟩ := ih hbq
      exact ⟨w, huw, .cons hvq hqw⟩

theorem Star.confluence (hu : Star t u) (hv : Star t v) :
    ∃ w, Star u w ∧ Star v w := by
  induction hu generalizing v with
  | refl => exact ⟨v, hv, .refl⟩
  | cons ht hs ih =>
      obtain ⟨q, hvq, hbq⟩ := hv.strip ht
      obtain ⟨w, huw, hqw⟩ := ih hbq
      exact ⟨w, huw, .cons hvq hqw⟩

private theorem ListRel.refl_par (xs : List Term) : ListRel Par xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (.refl x) ih

private theorem ListRel.stars (h : ListRel Star xs ys) : Closure (ListRel Par) xs ys := by
  induction h with
  | nil => exact .refl
  | @cons a b xs ys hab hxs ih =>
      exact (hab.map (fun x => x :: xs) (fun h => ListRel.cons h (ListRel.refl_par xs))).trans
        (ih.map (fun xs => b :: xs) (fun h => ListRel.cons (Par.refl b) h))

theorem Star.node (op : Op) (h : ListRel Star xs ys) : Star (.node op xs) (.node op ys) :=
  h.stars.map (Term.node op) (Par.node op)

def Join (t u : Term) : Prop := ∃ w, Star t w ∧ Star u w

private theorem Join.refl (t : Term) : Join t t := ⟨t, .refl, .refl⟩

private theorem Join.symm (h : Join t u) : Join u t := by
  obtain ⟨w, ht, hu⟩ := h
  exact ⟨w, hu, ht⟩

private theorem Join.trans (h : Join t u) (h' : Join u v) : Join t v := by
  obtain ⟨a, hta, hua⟩ := h
  obtain ⟨b, hub, hvb⟩ := h'
  obtain ⟨w, haw, hbw⟩ := hua.confluence hub
  exact ⟨w, hta.trans haw, hvb.trans hbw⟩

private theorem ListRel.join (h : ListRel Join xs ys) :
    ∃ zs, ListRel Star xs zs ∧ ListRel Star ys zs := by
  induction h with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons h _ ih =>
      obtain ⟨a, ha, hb⟩ := h
      obtain ⟨zs, hxs, hys⟩ := ih
      exact ⟨a :: zs, .cons ha hxs, .cons hb hys⟩

/-- Every modeled native conversion has a common forward parallel reduct.
This includes arbitrary malformed/ill-typed trees and all native operators. -/
theorem Conv.church_rosser (h : Conv t u) : Join t u := by
  induction h using Conv.rec (motive_2 := fun xs ys _ => ListRel Join xs ys) with
  | refl t => exact Join.refl t
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | node op _ ih =>
      obtain ⟨zs, hxs, hys⟩ := ih.join
      exact ⟨.node op zs, .node op hxs, .node op hys⟩
  | beta e A b a => exact ⟨_, .single (.beta (.refl b) (.refl a)), .refl⟩
  | add a b bound => exact ⟨_, .single (.add a b bound), .refl⟩
  | sub a b p lower upper => exact ⟨_, .single (.sub a b p lower upper), .refl⟩
  | read count xs k p v selected =>
      exact ⟨_, .single (.read count k p (ListRel.refl_par xs) selected), .refl⟩
  | witnessPack p a q => exact ⟨_, .single (.witnessPack (.refl a)), .refl⟩
  | proofPack p a q => exact ⟨_, .single (.proofPack (.refl q)), .refl⟩
  | derefBorrow a => exact ⟨_, .single (.derefBorrow (.refl a)), .refl⟩
  | borrowDeref a => exact ⟨_, .single (.borrowDeref (.refl a)), .refl⟩
  | transportRefl f a p => exact ⟨_,.single (.transportRefl f a (.refl p)),.refl⟩
  | ifLtTrue m n yes no bound => exact ⟨_,.single (.ifLtTrue m n no bound (.refl yes)),.refl⟩
  | ifLtFalse m n yes no bound => exact ⟨_,.single (.ifLtFalse m n yes bound (.refl no)),.refl⟩
  | ifEqTrue n yes no => exact ⟨_,.single (.ifEqTrue n no (.refl yes)),.refl⟩
  | ifEqFalse m n yes no apart => exact ⟨_,.single (.ifEqFalse m n yes apart (.refl no)),.refl⟩
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂

theorem Par.conv (h : Par t u) : Conv t u := by
  induction h using Par.rec (motive_2 := fun xs ys _ => ListRel Conv xs ys) with
  | var => exact .refl _
  | node op _ ih => exact .node op ih
  | beta hb ha ihb iha =>
      exact .trans (.node .app (.cons (.node (.lam _) (.cons (.refl _) (.cons ihb .nil)))
        (.cons iha .nil))) (.beta _ _ _ _)
  | add a b bound => exact .add a b bound
  | sub a b p lower upper => exact .sub a b p lower upper
  | read count k p hs selected ih =>
      exact .trans (.node .index (.cons (.node (.elements count) ih)
        (.cons (.refl _) (.cons (.refl p) .nil)))) (.read count _ k p _ selected)
  | witnessPack _ ih => exact .trans (.witnessPack _ _ _) ih
  | proofPack _ ih => exact .trans (.proofPack _ _ _) ih
  | derefBorrow _ ih => exact .trans (.derefBorrow _) ih
  | borrowDeref _ ih => exact .trans (.borrowDeref _) ih
  | transportRefl f a _ ih => exact .trans (.transportRefl f a _) ih
  | ifLtTrue m n no bound _ ih =>
      exact .trans (.ifLtTrue m n _ no bound)
        (ih.substitution (single (.decide (.natural m) (.natural n))))
  | ifLtFalse m n yes bound _ ih => exact .trans (.ifLtFalse m n yes _ bound) ih
  | ifEqTrue n no _ ih =>
      exact .trans (.ifEqTrue n _ no) (ih.substitution (single (.refl (.natural n))))
  | ifEqFalse m n yes apart _ ih => exact .trans (.ifEqFalse m n yes _ apart) ih
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂

theorem Star.conv (h : Star t u) : Conv t u := by
  induction h with
  | refl => exact .refl _
  | cons hp _ ih => exact .trans hp.conv ih

/-- Exactly the operators whose outer node cannot be contracted by a root
rule. This definition covers the entire Op vocabulary, including runtime forms. -/
def rigid : Op → Bool
  | .app | .uadd | .usub | .index | .witness | .proof | .deref | .borrow | .ifLt | .ifEq | .transport => false
  | _ => true

private theorem Par.rigid_inv {op : Op} (hr : rigid op = true) (h : Par (.node op xs) t) :
    ∃ ys, t = .node op ys ∧ ListRel Par xs ys := by
  cases h with
  | node op hs => exact ⟨_, rfl, hs⟩
  | _ => simp [rigid] at hr

private theorem ListRel.prependStar (hp : ListRel Par xs ys) (hs : ListRel Star ys zs) :
    ListRel Star xs zs := by
  induction hp generalizing zs with
  | nil => cases hs; exact .nil
  | cons hhead htail ih =>
      cases hs with
      | cons shead stail => exact .cons (.cons hhead shead) (ih stail)

private theorem ListRel.refl_star (xs : List Term) : ListRel Star xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons .refl ih

theorem Star.rigid_shape (h : Star t u) : ∀ {op xs}, rigid op = true → t = .node op xs →
    ∃ ys, u = .node op ys ∧ ListRel Star xs ys := by
  induction h with
  | refl =>
      intro op xs hr ht
      exact ⟨xs, ht, ListRel.refl_star xs⟩
  | cons hp hs ih =>
      intro op xs hr ht
      subst ht
      obtain ⟨ys, he, hxy⟩ := hp.rigid_inv hr
      obtain ⟨zs, hz, hyz⟩ := ih hr he
      exact ⟨zs, hz, hxy.prependStar hyz⟩

private theorem ListRel.join_conv (hx : ListRel Star xs zs) (hy : ListRel Star ys zs) :
    ListRel Conv xs ys := by
  induction hx generalizing ys with
  | nil => cases hy; exact .nil
  | cons hhead htail ih =>
      cases hy with
      | cons vhead vtail => exact .cons (.trans hhead.conv (.symm vhead.conv)) (ih vtail)

/-- Genuine injectivity in NativeConversion.Conv for every rigid native node.
Neither a semantic interpretation nor conversion reflection is assumed. -/
theorem Conv.rigid_node_injective {op op' : Op}
    (h : Conv (.node op xs) (.node op' ys)) (hr : rigid op = true) (hr' : rigid op' = true) :
    op = op' ∧ ListRel Conv xs ys := by
  obtain ⟨w, hw, hw'⟩ := h.church_rosser
  obtain ⟨zs, he, hxs⟩ := hw.rigid_shape hr rfl
  obtain ⟨zs', he', hys⟩ := hw'.rigid_shape hr' rfl
  have same := Term.node.inj (he.symm.trans he')
  rcases same with ⟨rfl, rfl⟩
  exact ⟨rfl, hxs.join_conv hys⟩

theorem Star.variable_shape (h : Star t u) (ht : t = .var x) : u = .var x := by
  induction h with
  | refl => exact ht
  | cons hp hs ih =>
      subst ht
      cases hp
      exact ih rfl

theorem Conv.variable_injective (h : Conv (.var x) (.var y)) : x = y := by
  obtain ⟨w, hw, hw'⟩ := h.church_rosser
  exact Term.var.inj ((hw.variable_shape rfl).symm.trans (hw'.variable_shape rfl))

/-- Neutral type variables cannot convert to a rigid constructed type. -/
theorem Conv.variable_node_separate {op : Op} (hr : rigid op = true) :
    ¬ Conv (.var x) (.node op xs) := by
  intro h
  obtain ⟨w, hw, hw'⟩ := h.church_rosser
  have hvar := hw.variable_shape rfl
  obtain ⟨ys, constructed, _⟩ := hw'.rigid_shape hr rfl
  cases hvar.symm.trans constructed

theorem Conv.pi_injective (h : Conv (.pi e A B) (.pi e' A' B')) :
    e = e' ∧ Conv A A' ∧ Conv B B' := by
  obtain ⟨he, hs⟩ := h.rigid_node_injective rfl rfl
  have flags := Op.pi.inj he
  cases hs with
  | cons hA hs =>
      cases hs with
      | cons hB hs => exact ⟨flags, hA, hB⟩

theorem Conv.array_injective (h : Conv (.array n) (.array n')) : Conv n n' := by
  obtain ⟨_, hs⟩ := h.rigid_node_injective rfl rfl
  cases hs with
  | cons hn hs => exact hn

theorem Conv.eq_injective (h : Conv (.eq a b) (.eq a' b')) : Conv a a' ∧ Conv b b' := by
  obtain ⟨_, hs⟩ := h.rigid_node_injective rfl rfl
  cases hs with
  | cons ha hs => cases hs with | cons hb hs => exact ⟨ha, hb⟩

theorem Conv.lt_injective (h : Conv (.lt a b) (.lt a' b')) : Conv a a' ∧ Conv b b' := by
  obtain ⟨_, hs⟩ := h.rigid_node_injective rfl rfl
  cases hs with
  | cons ha hs => cases hs with | cons hb hs => exact ⟨ha, hb⟩

theorem Conv.refine_injective (h : Conv (.refine p) (.refine q)) : Conv p q := by
  obtain ⟨_, hs⟩ := h.rigid_node_injective rfl rfl
  cases hs with
  | cons hp hs => exact hp

theorem Conv.universe_injective (h : Conv (.univ n) (.univ m)) : n = m := by
  obtain ⟨he, _⟩ := h.rigid_node_injective rfl rfl
  exact Op.universe.inj he

theorem Conv.natural_injective (h : Conv (.natural n) (.natural m)) : n = m := by
  obtain ⟨he, _⟩ := h.rigid_node_injective rfl rfl
  exact Op.natural.inj he

theorem Conv.integer_injective (h : Conv (.integer n) (.integer m)) : n = m := by
  obtain ⟨he, _⟩ := h.rigid_node_injective rfl rfl
  exact Op.integer.inj he

theorem Conv.rigid_disjoint {op op' : Op} (hr : rigid op = true) (hr' : rigid op' = true)
    (different : op ≠ op') : ¬ Conv (.node op xs) (.node op' ys) :=
  fun h => different (h.rigid_node_injective hr hr').1

theorem Conv.u64_i64_separate : ¬ Conv .u64 .i64 :=
  rigid_disjoint rfl rfl (by intro h; cases h)

theorem Conv.universe_prop_separate (n : Nat) : ¬ Conv (.univ n) .prop :=
  rigid_disjoint rfl rfl (by intro h; cases h)

theorem Conv.universe_successor_separate (n : Nat) : ¬ Conv (.univ n) (.univ (n+1)) := by
  intro h
  have same := h.universe_injective
  omega

theorem Conv.sort_injective {s r : SortTag} (h : Conv s.term r.term) : s = r := by
  cases s with
  | prop =>
      cases r with
      | prop => rfl
      | type n => exact False.elim (universe_prop_separate n (.symm h))
  | type n =>
      cases r with
      | prop => exact False.elim (universe_prop_separate n h)
      | type m => exact congrArg SortTag.type h.universe_injective

end Jihoo.NativeKernel.Conversion
