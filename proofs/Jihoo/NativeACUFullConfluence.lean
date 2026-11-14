import Jihoo.NativeACUParallelConfluence

/-! Full legacy-plus-ACU Church–Rosser modulo the proved finite arithmetic
quotient, and constructor injectivity in the actual ACU.Conv relation. -/
namespace Jihoo.NativeKernel.ACU

open Conversion (ListRel)

/-- Every original forward parallel computation embeds in the quotient
parallel calculus, including all legacy root constructors. -/
theorem QPar.ofLegacyParallel (h : Conversion.Par a b) : QPar a b := by
  induction h using Conversion.Par.rec
    (motive_2 := fun xs ys _ => ListRel QPar xs ys) with
  | var x => exact .refl _
  | node op hs ih => exact .node op ih
  | @beta body body' a a' e A hb ha ib ia =>
      exact QPar.ofAtom (.beta e A body (.refl _) ib ia) (by simp only [arithmeticFlatten])
  | add m n bound => exact .arithmetic (.add m n bound)
  | sub m n p bound valid =>
      exact QPar.ofAtom (.sub m n p (.refl _) (.refl _) bound valid) (by simp only [arithmeticFlatten])
  | read count k p hs selected ih =>
      exact QPar.ofAtom (.read count k p (.refl _) (.refl _) ih selected) (by simp only [arithmeticFlatten])
  | @witnessPack a a' p q ha ih =>
      exact QPar.ofAtom (.witnessPack p a q (.refl _) ih) (by simp only [arithmeticFlatten])
  | @proofPack q q' p a hq ih =>
      exact QPar.ofAtom (.proofPack p a q (.refl _) ih) (by simp only [arithmeticFlatten])
  | @derefBorrow a a' ha ih =>
      exact QPar.ofAtom (.derefBorrow a (.refl _) ih) (by simp only [arithmeticFlatten])
  | @borrowDeref a a' ha ih =>
      exact QPar.ofAtom (.borrowDeref a (.refl _) ih) (by simp only [arithmeticFlatten])
  | transportRefl f a hp ih =>
      exact QPar.ofAtom (.transportRefl a (.refl _) ih) (by simp only [arithmeticFlatten])
  | ifLtTrue m n no left hy ih =>
      exact QPar.ofAtom (.ifLtTrue m n no (.refl _) (.refl _) left ih) (by simp only [arithmeticFlatten])
  | ifLtFalse m n yes right hn ih =>
      exact QPar.ofAtom (.ifLtFalse m n yes (.refl _) (.refl _) right ih) (by simp only [arithmeticFlatten])
  | ifEqTrue n no hy ih =>
      exact QPar.ofAtom (.ifEqTrue n no (.refl _) (.refl _) ih) (by simp only [arithmeticFlatten])
  | ifEqFalse m n yes apart hn ih =>
      exact QPar.ofAtom (.ifEqFalse m n yes (.refl _) (.refl _) apart ih) (by simp only [arithmeticFlatten])
  | nil => exact .nil
  | cons h hs ih is => exact .cons ih is

theorem QStar.ofLegacy (h : Conversion.Star a b) : QStar a b := by
  induction h with
  | refl => exact .refl
  | cons h hs ih => exact .cons (QPar.ofLegacyParallel h) ih

theorem QStar.toConv (h : QStar a b) : Conv a b := by
  induction h with
  | refl => exact .refl _
  | cons h hs ih => exact h.toConv.trans ih

private theorem listQPar_refl (xs : List Term) : ListRel QPar xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (.refl x) ih

private theorem listQStar_refl (xs : List Term) : ListRel QStar xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons .refl ih

private theorem list_stars (h : ListRel QStar xs ys) : Conversion.Closure (ListRel QPar) xs ys := by
  induction h with
  | nil => exact .refl
  | @cons a b xs ys hab hxs ih =>
      exact (hab.map (fun x => x::xs) (fun h => ListRel.cons h (listQPar_refl xs))).trans
        (ih.map (fun xs => b::xs) (fun h => ListRel.cons (QPar.refl b) h))

theorem QStar.node (op : Op) (h : ListRel QStar xs ys) : QStar (.node op xs) (.node op ys) :=
  (list_stars h).map (Term.node op) (QPar.node op)

/-- A common reduct using forward legacy computation modulo Arithmetic.
Arithmetic contains exactly finite ACU and bounded literal-folding derivations;
it contains no beta, read, projection, transport, branch, or borrow inverse. -/
def QJoin (a b : Term) : Prop := ∃ c, QStar a c ∧ QStar b c

private theorem QJoin.refl (t : Term) : QJoin t t := ⟨t,.refl,.refl⟩
private theorem QJoin.symm (h : QJoin a b) : QJoin b a := by
  obtain ⟨c,hc,kc⟩ := h
  exact ⟨c,kc,hc⟩
private theorem QJoin.trans (h : QJoin a b) (k : QJoin b c) : QJoin a c := by
  obtain ⟨u,ha,hb⟩ := h
  obtain ⟨v,kb,kc⟩ := k
  obtain ⟨w,uw,vw⟩ := hb.confluence kb
  exact ⟨w,ha.trans uw,kc.trans vw⟩

private theorem list_join (h : ListRel QJoin xs ys) :
    ∃ zs, ListRel QStar xs zs ∧ ListRel QStar ys zs := by
  induction h with
  | nil => exact ⟨[],.nil,.nil⟩
  | cons h hs ih =>
      obtain ⟨a,ha,hb⟩ := h
      obtain ⟨zs,hxs,hys⟩ := ih
      exact ⟨a::zs,.cons ha hxs,.cons hb hys⟩

/-- Church–Rosser for the actual full ACU.Conv extension. Its only equations
modded out during forward computation are the separately proved Arithmetic
relation; no confluence, interpretation, or reflection theorem is a premise. -/
theorem Conv.church_rosser_modulo_arithmetic (h : Conv a b) : QJoin a b := by
  induction h using Conv.rec (motive_2 := fun xs ys _ => ListRel QJoin xs ys) with
  | legacy h =>
      obtain ⟨c,hc,kc⟩ := h.church_rosser
      exact ⟨c,QStar.ofLegacy hc,QStar.ofLegacy kc⟩
  | refl t => exact QJoin.refl t
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | node op kids ih =>
      obtain ⟨zs,hz,kz⟩ := list_join ih
      exact ⟨.node op zs,QStar.node op hz,QStar.node op kz⟩
  | assoc a b c => exact ⟨_,.single (.arithmetic (.assoc a b c)),.refl⟩
  | comm a b => exact ⟨_,.single (.arithmetic (.comm a b)),.refl⟩
  | zero a => exact ⟨_,.single (.arithmetic (.zero a)),.refl⟩
  | nil => exact .nil
  | cons h hs ih is => exact .cons ih is

theorem conv_iff_quotient_join (a b : Term) : Conv a b ↔ QJoin a b := by
  constructor
  · exact Conv.church_rosser_modulo_arithmetic
  · intro ⟨c,hc,kc⟩
    exact hc.toConv.trans kc.toConv.symm

/-- Rigid non-additive constructors. Natural payloads are covered separately. -/
def fullRigid (op : Op) : Bool := Conversion.rigid op && arithmeticRigid op

private theorem fullRigid_flatten (hr : fullRigid op = true) (xs : List Term) :
    arithmeticFlatten (.node op xs) = [.node op xs] := by
  have h := (Bool.and_eq_true_iff.mp hr).2
  cases op <;> simp_all only [arithmeticRigid,Bool.false_eq_true,arithmeticFlatten]

private theorem QAtom.rigid_inv (h : QAtom (.node op xs) t) (hr : fullRigid op = true) :
    ∃ ys, t = .node op ys ∧ ListRel QPar xs ys := by
  cases h with
  | node op hs => exact ⟨_,rfl,hs⟩
  | _ => simp only [fullRigid,Conversion.rigid,arithmeticRigid,Bool.false_and,Bool.false_eq_true] at hr

/-- Every quotient parallel reduct of a rigid node retains a displayed rigid
head modulo Arithmetic, with parallel derivations for its original children. -/
theorem QPar.rigid_view (h : QPar (.node op xs) t) (hr : fullRigid op = true) :
    ∃ ys, Arithmetic t (.node op ys) ∧ ListRel QPar xs ys := by
  obtain ⟨c,hc,out⟩ := h.atom_view (fullRigid_flatten hr xs)
  obtain ⟨ys,rfl,kids⟩ := hc.rigid_inv hr
  exact ⟨ys,out,kids⟩

private theorem list_prepend_star (h : ListRel QPar xs ys) (k : ListRel QStar ys zs) :
    ListRel QStar xs zs := by
  induction h generalizing zs with
  | nil => cases k; exact .nil
  | cons h hs ih => cases k with | cons k ks => exact .cons (.cons h k) (ih ks)

/-- Rigid heads survive any finite forward native computation modulo
Arithmetic, and their children retain actual finite forward derivations. -/
theorem QStar.rigid_shape (h : QStar t u) (hr : fullRigid op = true)
    (view : Arithmetic t (.node op xs)) :
    ∃ ys, Arithmetic u (.node op ys) ∧ ListRel QStar xs ys := by
  induction h generalizing xs with
  | refl => exact ⟨xs,view,listQStar_refl xs⟩
  | cons hp hs ih =>
      obtain ⟨ys,out,kids⟩ := (hp.input view).rigid_view hr
      obtain ⟨zs,last,rest⟩ := ih out
      exact ⟨zs,last,list_prepend_star kids rest⟩

theorem QStar.natural_shape (h : QStar t u) (view : Arithmetic t (.natural n)) :
    Arithmetic u (.natural n) := by
  induction h with
  | refl => exact view
  | cons hp hs ih => exact ih (hp.input view).natural_inv

private theorem list_join_conv (h : ListRel QStar xs us) (e : ListRel Arithmetic us vs)
    (k : ListRel QStar ys vs) : ListRel Conv xs ys := by
  induction h generalizing vs ys with
  | nil => cases e; cases k; exact .nil
  | cons h hs ih => cases e with | cons e es => cases k with
    | cons k ks => exact .cons (h.toConv.trans (e.toConv.trans k.toConv.symm)) (ih es ks)

/-- Rigid constructor injectivity in the actual extension containing every
legacy equation and unrestricted ACU congruence. This is a theorem, not a
property required of a conversion environment. -/
theorem Conv.full_rigid_node_injective (h : Conv (.node op xs) (.node op' ys))
    (left : fullRigid op = true) (right : fullRigid op' = true) :
    op = op' ∧ ListRel Conv xs ys := by
  obtain ⟨c,hc,kc⟩ := h.church_rosser_modulo_arithmetic
  obtain ⟨us,ou,hu⟩ := hc.rigid_shape left (.refl _)
  obtain ⟨vs,ov,kv⟩ := kc.rigid_shape right (.refl _)
  obtain ⟨eq,kids⟩ := (ou.symm.trans ov).head_fields
    (Bool.and_eq_true_iff.mp left).2 (Bool.and_eq_true_iff.mp right).2
  exact ⟨eq,list_join_conv hu kids kv⟩

theorem Conv.full_pi_injective (h : Conv (.pi e A B) (.pi e' A' B')) :
    e = e' ∧ Conv A A' ∧ Conv B B' := by
  obtain ⟨eq,kids⟩ := h.full_rigid_node_injective rfl rfl
  cases eq
  cases kids with | cons ha hs => cases hs with | cons hb hs => exact ⟨rfl,ha,hb⟩

theorem Conv.full_natural_injective (h : Conv (.natural m) (.natural n)) : m = n := by
  obtain ⟨c,hc,kc⟩ := h.church_rosser_modulo_arithmetic
  exact ((hc.natural_shape (.refl _)).symm.trans (kc.natural_shape (.refl _))).natural_injective

theorem Conv.full_universe_injective (h : Conv (.univ m) (.univ n)) : m = n := by
  obtain ⟨eq,_⟩ := h.full_rigid_node_injective rfl rfl
  exact Op.universe.inj eq

theorem Conv.full_u64_i64_separate : ¬ Conv .u64 .i64 := by
  intro h
  obtain ⟨eq,_⟩ := h.full_rigid_node_injective rfl rfl
  cases eq

theorem Conv.full_array_injective (h : Conv (.array n) (.array n')) : Conv n n' := by
  obtain ⟨_,kids⟩ := h.full_rigid_node_injective rfl rfl
  cases kids with | cons hn _ => exact hn

theorem Conv.full_eq_injective (h : Conv (.eq a b) (.eq a' b')) : Conv a a' ∧ Conv b b' := by
  obtain ⟨_,kids⟩ := h.full_rigid_node_injective rfl rfl
  cases kids with | cons ha hs => cases hs with | cons hb _ => exact ⟨ha,hb⟩

theorem Conv.full_lt_injective (h : Conv (.lt a b) (.lt a' b')) : Conv a a' ∧ Conv b b' := by
  obtain ⟨_,kids⟩ := h.full_rigid_node_injective rfl rfl
  cases kids with | cons ha hs => cases hs with | cons hb _ => exact ⟨ha,hb⟩

theorem Conv.full_refine_injective (h : Conv (.refine p) (.refine q)) : Conv p q := by
  obtain ⟨_,kids⟩ := h.full_rigid_node_injective rfl rfl
  cases kids with | cons hp _ => exact hp

theorem Conv.full_integer_injective (h : Conv (.integer m) (.integer n)) : m = n := by
  obtain ⟨eq,_⟩ := h.full_rigid_node_injective rfl rfl
  exact Op.integer.inj eq

theorem Conv.full_rigid_disjoint (left : fullRigid op = true) (right : fullRigid op' = true)
    (different : op ≠ op') : ¬ Conv (.node op xs) (.node op' ys) := by
  intro h
  exact different (h.full_rigid_node_injective left right).1

theorem Conv.full_sort_injective {s r : SortTag} (h : Conv s.term r.term) : s = r := by
  cases s with
  | prop => cases r with
    | prop => rfl
    | type n => exact False.elim (Conv.full_rigid_disjoint rfl rfl (by intro eq; cases eq) h)
  | type n => cases r with
    | prop => exact False.elim (Conv.full_rigid_disjoint rfl rfl (by intro eq; cases eq) h)
    | type m => exact congrArg SortTag.type h.full_universe_injective

private theorem QPar.variable_inv (h : QPar (.var x) t) : Arithmetic t (.var x) := by
  obtain ⟨c,hc,out⟩ := h.atom_view (by simp only [arithmeticFlatten])
  cases hc
  exact out

theorem QStar.variable_shape (h : QStar t u) (view : Arithmetic t (.var x)) : Arithmetic u (.var x) := by
  induction h with
  | refl => exact view
  | cons hp hs ih => exact ih (hp.input view).variable_inv

theorem Arithmetic.variable_injective (h : Arithmetic (.var x) (.var y)) : x = y := by
  have model := h.model
  unfold ArithmeticModel at model
  simp only [arithmeticFlatten] at model
  have atom := model.singleton ArithmeticAtom.refl ArithmeticAtom.symm ArithmeticAtom.trans
  cases atom
  rfl

theorem Conv.full_variable_injective (h : Conv (.var x) (.var y)) : x = y := by
  obtain ⟨c,hc,kc⟩ := h.church_rosser_modulo_arithmetic
  exact ((hc.variable_shape (.refl _)).symm.trans (kc.variable_shape (.refl _))).variable_injective

end Jihoo.NativeKernel.ACU
