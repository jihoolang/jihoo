import Jihoo.NativeSubstitution

/-! Untyped conversion and executable bounded conversion search on the complete
native syntax. Generic node congruence covers every native operator. Search uses
selected pure beta/arithmetic/read/projection equations; it does not claim to
decide every equation implemented by Core.normal. -/
namespace Jihoo.NativeKernel.Conversion

inductive ListRel (R : Term → Term → Prop) : List Term → List Term → Prop where
  | nil : ListRel R [] []
  | cons : R a b → ListRel R xs ys → ListRel R (a :: xs) (b :: ys)

inductive Conv : Term → Term → Prop where
  | refl (t) : Conv t t
  | symm : Conv a b → Conv b a
  | trans : Conv a b → Conv b c → Conv a c
  | node (op : Op) : ListRel Conv xs ys → Conv (.node op xs) (.node op ys)
  | beta (e : Bool) (A body a : Term) :
      Conv (.node .app [.node (.lam e) [A, body], a]) (body.subst (single a))
  | add (a b : Nat) : a + b < 2^64 →
      Conv (.node .uadd [.node (.natural a) [], .node (.natural b) []]) (.node (.natural (a+b)) [])
  | sub (a b : Nat) (p : Term) : b ≤ a → a < 2^64 →
      Conv (.node .usub [.node (.natural a) [], .node (.natural b) [], p]) (.node (.natural (a-b)) [])
  | read (count : Nat) (xs : List Term) (k : Nat) (p v : Term) : xs[k]? = some v →
      Conv (.node .index [.node (.elements count) xs, .node (.natural k) [], p]) v
  | witnessPack (p a q : Term) : Conv (.node .witness [.node .pack [p,a,q]]) a
  | proofPack (p a q : Term) : Conv (.node .proof [.node .pack [p,a,q]]) q
  | derefBorrow (a : Term) : Conv (.node .deref [.node .borrow [a]]) a
  | borrowDeref (a : Term) : Conv (.node .borrow [.node .deref [a]]) a

  | transportRefl (f a p : Term) :
      Conv (.node .transport [f, .node .refl [a], p]) p
  | ifLtTrue (m n : Nat) (yes no : Term) : m < n →
      Conv (.node .ifLt [.node (.natural m) [], .node (.natural n) [], yes, no])
        (yes.subst (single (.node .decide [.node (.natural m) [], .node (.natural n) []])))
  | ifLtFalse (m n : Nat) (yes no : Term) : n ≤ m →
      Conv (.node .ifLt [.node (.natural m) [], .node (.natural n) [], yes, no]) no
  | ifEqTrue (n : Nat) (yes no : Term) :
      Conv (.node .ifEq [.node (.natural n) [], .node (.natural n) [], yes, no])
        (yes.subst (single (.node .refl [.node (.natural n) []])))
  | ifEqFalse (m n : Nat) (yes no : Term) : m ≠ n →
      Conv (.node .ifEq [.node (.natural m) [], .node (.natural n) [], yes, no]) no

@[simp] theorem renameArgs_elements (count : Nat) (ρ : Nat → Nat) (offset : Nat) (xs : List Term) :
    renameArgs (.elements count) ρ offset xs = xs.map (Term.rename ρ) := by
  induction xs generalizing offset with
  | nil => simp [renameArgs]
  | cons x xs ih => simp [renameArgs, Op.binders, liftRenaming, ih]

@[simp] theorem substArgs_elements (count : Nat) (σ : Nat → Term) (offset : Nat) (xs : List Term) :
    substArgs (.elements count) σ offset xs = xs.map (Term.subst σ) := by
  induction xs generalizing offset with
  | nil => simp [substArgs]
  | cons x xs ih => simp [substArgs, Op.binders, liftSub, ih]

theorem Conv.renaming {a b : Term} (h : Conv a b) (ρ : Nat → Nat) :
    Conv (a.rename ρ) (b.rename ρ) := by
  induction h using Conv.rec
    (motive_2 := fun xs ys _ => ∀ op offset ρ,
      ListRel Conv (renameArgs op ρ offset xs) (renameArgs op ρ offset ys)) generalizing ρ with
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih ρ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ ρ) (ih₂ ρ)
  | node op _ ih => simpa only [Term.rename] using Conv.node op (ih op 0 ρ)
  | beta e A body a =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming, Term.rename_instantiate] using
        Conv.beta e (A.rename ρ) (body.rename (Indexed.liftRenaming ρ)) (a.rename ρ)
  | add a b bound =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using Conv.add a b bound
  | sub a b p hb ha =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using Conv.sub a b (p.rename ρ) hb ha
  | read count xs k p v selected =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
        Conv.read count (xs.map (Term.rename ρ)) k (p.rename ρ) (v.rename ρ)
          (by simp [List.getElem?_map, selected])
  | witnessPack p a q =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
        Conv.witnessPack (p.rename ρ) (a.rename ρ) (q.rename ρ)
  | proofPack p a q =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
        Conv.proofPack (p.rename ρ) (a.rename ρ) (q.rename ρ)
  | derefBorrow a =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using Conv.derefBorrow (a.rename ρ)
  | borrowDeref a =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using Conv.borrowDeref (a.rename ρ)
  | transportRefl f a p =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
        Conv.transportRefl (f.rename ρ) (a.rename ρ) (p.rename ρ)
  | ifLtTrue m n yes no bound =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming, Term.rename_instantiate] using
        Conv.ifLtTrue m n (yes.rename (Indexed.liftRenaming ρ)) (no.rename ρ) bound
  | ifLtFalse m n yes no bound =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
        Conv.ifLtFalse m n (yes.rename (Indexed.liftRenaming ρ)) (no.rename ρ) bound
  | ifEqTrue n yes no =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming, Term.rename_instantiate] using
        Conv.ifEqTrue n (yes.rename (Indexed.liftRenaming ρ)) (no.rename ρ)
  | ifEqFalse m n yes no apart =>
      simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
        Conv.ifEqFalse m n (yes.rename (Indexed.liftRenaming ρ)) (no.rename ρ) apart
  | nil => simp [renameArgs]; exact .nil
  | cons _ _ ih₁ ih₂ =>
      rename_i op offset ρ
      simp only [renameArgs]
      exact .cons (ih₁ _) (ih₂ op (offset + 1) ρ)

theorem Conv.substitution {a b : Term} (h : Conv a b) (σ : Nat → Term) :
    Conv (a.subst σ) (b.subst σ) := by
  induction h using Conv.rec
    (motive_2 := fun xs ys _ => ∀ op offset σ,
      ListRel Conv (substArgs op σ offset xs) (substArgs op σ offset ys)) generalizing σ with
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih σ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ σ) (ih₂ σ)
  | node op _ ih => simpa only [Term.subst] using Conv.node op (ih op 0 σ)
  | beta e A body a =>
      simpa [Term.subst, substArgs, Op.binders, liftSub, Term.subst_instantiate] using
        Conv.beta e (A.subst σ) (body.subst (liftSubOne σ)) (a.subst σ)
  | add a b bound =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using Conv.add a b bound
  | sub a b p hb ha =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using Conv.sub a b (p.subst σ) hb ha
  | read count xs k p v selected =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using
        Conv.read count (xs.map (Term.subst σ)) k (p.subst σ) (v.subst σ)
          (by simp [List.getElem?_map, selected])
  | witnessPack p a q =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using
        Conv.witnessPack (p.subst σ) (a.subst σ) (q.subst σ)
  | proofPack p a q =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using
        Conv.proofPack (p.subst σ) (a.subst σ) (q.subst σ)
  | derefBorrow a =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using Conv.derefBorrow (a.subst σ)
  | borrowDeref a =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using Conv.borrowDeref (a.subst σ)
  | transportRefl f a p =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using
        Conv.transportRefl (f.subst σ) (a.subst σ) (p.subst σ)
  | ifLtTrue m n yes no bound =>
      simpa [Term.subst, substArgs, Op.binders, liftSub, Term.subst_instantiate] using
        Conv.ifLtTrue m n (yes.subst (liftSubOne σ)) (no.subst σ) bound
  | ifLtFalse m n yes no bound =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using
        Conv.ifLtFalse m n (yes.subst (liftSubOne σ)) (no.subst σ) bound
  | ifEqTrue n yes no =>
      simpa [Term.subst, substArgs, Op.binders, liftSub, Term.subst_instantiate] using
        Conv.ifEqTrue n (yes.subst (liftSubOne σ)) (no.subst σ)
  | ifEqFalse m n yes no apart =>
      simpa [Term.subst, substArgs, Op.binders, liftSub] using
        Conv.ifEqFalse m n (yes.subst (liftSubOne σ)) (no.subst σ) apart
  | nil => simp [substArgs]; exact .nil
  | cons _ _ ih₁ ih₂ =>
      rename_i op offset σ
      simp only [substArgs]
      exact .cons (ih₁ _) (ih₂ op (offset + 1) σ)

def treeSize : Term → Nat
  | .var _ => 1
  | .node _ xs => 1 + (xs.map treeSize).sum

def treeDepth : Term → Nat
  | .var _ => 1
  | .node _ xs => 1 + (xs.map treeDepth).foldl max 0

/-- A substitution expansion guard, not a bound on total normalization work. -/
def substitutionSafe (body arg : Term) : Bool :=
  decide (treeSize body * (treeSize arg + 1) ≤ 200000 ∧ treeDepth body + treeDepth arg ≤ 128)

/-- Transform every child; this visits even unsupported runtime/inductive forms. -/
def children (f : Term → Term) : Term → Term
  | .var x => .var x
  | .node op xs => .node op (xs.map f)

/-- Selected native pure computation rules. Ill-shaped nodes stay neutral. -/
def contract : Term → Option Term
  | .node .app [.node (.lam _) [_, body], a] =>
      if substitutionSafe body a then some (body.subst (single a)) else none
  | .node .uadd [.node (.natural a) [], .node (.natural b) []] =>
      if a + b < 2^64 then some (.node (.natural (a+b)) []) else none
  | .node .usub [.node (.natural a) [], .node (.natural b) [], _] =>
      if b ≤ a ∧ a < 2^64 then some (.node (.natural (a-b)) []) else none
  | .node .index [.node (.elements _) xs, .node (.natural k) [], _] => xs[k]?
  | .node .witness [.node .pack [_, a, _]] => some a
  | .node .proof [.node .pack [_, _, q]] => some q
  | .node .deref [.node .borrow [a]] => some a
  | .node .borrow [.node .deref [a]] => some a
  | .node .transport [_f, .node .refl [_a], p] => some p
  | .node .ifLt [.node (.natural m) [], .node (.natural n) [], yes, no] =>
      if m < n then
        let evidence := .node .decide [.node (.natural m) [], .node (.natural n) []]
        if substitutionSafe yes evidence then some (yes.subst (single evidence)) else none
      else some no
  | .node .ifEq [.node (.natural m) [], .node (.natural n) [], yes, no] =>
      if m = n then
        let evidence := .node .refl [.node (.natural m) []]
        if substitutionSafe yes evidence then some (yes.subst (single evidence)) else none
      else some no
  | _ => none

/-- Bounded residual normalization; every recursive call decreases fuel. -/
def normalize : Nat → Term → Term
  | 0, t => t
  | fuel + 1, t =>
      let residual := children (normalize fuel) t
      match contract residual with
      | some u => normalize fuel u
      | none => residual

@[simp] theorem normalize_zero (t : Term) : normalize 0 t = t := rfl

theorem children_sound (t : Term) (f : Term → Term) (h : ∀ t, Conv t (f t)) :
    Conv t (children f t) := by
  cases t with
  | var => exact .refl _
  | node op xs =>
      apply Conv.node
      induction xs with
      | nil => exact .nil
      | cons x xs ih => exact .cons (h x) ih

theorem contract_sound {t u : Term} (h : contract t = some u) : Conv t u := by
  fun_cases contract t <;> simp_all [contract]
  all_goals try (split at h <;> simp_all <;> try (exact False.elim (by omega)))
  all_goals try (rcases h with ⟨hbound, h⟩)
  all_goals try subst u
  all_goals first
    | exact .beta _ _ _ _
    | exact .add _ _ (by omega)
    | exact .sub _ _ _ (by omega) (by omega)
    | exact .read _ _ _ _ _ (by assumption)
    | exact .witnessPack _ _ _
    | exact .proofPack _ _ _
    | exact .derefBorrow _
    | exact .borrowDeref _
    | exact .transportRefl _ _ _
    | exact .ifLtTrue _ _ _ _ (by omega)
    | exact .ifLtFalse _ _ _ _ (by omega)
    | exact .ifEqTrue _ _ _
    | exact .ifEqFalse _ _ _ _ (by assumption)

theorem normalize_sound (fuel : Nat) (t : Term) : Conv t (normalize fuel t) := by
  induction fuel generalizing t with
  | zero => exact .refl _
  | succ fuel ih =>
      have hc := children_sound t (normalize fuel) ih
      simp only [normalize]
      split
      · rename_i u hu
        exact .trans hc (.trans (contract_sound hu) (ih u))
      · exact hc

/-- A negative result is inconclusive; budget exhaustion can leave redexes. -/
def equal (fuel : Nat) (a b : Term) : Bool :=
  decide (normalize fuel a = normalize fuel b)

theorem equal_sound {fuel : Nat} {a b : Term} (h : equal fuel a b = true) : Conv a b := by
  have he : normalize fuel a = normalize fuel b := of_decide_eq_true h
  apply Conv.trans (normalize_sound fuel a)
  rw [he]
  exact .symm (normalize_sound fuel b)

@[simp] theorem equal_self (fuel : Nat) (t : Term) : equal fuel t t = true := by simp [equal]

theorem equal_symm (fuel : Nat) (a b : Term) : equal fuel a b = equal fuel b a := by
  simp only [equal, eq_comm]

theorem equal_trans {fuel : Nat} {a b c : Term}
    (hab : equal fuel a b = true) (hbc : equal fuel b c = true) : equal fuel a c = true :=
  decide_eq_true ((of_decide_eq_true hab).trans (of_decide_eq_true hbc))

end Jihoo.NativeKernel.Conversion
