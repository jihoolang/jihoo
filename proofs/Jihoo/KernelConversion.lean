import Jihoo.TypingCertificates

/-! Executable conversion search over Raw terms, independently justified by the
existing untyped beta/arithmetic/read conversion relation. The depth budget
limits search; exhaustion returns a convertible residual term. Consequently an
unsuccessful comparison does not establish inequivalence. No derivation or trace
certificate is supplied as input. -/
namespace Jihoo.KernelConversion

open CoreBridge CoreBridge.Raw
open GraphCertificates.Typing (rawDecidableEq substitutionSafe)

/-- Transform each immediate child, including annotations, binder bodies and all
array elements. The transformation itself must respect de Bruijn binding. -/
def children (f : Raw → Raw) : Raw → Raw
  | .array n => .array (f n)
  | .lt a b => .lt (f a) (f b)
  | .eq a b => .eq (f a) (f b)
  | .pi e A B => .pi e (f A) (f B)
  | .lam e A body => .lam e (f A) (f body)
  | .app g a => .app (f g) (f a)
  | .elements xs => .elements (xs.map f)
  | .index a i p => .index (f a) (f i) (f p)
  | .refl a => .refl (f a)
  | .zeroLe a => .zeroLe (f a)
  | .decide a b => .decide (f a) (f b)
  | .uadd a b => .uadd (f a) (f b)
  | .usub a b p => .usub (f a) (f b) (f p)
  | t => t

/-- A single root contraction. Arithmetic preserves the native word bounds;
subtraction never folds underflow. Beta expansion uses the existing substitution
size/depth guard. The untyped read relation permits any selected element. -/
def contract : Raw → Option Raw
  | .app (.lam _ _ body) a =>
      if substitutionSafe body a then some (body.subst (single a)) else none
  | .uadd (.natural a) (.natural b) =>
      if a + b < wordBound then some (.natural (a + b)) else none
  | .usub (.natural a) (.natural b) _ =>
      if b ≤ a ∧ a < wordBound then some (.natural (a - b)) else none
  | .index (.elements xs) (.natural k) _ => xs[k]?
  | _ => none

/-- Bounded bottom-up normalization followed by another bounded search after a
root contraction. Every recursive call decreases fuel. Zero returns its input;
the result need not be a full normal form and the budget is not a total work cap. -/
def normalize : Nat → Raw → Raw
  | 0, t => t
  | fuel + 1, t =>
      let residual := children (normalize fuel) t
      match contract residual with
      | some u => normalize fuel u
      | none => residual

@[simp] theorem normalize_zero (t : Raw) : normalize 0 t = t := rfl

private theorem list_children_sound (xs : List Raw) (f : Raw → Raw)
    (h : ∀ t, Beta.Conv t (f t)) : Beta.ListRel Beta.Conv xs (xs.map f) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (h x) ih

/-- A pointwise convertible child transformation is convertible at every Raw
constructor; in particular no evidence or annotation field is skipped. -/
theorem children_sound (t : Raw) (f : Raw → Raw)
    (h : ∀ t, Beta.Conv t (f t)) : Beta.Conv t (children f t) := by
  cases t with
  | var | natural | integer | u64 | i64 => exact .refl _
  | array n => exact .array (h n)
  | lt a b => exact .lt (h a) (h b)
  | eq a b => exact .eq (h a) (h b)
  | pi e A B => exact .pi (h A) (h B)
  | lam e A body => exact .lam (h A) (h body)
  | app g a => exact .app (h g) (h a)
  | elements xs => exact .elements (list_children_sound xs f h)
  | index a i p => exact .index (h a) (h i) (h p)
  | refl a => exact .reflTerm (h a)
  | zeroLe a => exact .zeroLe (h a)
  | decide a b => exact .decide (h a) (h b)
  | uadd a b => exact .uadd (h a) (h b)
  | usub a b p => exact .usub (h a) (h b) (h p)

/-- Every successful root contraction has a declarative conversion derivation. -/
theorem contract_sound {t u : Raw} (h : contract t = some u) : Beta.Conv t u := by
  cases t <;> simp only [contract] at h
  all_goals first | contradiction | skip
  case app f a =>
    cases f <;> try dsimp only at h
    all_goals first | contradiction | skip
    case lam e A body =>
      split at h
      · cases h
        exact .beta e A body a
      · contradiction
  case uadd a b =>
    cases a <;> try dsimp only at h
    all_goals first | contradiction | skip
    case natural a =>
      cases b <;> try dsimp only at h
      all_goals first | contradiction | skip
      case natural b =>
        split at h
        · rename_i bound
          cases h
          exact .add a b bound
        · contradiction
  case usub a b p =>
    cases a <;> try dsimp only at h
    all_goals first | contradiction | skip
    case natural a =>
      cases b <;> try dsimp only at h
      all_goals first | contradiction | skip
      case natural b =>
        split at h
        · rename_i bound
          cases h
          exact .subLiteral a b p bound.1 bound.2
        · contradiction
  case index a i p =>
    cases a <;> try dsimp only at h
    all_goals first | contradiction | skip
    case elements xs =>
      cases i <;> try dsimp only at h
      all_goals first | contradiction | skip
      case natural k => exact .read xs k p u h

/-- Soundness is unconditional, including on ill-typed raw inputs and at zero
fuel. Search budgets affect acceptance power, never the conversion guarantee. -/
theorem normalize_sound (fuel : Nat) (t : Raw) : Beta.Conv t (normalize fuel t) := by
  induction fuel generalizing t with
  | zero => exact .refl _
  | succ fuel ih =>
      have hc := children_sound t (normalize fuel) (fun s => ih s)
      simp only [normalize]
      split
      · rename_i u hu
        exact .trans hc (.trans (contract_sound hu) (ih u))
      · exact hc

/-- Compare bounded residuals structurally. False means search did not establish
conversion; it can reflect insufficient fuel. -/
def equal (fuel : Nat) (a b : Raw) : Bool :=
  decide (normalize fuel a = normalize fuel b)

theorem equal_sound {fuel : Nat} {a b : Raw} (h : equal fuel a b = true) :
    Beta.Conv a b := by
  have he : normalize fuel a = normalize fuel b := of_decide_eq_true h
  apply Beta.Conv.trans (normalize_sound fuel a)
  rw [he]
  exact .symm (normalize_sound fuel b)

@[simp] theorem equal_self (fuel : Nat) (t : Raw) : equal fuel t t = true := by
  simp [equal]

theorem equal_symm (fuel : Nat) (a b : Raw) : equal fuel a b = equal fuel b a := by
  simp only [equal, eq_comm]

theorem equal_trans {fuel : Nat} {a b c : Raw}
    (hab : equal fuel a b = true) (hbc : equal fuel b c = true) :
    equal fuel a c = true := by
  exact decide_eq_true ((of_decide_eq_true hab).trans (of_decide_eq_true hbc))

end Jihoo.KernelConversion
