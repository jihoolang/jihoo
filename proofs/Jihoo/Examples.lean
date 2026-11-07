import Jihoo.Arithmetic

namespace Jihoo.Arithmetic

-- Congruence and nested subtraction: equal atoms remain equal in larger sums.
example (a b c : Expr) :
    Conv (.add c (.sub (.add a b) b)) (.add a c) :=
  .trans (.add (.refl c) (.subAddCancel a b)) (.addComm c a)

-- Closed evidence uses a computable numeral comparison.
example : Derives [] (.lt (.lit 2) (.lit 5)) := .decide 2 5 (by decide)

example (a b c : Expr) (h : Derives Γ (.lt a b)) :
    Derives Γ (.lt a b) := .ltCancel (c := c) (.ltAdd h)

-- An open context may legitimately contain evidence; soundness requires it
-- to hold in the interpreting environment.
example (a b : Expr) : Derives [.lt a b] (.lt (.add a (.lit 7)) (.add b (.lit 7))) :=
  .ltAdd (.assumption (by simp))

example (a b : Expr) (h : Derives Γ (.eq a b))
    (p : Derives Γ (instantiate (.lt (.var 0) (.var 1)) a)) :
    Derives Γ (instantiate (.lt (.var 0) (.var 1)) b) :=
  .transport _ h p

-- The largest machine value plus one remains a natural in evidence.
example : Derives [] (.lt (.lit 0) (.add (.lit (2^64 - 1)) (.lit 1))) :=
  .zeroLe _

-- Unconditional (a-b)+b=a would be unsound. Conv cannot derive this instance.
example : ¬ Conv (.add (.sub (.lit 0) (.lit 1)) (.lit 1)) (.lit 0) := by
  intro h
  have bad := h.sound (fun _ => 0)
  simp [Expr.eval] at bad

example : ¬ Derives [] (.eq (.lit 0) (.lit 1)) := by
  intro h
  have bad := h.sound (fun _ => 0) (by simp [Satisfies])
  simp [Formula.Holds, Expr.eval] at bad

-- Equality transport is simultaneous even when the replacements mention zero.
example (p : Formula) (h : Derives Γ (.eq (.var 0) (.add (.var 0) (.var 1))))
    (hp : Derives Γ (instantiate p (.var 0))) :
    Derives Γ (instantiate p (.add (.var 0) (.var 1))) := .transport p h hp

example (x y z : Expr) (h : Derives Γ (.lt x y))
    (hy : Derives Γ (.lt y (.add z (.lit 1)))) : Derives Γ (.lt x z) :=
  .ltLe h hy

example (a : Expr) (ρ : Env) :
    (.add (.sub a a) a : Expr).eval ρ = a.eval ρ := by
  apply certified_sub_add (Γ := [])
  · exact .convertLt (.trans (.addComm _ _) (.addZero a)) (.addComm _ _)
      (.ltAdd (c := a) (.decide 0 1 (by decide)))
  · simp [Satisfies]

-- False assumptions permit false conclusions; the empty context matters.
example : Derives [.lt (.lit 0) (.lit 0)] (.lt (.lit 0) (.lit 0)) :=
  .assumption (by simp)

example : ¬ Derives [] (.lt (.lit 0) (.lit 0)) := no_closed_false_lt

end Jihoo.Arithmetic
