import Jihoo.Semantics

namespace Jihoo.Indexed
open Arithmetic (Expr)

def addZeroEquality : Term := .lam (.refl (.add (.var 0) (.lit 0)))

-- Conversion is inside the derivation, around the function before application.
theorem converted_function (Γ : Context) :
    HasType Γ addZeroEquality (.pi (.eq (.var 0) (.var 0))) :=
  .convert (.lam (.refl _ _)) (.pi (.eq (.addZero _) (.addZero _)))

example (Γ : Context) :
    HasType Γ (.app addZeroEquality (.lit 7)) (.eq (.lit 7) (.lit 7)) :=
  .app (converted_function Γ)

example (Γ : Context) :
    HasType Γ (.refl (.add (.lit 7) (.lit 0))) (.eq (.lit 7) (.lit 7)) :=
  preservation (t := .app addZeroEquality (.lit 7)) (.app (converted_function Γ)) (.beta _ _)

example (Γ : Context) :
    HasType Γ (.refl (.add (.lit 7) (.lit 0)))
      (.eq (.add (.lit 7) (.lit 0)) (.add (.lit 7) (.lit 0))) := by
  apply preservation (t := .app addZeroEquality (.lit 7)) _ (.beta _ _)
  exact .convert (.app (converted_function Γ))
    (.eq (.symm (.addZero _)) (.symm (.addZero _)))

-- A let body uses both a converted array type and converted bounds evidence.
def convertedLet : Term :=
  .letValue (.elements [3]) (.index (.param 0) (.lit 0) (.decide 0 1))

theorem converted_let (Γ : Context) : HasType Γ convertedLet .i64 := by
  apply HasType.letValue (A := .array (.add (.lit 0) (.lit 1)))
  · exact .convert (.elements _ _) (.array (.symm (.addLiterals 0 1)))
  · apply HasType.index (.param _ 0)
    exact .convert (.decide _ _ _ (by decide))
      (.lt (.refl _) (.symm (.addLiterals 0 1)))

example (Γ : Context) : HasType Γ (.index (.elements [3]) (.lit 0) (.decide 0 1)) .i64 :=
  preservation (t := convertedLet) (converted_let Γ) (.letBeta _ _)

example : ScopedTyping 0 [] convertedLet .i64 := by
  refine ⟨by simp, ?_, trivial, converted_let _⟩
  simp [convertedLet, Term.Scoped, Expr.Scoped]

example : HasType (fun _ => .array (.add (.lit 0) (.lit 1))) (.param 0) (.array (.lit 1)) :=
  (HasType.param (fun _ => .array (.lit 1)) 0).contextConversion
    (fun _ => .array (.symm (.addLiterals 0 1)))

example : ScopedTyping 0 [] (.elements [3]) (.array (.add (.lit 0) (.lit 1))) := by
  have base : ScopedTyping 0 [] (.elements [3]) (.array (.lit 1)) :=
    ⟨by simp, trivial, trivial, .elements _ _⟩
  apply base.convert (.array (.symm (.addLiterals 0 1)))
  simp [Ty.Scoped, Expr.Scoped]

-- Raw conversion can introduce an index that cancels mathematically. Finite
-- conversion therefore needs explicit scope of its new result type.
def hiddenIndex : Expr := .sub (.add (.lit 0) (.var 0)) (.var 0)

example : HasType (complete []) (.elements []) (.array hiddenIndex) :=
  .convert (.elements _ _) (.array (.symm (.subAddCancel _ _)))

example : ¬ ScopedTyping 0 [] (.elements []) (.array hiddenIndex) := by
  intro h
  have bad := h.2.2.1
  simp [hiddenIndex, Ty.Scoped, Expr.Scoped] at bad

-- Conversion cannot turn unequal numerals or distinct type constructors equal.
example : ¬ Ty.Conv (.eq (.lit 0) (.lit 0)) (.eq (.lit 0) (.lit 1)) := by
  intro h
  have bad := h.view_sound (fun _ => 0)
  simp [Ty.view, Expr.eval] at bad

example : ¬ Ty.Conv (.array (.lit 1)) .u64 := by
  intro h
  cases h

-- These quantify over all terms, including arbitrary nested lets/conversions.
example (t : Term) : ¬ ScopedTyping 0 [] t (.lt (.lit 0) (.lit 0)) :=
  no_closed_false_bound

example (t : Term) : ¬ ScopedTyping 0 [] t (.eq (.lit 0) (.lit 1)) :=
  no_closed_false_equality

end Jihoo.Indexed
