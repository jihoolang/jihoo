import Jihoo.Indexed

namespace Jihoo.Indexed

open Arithmetic (Expr)

-- A genuinely dependent result: the equality type refers to the argument.
def selfEquality : Term := .lam (.refl (.var 0))

example (Γ : Context) :
    HasType Γ selfEquality (.pi (.eq (.var 0) (.var 0))) :=
  .lam (.refl _ _)

example (Γ : Context) :
    HasType Γ (.app selfEquality (.lit 7)) (.eq (.lit 7) (.lit 7)) :=
  .app (.lam (.refl _ _))

example : Step (.app selfEquality (.lit 7)) (.refl (.lit 7)) := .beta _ _

example (Γ : Context) : HasType Γ (.refl (.lit 7)) (.eq (.lit 7) (.lit 7)) :=
  preservation (t := .app selfEquality (.lit 7)) (.app (.lam (.refl _ _))) (.beta _ _)

-- Substituting a free variable beneath a lambda must shift it, not capture it.
def outerEquality : Term := .lam (.lam (.refl (.var 1)))

example : Step (.app outerEquality (.var 0)) (.lam (.refl (.var 1))) := .beta _ _

example (Γ : Context) :
    HasType Γ (.app outerEquality (.var 0)) (.pi (.eq (.var 1) (.var 1))) :=
  .app (.lam (.lam (.refl _ _)))

-- Removing the remaining binder restores the original free index zero.
example : Steps (.app (.app outerEquality (.var 0)) (.lit 9)) (.refl (.var 0)) :=
  .next (.app (.beta _ _)) (.next (.beta _ _) (.refl _))

example (Γ : Context) : HasType Γ (.refl (.var 0)) (.eq (.var 0) (.var 0)) :=
  preservation_many (t := .app (.app outerEquality (.var 0)) (.lit 9))
    (.app (.app (.lam (.lam (.refl _ _)))))
    (.next (.app (.beta _ _)) (.next (.beta _ _) (.refl _)))

-- Types of free value parameters are weakened under an index binder.
def arrays : Context := fun _ => .array (.var 0)

example : HasType arrays (.lam (.param 0)) (.pi (.array (.var 1))) :=
  .lam (.param _ _)

example : HasType arrays (.app (.lam (.param 0)) (.lit 7)) (.array (.var 0)) :=
  .app (.lam (.param _ _))

-- A beta step inside an array expression retains the index evidence type.
example (Γ : Context) :
    HasType Γ (.index (.app (.lam (.elements [3, 7])) (.lit 8)) (.lit 0) (.decide 0 2))
      .i64 := .index (.app (.lam (.elements _ _))) (.decide _ _ _ (by decide))

example : Step
    (.index (.app (.lam (.elements [3, 7])) (.lit 8)) (.lit 0) (.decide 0 2))
    (.index (.elements [3, 7]) (.lit 0) (.decide 0 2)) := .indexArray (.beta _ _)

-- This reduction relation deliberately stops before runtime array loads.
example (Γ : Context) :
    HasType Γ (.index (.elements [3, 7]) (.lit 0) (.decide 0 2)) .i64 :=
  .index (.elements _ _) (.decide _ _ _ (by decide))

-- The extrinsic relation rejects false result annotations and wrong lengths.
example (Γ : Context) : ¬ HasType Γ (.refl (.lit 0)) (.eq (.lit 0) (.lit 1)) := by
  intro h
  cases h

example (Γ : Context) : ¬ HasType Γ (.elements [3, 7]) (.array (.lit 3)) := by
  intro h
  cases h

example (Γ : Context) :
    HasType Γ (.app (.lam (.zeroLe (.var 0))) (.lit 5))
      (.lt (.lit 0) (.add (.lit 5) (.lit 1))) := .app (.lam (.zeroLe _ _))

-- This calculus has no type-conversion rule, even for zero plus one.
example (Γ : Context) :
    ¬ HasType Γ (.elements [3]) (.array (.add (.lit 0) (.lit 1))) := by
  intro h
  cases h

end Jihoo.Indexed
