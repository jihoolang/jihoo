import Jihoo.Scoped

namespace Jihoo.Indexed
open Arithmetic (Expr)

def letSeven : Term := .letValue (.integer 7) (.param 0)

example : ScopedTyping 0 [] letSeven .i64 := by
  refine ⟨by simp, ?_, trivial, .letValue (.integer _ _) (.param _ _)⟩
  simp [letSeven, Term.Scoped]

example : Step letSeven (.integer 7) := .letBeta _ _

example : ScopedTyping 0 [] (.integer 7) .i64 := by
  apply scoped_preservation (t := letSeven) _ (.letBeta _ _)
  refine ⟨by simp, ?_, trivial, .letValue (.integer _ _) (.param _ _)⟩
  simp [letSeven, Term.Scoped]

-- A value argument containing an ambient index is shifted under an index lambda.
def mixedBinders : Term := .letValue (.refl (.var 0)) (.lam (.param 0))

example : Step mixedBinders (.lam (.refl (.var 1))) := .letBeta _ _

example : ScopedTyping 1 [] mixedBinders (.pi (.eq (.var 1) (.var 1))) := by
  refine ⟨by simp, ?_, ?_, .letValue (.refl _ _) (.lam (.param _ _))⟩
  · simp [mixedBinders, Term.Scoped, Expr.Scoped]
  · simp [Ty.Scoped, Expr.Scoped]

-- Crossing a value let must shift value variables too, avoiding capture.
example : Step (.letValue (.param 0) (.letValue (.integer 3) (.param 1)))
    (.letValue (.integer 3) (.param 1)) := .letBeta _ _

example : ScopedTyping 0 [.i64]
    (.letValue (.param 0) (.letValue (.integer 3) (.param 1))) .i64 := by
  refine ⟨?_, ?_, trivial, .letValue (.param _ _) (.letValue (.integer _ _) (.param _ _))⟩
  · simp [Ty.Scoped]
  · simp [Term.Scoped]

-- Out-of-context defaults in `complete` never authorize a finite scoped program.
example : ¬ ScopedTyping 0 [] (.param 0) .u64 := no_closed_parameter

example : ¬ ScopedTyping 0 [] (.lam (.natural (.var 1))) (.pi .u64) := by
  intro h
  have bad := h.2.1
  simp [Term.Scoped, Expr.Scoped] at bad

example : ¬ ScopedTyping 0 [.array (.var 0)] (.param 0) (.array (.var 0)) := by
  intro h
  have bad := h.1 (.array (.var 0)) (by simp)
  simp [Ty.Scoped, Expr.Scoped] at bad

-- A typed total-context term can be invalid at a finite scope.
example : HasType (complete []) (.param 0) .u64 := .param _ _

-- Interleaving both binder sorts weakens only the appropriate namespace.
example : Step
    (.letValue (.refl (.var 0)) (.lam (.letValue (.integer 3) (.param 1))))
    (.lam (.letValue (.integer 3) (.refl (.var 1)))) := .letBeta _ _

end Jihoo.Indexed
