import Jihoo.QuantitySubstitution

namespace Jihoo.Quantity.Substitution

private def read : Expr := .seq (.var 0) (.borrow 3)
example : read.subst (openBorrow 2) = some (.seq (.borrow 2) (.borrow 2)) := rfl
-- Erasing ownership events alone cannot authenticate which pointer was borrowed.
example : (Expr.borrow 1).project = (Expr.borrow 2).project := rfl
example : (Expr.borrow 1) ≠ (Expr.borrow 2) := by decide
example : (Expr.borrow 0).subst (openBorrow 2) = none := rfl
example : (Expr.lend 0 .unrestricted .literal .literal).subst (openBorrow 2) = none := rfl

-- Capture avoidance preserves a fresh owned slot below the replaced borrow.
example : (Expr.scope .linear (.seq (.var 0) (.var 1))).subst (openBorrow 3) =
    some (.scope .linear (.seq (.var 0) (.borrow 4))) := rfl
example : (Expr.scope .erased (.scope .linear (.seq (.var 0) (.var 2)))).subst (openBorrow 3) =
    some (.scope .erased (.scope .linear (.seq (.var 0) (.borrow 5)))) := rfl

private def rest : Expr := .seq (.var 0) (.var 1)
example : rest.subst (openVariable 1) = some (.seq (.var 1) (.var 0)) := rfl
example : (Control.scope .linear (.seq (.use 1) (.use 0))).demand 0 = some 1 := rfl
-- Wrong shift merges fresh result and owner, even when both have the same type.
example : rest.subst (openVariable 0) = some (.seq (.var 0) (.var 0)) := rfl
example : (Control.scope .linear (.seq (.use 0) (.use 0))).demand 0 = none := rfl

private def nested : Expr := .lend 0 .unrestricted
  (.seq (.var 0) .literal) (.seq (.var 0) (.seq (.var 3) (.var 1)))
example : nested.subst (openVariable 1) = some
    (.lend 1 .unrestricted (.seq (.var 0) .literal)
      (.seq (.var 0) (.seq (.var 2) (.var 1)))) := rfl
-- Both the returned name and the old name map to the actual original owner.
example : (Expr.seq (.var 0) (.var 2)).subst (openVariable 1) =
    some (.seq (.var 1) (.var 1)) := rfl

-- Substitution does not turn a pre-existing fresh-slot/capture rejection into success.
example : ((Control.scope .linear (.seq (.use 0) (.seq (.use 0) (.use 1)))).relabel dropBorrow).demand 0 = none := rfl
example : ((Control.closure (.seq (.use 0) (.use 1))).relabel dropBorrow).demand 0 = none := rfl
example : ((Control.branch (.use 1) .pure).relabel dropBorrow).demand 0 = none := rfl
example : ((Control.repeat (.use 1)).relabel dropBorrow).demand 0 = none := rfl
example : ((Control.seq (.use 0) (.use 1)).relabel dropBorrow).demand 0 = some 1 := rfl

end Jihoo.Quantity.Substitution
