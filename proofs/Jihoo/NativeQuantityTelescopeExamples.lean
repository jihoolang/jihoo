import Jihoo.NativeQuantityFunctions
import Jihoo.NativeTyping
import Jihoo.NativeResourceSyntax

namespace Jihoo.NativeKernel.NativeQuantity.TelescopeExamples

open Jihoo.Quantity

private abbrev zero : Term := .natural 0
private abbrev buffer : Term := .buffer (.natural 2)
private abbrev first : Term := .lam false buffer
  (.lam false .u64 (.free (.var 1) (.var 0)))
private abbrev last : Term := .lam false .u64
  (.lam false buffer (.free (.var 0) (.var 1)))
private abbrev twoOwners : Term := .lam false buffer (.lam false buffer
  (.lam false .u64 (.free (.var 2) (.free (.var 1) (.var 0)))))
private abbrev returnedClosure : Term := .lam false buffer
  (.strict zero (.lam false .u64 (.var 1)))

example : project 32 first = some (.closure (.scopes [.linear, .unrestricted]
    (.seq (.use 1) (.seq (.use 0) .pure)))) := by decide
example : check 32 0 [] [] first = true := by decide
example : check 32 0 [] [] last = true := by decide
example : check 32 0 [] [] twoOwners = true := by decide
example : check 32 0 [] [] returnedClosure = false := by decide
example : check 32 1 [0] [] (.lam false .u64 (.lam false .i64 (.var 2))) = false := by decide
example : check 32 0 [] [] (.app first (.alloc (.natural 2) (.integer 0))) = false := by decide
example : check 32 0 [] [] (.app (.app (.lam false buffer (.lam false .u64 (.var 1)))
    (.alloc (.natural 2) (.integer 0))) zero) = true := by decide
example : check 32 0 [] [] (.lam false buffer (.lam false .u64
    (.free (.var 1) (.free (.var 1) zero)))) = false := by decide
example : check 32 0 [] [] (.lam false buffer (.lam true .u64
    (.free (.var 1) (.var 0)))) = false := by decide
example : check 32 0 [] [] (.lam false buffer (.lam true .u64
    (.free (.var 1) zero))) = true := by decide

example : openFunctions 2 (.closure (.scopes [.unrestricted, .linear, .unrestricted] (.use 1))) =
    some (.scopes [.unrestricted, .linear] (.closure (.scope .unrestricted (.use 1)))) := by decide
example : openFunctions 3 (.closure (.scopes [.unrestricted, .linear, .unrestricted] (.use 1))) =
    some (.scopes [.unrestricted, .linear, .unrestricted] (.use 1)) := by decide
example : openFunctions 3 (.closure (.scopes [.unrestricted, .linear] (.use 0))) = none := by decide
example : caseBody 3 (.closure (.scopes [.unrestricted, .linear] (.use 0))) =
    .closure (.scopes [.unrestricted, .linear] (.use 0)) := by decide
example : (caseBody 2 (.closure (.scopes [.unrestricted, .linear, .unrestricted] (.use 1)))).demand 0 = none := by decide
example : (caseBody 3 (.closure (.scopes [.unrestricted, .linear, .unrestricted] (.use 1)))).demand 0 = some 0 := by decide

example : LambdaTelescope first [.linear, .unrestricted] (.free (.var 1) (.var 0)) :=
  .lam (by decide) (.lam (by decide) (.stop (by decide)))
example : project 32 (first.rename (fun x => x + 7)) = project 32 first := by
  rw [project_rename]
  decide
example : project 32 (first.subst (fun x => atomTerm (.borrow (x + 7)))) = project 32 first := by
  rw [project_atom_subst]
  decide
example : check 32 0 [] [] (.load (.alloc (.natural 2) (.integer 0)) zero zero
    (.lam false .i64 (.lam false buffer (.lam false .u64 (.free (.var 1) (.var 0)))))) = false := by decide

end Jihoo.NativeKernel.NativeQuantity.TelescopeExamples
