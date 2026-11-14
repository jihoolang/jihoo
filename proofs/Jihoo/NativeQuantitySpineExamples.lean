import Jihoo.NativeQuantityExamples

namespace Jihoo.NativeKernel.NativeQuantity.SpineExamples

open Jihoo.Quantity

private abbrev zero : Term := .natural 0
private abbrev one : Term := .natural 1
private abbrev buffer : Term := .node .buffer [zero]
private abbrev add : Term := .lam false .u64 (.lam false .u64 (.uadd (.var 1) (.var 0)))
private abbrev apply2 (f a b : Term) : Term := .app (.app f a) b
private abbrev firstOwner : Term := .lam false buffer (.lam false .i64 (.var 1))
private abbrev twoOwners : Term := .lam false buffer (.lam false buffer
  (.node (.give false) [zero, .var 1, .var 0]))

example : check 64 0 [] [] (apply2 add one one) = true := by decide
example : check 64 1 [0] [] (apply2 add (.var 0) one) = true := by decide
example : check 64 1 [0] [] (apply2 add (.var 0) (.var 0)) = false := by decide
example : (project 64 (.app add one)).isSome = true := by decide
example : (project 64 (.app add (.var 0))).isSome = true := by decide
example : check 64 1 [0] [] (apply2 firstOwner (.var 0) (.integer 0)) = true := by decide
example : check 64 2 [0, 1] [] (apply2 twoOwners (.var 0) (.var 1)) = true := by decide
example : check 64 1 [0] [] (apply2 twoOwners (.var 0) (.var 0)) = false := by decide

example : check 64 1 [0] [] (.app (.lam false buffer (.var 0)) (.var 0)) = true := by decide
example : check 64 1 [0] []
    (.app (.lam false buffer (.node .alloc [zero, .integer 0])) (.var 0)) = false := by decide
example : check 64 1 [0] []
    (.app (.lam false buffer (.node (.give false) [zero, .var 0, .var 0])) (.var 0)) = false := by decide
example : project 64 (.app (.var 0) zero) = none := by decide
example : (project 64 (.app (.lam false (.pi false .u64 .u64) (.var 0))
    (.lam false .u64 (.var 0)))).isSome = true := by decide

example : check 64 1 [0] []
    (.app (.lam true .u64 (.node .alloc [zero, .integer 0])) (.var 0)) = false := by decide
example : check 64 1 [] [0]
    (.app (.lam true .u64 (.node .alloc [zero, .integer 0])) (.var 0)) = true := by decide
example : check 64 0 [] [] (.app (.lam true .u64 (.var 0)) zero) = false := by decide
example : check 64 1 [] []
    (.app (.lam true .u64 (.uadd (.var 0) one)) zero) = false := by decide
example : check 64 0 [] []
    (.app (.lam true .u64 one) (.app (.var 0) (.var 0))) = true := by decide

example : check 64 1 [0] []
    (.app (.lam false .u64 (.uadd (.var 1) (.var 0))) zero) = true := by decide
example : check 64 1 [0] []
    (.strict (.app (.lam false .u64 (.uadd (.var 1) (.var 0))) zero) (.var 0)) = false := by decide
example : check 64 1 [0] []
    (.ifEq zero zero
      (.app (.lam false .u64 (.uadd (.var 2) (.var 0))) zero)
      (.app (.lam false .u64 (.uadd (.var 1) (.var 0))) zero)) = true := by decide
example : check 64 0 [] []
    (.app (.lam false .u64 (.var 0)) (.app (.lam false .u64 (.var 0)) one)) = true := by decide

example : check 64 1 [0] []
    (.app (.lam false .u64 (.uadd (.var 0) one)) (.var 0)) = true := by decide
example : check 1 0 [] [] (.app (.lam false .u64 (.var 0)) one) = false := by decide
example : check 64 1 [] [0]
    ((Term.app (.lam false .u64 (.uadd (.var 1) (.var 0))) zero).subst
      (fun x => atomTerm (Jihoo.Quantity.Substitution.openBorrow 5 x))) = true := by
  unfold check
  rw [reader_projection]
  decide

end Jihoo.NativeKernel.NativeQuantity.SpineExamples
