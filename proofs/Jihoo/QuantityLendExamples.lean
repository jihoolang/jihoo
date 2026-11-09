import Jihoo.QuantityLendProjection

namespace Jihoo.Quantity.LendProjection
open Binders ContextProjection

private def ctx : List Entry := [⟨⟨100, false⟩, .buffer⟩]
private def observe (_ : List RawBinding) : Nat → Option Domain
  | 100 => some .buffer | 101 => some .borrow | 102 => some .scalar | _ => none

-- Original nodes for lend b (fun r => index r 0 proof)
--   (fun x returned => free returned x). Domain summaries are trusted here.
private def graph : Syntax
  | 0 => .lend 1 2 3
  | 1 => .var 0
  | 2 => .lam false 101 4
  | 3 => .lam false 102 5
  | 4 => .seq 7 8
  | 5 => .lam false 100 6
  | 6 => .seq 9 10
  | 7 => .var 0
  | 8 => .literal
  | 9 => .var 0
  | 10 => .var 1
  | _ => .unsupported

private def expected : Control :=
  .seq (.scope .borrowed (.seq (.use 0) .pure))
    (.scope .unrestricted (.seq (.use 1) (.use 0)))

example : project graph observe 8 ctx 0 11 = some (expected, 0) := by decide
example : project graph observe 8 ctx 0 10 = none := by decide
example : expected.demand 0 = some 1 := rfl
-- The original name at slot 2 and returned name at slot 0 denote the same owner.
example : project (fun n => if n = 9 then .var 2 else graph n) observe 8 ctx 0 11 =
    some (expected, 0) := by decide
example : project (fun n => if n = 9 then .var 3 else graph n) observe 8 ctx 0 11 = none := by decide
example : project (fun n => if n = 2 then .lam true 101 4 else graph n) observe 8 ctx 0 20 = none := by decide
example : project (fun n => if n = 3 then .lam false 101 5 else graph n) observe 8 ctx 0 20 = none := by decide
example : project (fun n => if n = 5 then .lam false 102 6 else graph n) observe 8 ctx 0 20 = none := by decide
example : project (fun n => if n = 7 then .var 1 else graph n) observe 8 ctx 0 20 = none := by decide
-- Both alias names consumed: reject, rather than counting them as independent owners.
example : project (fun n => if n = 10 then .var 2 else graph n) observe 8 ctx 0 20 = none := by decide

-- An owned reader result is a fresh linear slot, separate from returned owner.
example : checkedLend 0 .linear .pure (.seq (.use 0) (.seq (.use 1) .pure)) =
    some (.seq (.scope .borrowed .pure)
      (.scope .linear (.seq (.use 1) (.seq (.use 0) .pure)))) := rfl
example : checkedLend 0 .linear .pure (.seq (.use 0) .pure) = none := rfl
example : checkedLend 0 .linear .pure (.seq (.use 0) (.seq (.use 1) (.use 1))) = none := rfl
-- A mistaken alias offset merges the fresh result and returned owner.
example : (Control.scope .linear (.alias 0 (.seq (.use 0) (.use 1)))).demand 0 = none := rfl

-- Seven visits, despite just three shared nodes. A depth bound alone is insufficient.
private def shared : Syntax
  | 0 => .seq 1 1 | 1 => .seq 2 2 | _ => .literal
example : project shared observe 3 [] 0 7 = some (.seq (.seq .pure .pure) (.seq .pure .pure), 0) := by decide
example : project shared observe 3 [] 0 6 = none := by decide
example : project (fun _ => .seq 0 0) observe 8 [] 0 100 = none := by decide
example : project graph observe 0 ctx 0 100 = none := rfl

example : rootedProject (fun n => if n = 20 then .lam false 100 0 else graph n)
    observe 8 11 20 = some (ctx, expected, 0) := by decide
example : rootedProject (fun n => if n = 20 then .lam true 100 0 else graph n)
    observe 8 11 20 = none := by decide

-- Nested real-shaped Lend: old result x is slot 3 under the inner result/owner.
private def nested : Syntax
  | 6 => .lend 9 11 12
  | 11 => .lam false 101 13
  | 12 => .lam false 102 15
  | 13 => .seq 14 8
  | 14 => .var 0
  | 15 => .lam false 100 16
  | 16 => .seq 17 18
  | 17 => .var 0
  | 18 => .seq 19 20
  | 19 => .var 3
  | 20 => .var 1
  | n => graph n
example : (project nested observe 12 ctx 0 21).map (fun result => result.1.demand 0) =
    some (some 1) := by decide
example : project nested observe 12 ctx 0 20 = none := by decide

private def ownedResult : Syntax
  | 3 => .lam false 100 5
  | 7 => .literal
  | 10 => .seq 11 8
  | 11 => .var 1
  | n => graph n
example : (project ownedResult observe 8 ctx 0 13).map (fun result => result.1.demand 0) =
    some (some 1) := by decide
example : project (fun n => if n = 11 then .literal else ownedResult n) observe 8 ctx 0 20 = none := by decide

end Jihoo.Quantity.LendProjection
