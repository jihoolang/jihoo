import Jihoo.NativeQuantityAtoms
import Jihoo.NativeTyping

namespace Jihoo.NativeKernel.NativeQuantity.Examples

open Jihoo.Quantity

private abbrev zero : Term := .natural 0
private abbrev buffer : Term := .node .buffer [zero]
private abbrev free (a b : Term) : Term := .node .free [a, b]
private abbrev load (a i p k : Term) : Term := .node .load [a, i, p, k]
private abbrev borrowed : Term := .node .ref [buffer]
private abbrev ownId : Term := .lam false buffer (.var 0)
private abbrev loadBody : Term := .lam false .i64 (.lam false buffer (free (.var 0) (.var 1)))
private abbrev loopBody : Term := .lam false .u64
  (.lam true (.lt (.var 0) (.natural 3)) (.lam false buffer (.var 0)))

example : check 32 1 [0] [] (.var 0) = true := by decide
example : check 32 1 [0] [] zero = false := by decide
example : check 32 1 [0] [] (.strict (.var 0) (.var 0)) = false := by decide
example : check 32 1 [0] [] (free (.var 0) zero) = true := by decide
example : check 32 1 [0] [] (.proof (.var 0)) = false := by decide
example : check 32 1 [] [0] (.proof (.var 0)) = true := by decide
example : check 32 1 [] [0] (.var 0) = false := by decide
example : check 32 1 [] [] (.lam false .i64 (.var 1)) = true := by decide
example : check 32 1 [0] [] (.lam false .i64 (.var 1)) = false := by decide
example : check 32 0 [] [] ownId = true := by decide
example : check 32 0 [] [] (.lam false buffer zero) = false := by decide
example : check 32 0 [] [] (.lam false buffer (.strict (.var 0) (.var 0))) = false := by decide
example : check 32 0 [] [] (.lam true .u64 (.var 0)) = false := by decide
example : check 32 0 [] [] (.lam true .u64 zero) = true := by decide
example : check 32 0 [] [] (.lam false borrowed (.strict (.var 0) (.var 0))) = true := by decide

example : check 32 1 [0] [] (.ifLt zero zero (.var 1) (.var 0)) = true := by decide
example : check 32 1 [0] [] (.ifEq zero zero (.var 1) zero) = false := by decide
example : check 32 1 [0] [] (.ifEq zero zero (.var 0) (.var 0)) = false := by decide
example : check 32 1 [0] [] (.ifEq zero zero (.proof (.var 1)) (.proof (.var 0))) = false := by decide
example : check 32 1 [0] []
    (.strict (.var 0) (.ifEq zero zero (.proof (.var 1)) (.proof (.var 0)))) = true := by decide

example : check 32 1 [0] [] (load (.var 0) zero (.var 0) loadBody) = true := by decide
example : check 32 1 [0] []
    (load (.var 0) zero zero (.lam false .i64 (.lam false buffer zero))) = false := by decide
example : check 32 2 [0, 1] []
    (load (.var 0) zero zero
      (.lam false .i64 (.lam false buffer (free (.var 0) (.var 3))))) = true := by decide
example : check 32 1 [0] []
    (.node .take [.var 0, .lam false .i64 (.lam false buffer (.var 0))]) = true := by decide
example : check 32 1 [0] [] (.node (.give true) [zero, .var 0, .var 0]) = true := by decide
example : check 32 1 [0] [] (.node (.give false) [zero, .var 0, .var 0]) = false := by decide

example : check 32 1 [0] [] (.fold zero (.var 0) loopBody) = true := by decide
example : check 32 1 [0] []
    (.loop zero (.var 0) (.var 0) loopBody) = true := by decide
example : check 32 1 [0] []
    (.fold zero zero (.lam false .u64 (.lam true (.lt zero zero)
      (.lam false .i64 (.var 3))))) = false := by decide
example : check 32 1 [0] [] (.app ownId (.var 0)) = true := by decide
example : project 32 (.node .lend [.var 0, zero, zero]) = none := by decide
example : project 32 (.node (.con 0 0 1) [.var 0]) = none := by decide
example : project 32 (.node .free [.var 0]) = none := by decide
example : project 0 (.var 0) = none := by decide

example : (project 32 ((.var 0 : Term).subst
    (fun x => atomTerm (Jihoo.Quantity.Substitution.openBorrow 5 x)))).bind
      (Control.demand 5) = some 0 := by rw [reader_demand]; decide
example : (project 32 ((Term.strict (.var 0) (.var 1)).subst
    (fun x => atomTerm (Jihoo.Quantity.Substitution.openVariable 0 x)))).bind
      (Control.demand 0) = some 2 := by rw [continuation_projection]; decide
example : check 32 1 [0] []
    ((Term.ifEq zero zero (.var 1) (.var 1)).rename (fun _ => 0)) = true := by
  simp only [Term.rename, renameArgs, Op.binders, liftRenaming, Indexed.liftRenaming]
  decide
example : (project 32 ((Term.ifEq zero zero (.var 1) (.var 0)).subst
    (fun x => atomTerm (Jihoo.Quantity.Substitution.openBorrow 3 x)))).bind
      (Control.demand 3) = some 0 := by rw [reader_demand]; decide

end Jihoo.NativeKernel.NativeQuantity.Examples
