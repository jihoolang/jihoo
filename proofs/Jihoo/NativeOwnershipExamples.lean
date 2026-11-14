import Jihoo.NativeOwnership
import Jihoo.NativeResourceSyntax

namespace Jihoo.NativeKernel.NativeOwnership.Examples

open Jihoo.Quantity

private abbrev owned : Binding := ⟨.buffer (.natural 2), false⟩
private abbrev erasedIndex : Binding := ⟨.u64, true⟩
private abbrev borrowed : Binding := ⟨.ref (.buffer (.natural 2)), false⟩
private abbrev value : Binding := ⟨.i64, false⟩

example : classify [borrowed, erasedIndex, owned, value] =
    some [.borrowed, .erased, .linear, .unrestricted] := by decide
example : classify [⟨.var 0, false⟩] = none := by decide
example : classify [⟨.univ 0, false⟩] = none := by decide
example : classify [⟨.var 0, true⟩] = some [.erased] := by decide
example : check 32 [borrowed, erasedIndex, owned, value]
    (.free (.var 2) (.strict (.var 0) (.var 3))) = true := by decide
example : check 32 [owned] (.natural 0) = false := by decide
example : check 32 [owned] (.strict (.var 0) (.var 0)) = false := by decide
example : check 32 [owned] (.free (.var 0) (.natural 0)) = true := by decide
example : check 32 [erasedIndex] (.var 0) = false := by decide
example : check 32 [erasedIndex] (.proof (.var 0)) = true := by decide
example : check 32 [borrowed] (.strict (.var 0) (.var 0)) = true := by decide
example : checkClosed 32 (.lam false owned.ty (.var 0)) = true := by decide
example : checkClosed 32 (.lam false owned.ty (.natural 0)) = false := by decide
example : declarationGate 32 false (.lam false owned.ty (.natural 0)) = false := by decide
example : declarationGate 32 true (.lam false owned.ty (.natural 0)) = true := by decide

example : loadBodyType (.var 0) (.var 1) =
    .pi false .i64 (.pi false (.buffer (.var 1)) (.var 3)) := by simp only [loadBodyType, Term.rename]
example : PartialRenaming.shift (-2) 0 (.buffer (.var 3)) = some (.buffer (.var 1)) := by
  simp [PartialRenaming.shift, PartialRenaming.lower, PartialRenaming.rename?, PartialRenaming.renameArgs?, PartialRenaming.lift, PartialRenaming.lowerIndex, Op.binders]
example : PartialRenaming.shift (-2) 0 (.buffer (.var 0)) = none := by
  simp [PartialRenaming.shift, PartialRenaming.lower, PartialRenaming.rename?, PartialRenaming.renameArgs?, PartialRenaming.lift, PartialRenaming.lowerIndex, Op.binders]
example : PartialRenaming.shift (-2) 0 (.pi false .u64 (.var 2)) = none := by
  simp [PartialRenaming.shift, PartialRenaming.lower, PartialRenaming.rename?, PartialRenaming.renameArgs?, PartialRenaming.lift, PartialRenaming.liftOne, PartialRenaming.lowerIndex, Op.binders]
example : PartialRenaming.shift (-2) 0 (.pi false .u64 (.var 3)) =
    some (.pi false .u64 (.var 1)) := by
  simp [PartialRenaming.shift, PartialRenaming.lower, PartialRenaming.rename?, PartialRenaming.renameArgs?, PartialRenaming.lift, PartialRenaming.liftOne, PartialRenaming.lowerIndex, Op.binders]
example : (loadBodyType (.var 0) (.var 1)).subst (fun x => .natural x) =
    loadBodyType (.natural 0) (.natural 1) := by rw [subst_loadBodyType]; simp only [Term.subst]

end Jihoo.NativeKernel.NativeOwnership.Examples
