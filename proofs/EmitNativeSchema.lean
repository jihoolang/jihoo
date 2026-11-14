import Jihoo.NativeSchema

/-! Constructor metadata emitted from the same definitions used by the full
native syntax and its binder-aware substitution proofs. -/
open Jihoo.NativeKernel

def main : IO Unit := do
  for count in [0, 1, 3] do
    IO.println s!"{count}\tVar\t0\t0\t"
    for op in NativeSchema.representatives count do
      let binders := String.intercalate "," ((List.range op.arity).map
        (fun index => toString (op.binders index)))
      IO.println s!"{count}\t{op.nativeName}\t{NativeSchema.tag op}\t{op.arity}\t{binders}"
