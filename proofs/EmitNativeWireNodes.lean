import Jihoo.NativeWire

/-! Compare actual native serialization of every constructor with the canonical
Lean encoder whose round-trip and exact-byte properties are mechanized. -/
open Jihoo.NativeKernel

private def encoded (node : NativeArena.Node) : String :=
  String.fromUTF8! (NativeWire.encodeNode node).toByteArray

def main : IO Unit := do
  for count in [0, 1, 3] do
    IO.println s!"{count}\tVar\t{encoded (.var 0)}"
    for op in NativeSchema.representatives count do
      let node := NativeArena.Node.node op (List.replicate op.arity 0)
      IO.println s!"{count}\t{op.nativeName}\t{encoded node}"
