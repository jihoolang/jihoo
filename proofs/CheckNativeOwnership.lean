import Jihoo.NativeOwnershipAdmission
import Jihoo.TypingInput

/-! Bounded exact-byte adapter for closed declarations checked against the empty
environment. There is no caller-selected ghost mode or outer resource list. -/
open Jihoo.NativeKernel Jihoo.GraphCertificates

private def preflight (bytes : ByteArray) : Bool := (do
  let cursor ← TypingInput.scanFields bytes 0 4
  let (count, start) ← TypingInput.scanNat bytes cursor
  if count > 4096 then none else do
    let mut cursor := start
    for _ in [:count] do
      cursor ← TypingInput.scanFields bytes cursor 1
      cursor ← TypingInput.scanVector bytes cursor 4
      cursor ← TypingInput.scanVector bytes cursor 4096
    if cursor = bytes.size then some () else none).isSome

def main (args : List String) : IO UInt32 := do
  try
    let [fuelText, quantityFuelText] := args |
      throw (IO.userError "expected typing fuel and quantity fuel")
    let some fuel := fuelText.toNat? | throw (IO.userError "invalid typing fuel")
    let some quantityFuel := quantityFuelText.toNat? | throw (IO.userError "invalid quantity fuel")
    if fuel > 128 ∨ quantityFuel > 128 then throw (IO.userError "fuel exceeds limit")
    let bytes ← TypingInput.input []
    unless preflight bytes do throw (IO.userError "invalid native snapshot shape or bounds")
    unless NativeOwnershipAdmission.checkBytes fuel quantityFuel Environment.empty bytes do
      throw (IO.userError "typing or closed resource gate rejects")
    IO.println "exact resource-gated native declaration accepted"
    return 0
  catch error =>
    IO.eprintln s!"native resource declaration rejected: {error}"
    return 1
