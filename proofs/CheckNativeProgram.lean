import Jihoo.NativeProgramAdmission
import Jihoo.TypingInput

/-! Bounded IO adapter for canonical version-5 ordered native programs. The
pure admission theorem does not depend on this adapter or source provenance. -/
open Jihoo.NativeKernel Jihoo.GraphCertificates

private def preflight (bytes : ByteArray) : Bool := (do
  let (version, cursor) ← TypingInput.scanNat bytes 0
  if version != 5 then none else do
    let (declarations, cursor) ← TypingInput.scanNat bytes cursor
    if declarations > 1024 then none else do
      let cursor ← TypingInput.scanFields bytes cursor (2 * declarations)
      let (nodes, cursor) ← TypingInput.scanNat bytes cursor
      if nodes > 4096 then none else do
        let mut cursor := cursor
        for _ in [:nodes] do
          cursor ← TypingInput.scanFields bytes cursor 1
          cursor ← TypingInput.scanVector bytes cursor 4
          cursor ← TypingInput.scanVector bytes cursor 4096
        if cursor = bytes.size then some () else none).isSome

def main (args : List String) : IO UInt32 := do
  try
    let [fuelText] := args | throw (IO.userError "expected fuel")
    let some fuel := fuelText.toNat? | throw (IO.userError "invalid fuel")
    if fuel > 128 then throw (IO.userError "fuel exceeds limit")
    let bytes ← TypingInput.input []
    unless preflight bytes do throw (IO.userError "invalid native program shape or bounds")
    unless NativeProgramAdmission.checkBytes fuel bytes do
      throw (IO.userError "native program admission rejects")
    IO.println "exact native program accepted"
    return 0
  catch error =>
    IO.eprintln s!"native program rejected: {error}"
    return 1
