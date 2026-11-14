import Jihoo.NativeAdmission
import Jihoo.TypingInput

/-! Bounded IO adapter to the proved exact-byte native-syntax admission function.
The input contains no derivation certificate and no normalization trace. -/
open Jihoo.NativeKernel
open Jihoo.GraphCertificates

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
    let [fuelText] := args | throw (IO.userError "expected fuel")
    let some fuel := fuelText.toNat? | throw (IO.userError "invalid fuel")
    if fuel > 128 then throw (IO.userError "fuel exceeds limit")
    let bytes ← TypingInput.input []
    unless preflight bytes do throw (IO.userError "invalid native snapshot shape or bounds")
    unless NativeAdmission.checkBytes fuel bytes do
      throw (IO.userError "native-syntax admission rejects")
    IO.println "exact native-syntax snapshot accepted"
    return 0
  catch error =>
    IO.eprintln s!"native-syntax snapshot rejected: {error}"
    return 1
