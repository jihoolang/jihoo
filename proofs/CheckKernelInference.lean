import Jihoo.KernelChecker
import Jihoo.TypingInput

/-! Regression adapter: consume the existing exact native snapshot envelope,
unfold its selected roots with the existing bounded graph decoder, and compare
the executable raw checker result. IO provenance is not a refinement theorem. -/
open Jihoo Jihoo.GraphCertificates
open Jihoo.GraphCertificates.Typing (rawDecidableEq)

def main (args : List String) : IO UInt32 := do
  try
    let [fuelText] := args | throw (IO.userError "expected fuel")
    let some fuel := fuelText.toNat? | throw (IO.userError "invalid fuel")
    if fuel > 128 then throw (IO.userError "fuel exceeds regression limit")
    let snapshot ← TypingInput.canonicalSnapshot (← TypingInput.input [])
    let some term := decode snapshot.graph snapshot.termRoot |
      throw (IO.userError "unsupported or invalid selected term")
    let some ty := decode snapshot.graph snapshot.typeRoot |
      throw (IO.userError "unsupported or invalid selected type")
    unless KernelChecker.infer fuel [] term = some ty do
      throw (IO.userError "raw inference differs or rejects")
    unless KernelChecker.isType fuel [] ty do
      throw (IO.userError "raw formation rejects")
    IO.println "exact snapshot raw inference accepted"
    return 0
  catch error =>
    IO.eprintln s!"exact snapshot raw inference rejected: {error}"
    return 1
