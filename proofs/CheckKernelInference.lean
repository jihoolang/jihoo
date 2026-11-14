import Jihoo.KernelAdmission
import Jihoo.TypingInput

/-! Regression adapter: run the proved certificate-free admission function on
the exact native snapshot bytes after bounded IO preflight. Native provenance
and IO execution are not refinement theorems. -/
open Jihoo Jihoo.GraphCertificates

def main (args : List String) : IO UInt32 := do
  try
    let [fuelText] := args | throw (IO.userError "expected fuel")
    let some fuel := fuelText.toNat? | throw (IO.userError "invalid fuel")
    if fuel > 128 then throw (IO.userError "fuel exceeds regression limit")
    let bytes ← TypingInput.input []
    let _ ← TypingInput.canonicalSnapshot bytes
    unless KernelAdmission.checkBytes fuel bytes do
      throw (IO.userError "raw inference differs or rejects")
    IO.println "exact snapshot raw inference accepted"
    return 0
  catch error =>
    IO.eprintln s!"exact snapshot raw inference rejected: {error}"
    return 1
