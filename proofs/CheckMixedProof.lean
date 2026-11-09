import Jihoo.MixedProofAdmission
import Jihoo.TypingInput

open Jihoo.GraphCertificates.TypingInput
open Jihoo.MixedProofFunctions.Checked.Snapshot

def main (args : List String) : IO UInt32 := do
  try
    let snapshot ← canonicalSnapshot (← input args)
    let some _ := admitSnapshot snapshot |
      throw (IO.userError "unsupported, ill-typed, inexact or over-budget mixed proof snapshot")
    IO.println "mixed proof snapshot accepted"
    return 0
  catch error =>
    IO.eprintln s!"mixed proof snapshot rejected: {error}"
    return 1
