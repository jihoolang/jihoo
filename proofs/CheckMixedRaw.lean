import Jihoo.MixedRawAdmission
import Jihoo.TypingInput

open Jihoo.GraphCertificates Jihoo.GraphCertificates.TypingInput
open Jihoo.CoreBridge.Checked.Admission

def main (args : List String) : IO UInt32 := do
  try
    let snapshot ← canonicalSnapshot (← input args)
    let some _ := admitSnapshot snapshot |
      throw (IO.userError "unsupported snapshot, exact type mismatch, or resource bound")
    IO.println "mixed raw snapshot accepted"
    return 0
  catch error =>
    IO.eprintln s!"mixed raw snapshot rejected: {error}"
    return 1
