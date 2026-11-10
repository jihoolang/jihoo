import Jihoo.VerifiedCore
import Jihoo.TypingInput

open Jihoo.GraphCertificates.TypingInput
open Jihoo.MixedProofFunctions.Checked.Snapshot

/-- Exact byte-bound response. No response is emitted before all parsing and
independent admission succeeds. The caller must compare the entire response,
including the original snapshot bytes and process status. -/
def main (args : List String) : IO UInt32 := do
  try
    unless args.isEmpty do throw (IO.userError "expected snapshot on stdin only")
    let bytes ← readBounded (← IO.getStdin)
    let snapshot ← canonicalSnapshot bytes
    let some _ := admitSnapshot snapshot |
      throw (IO.userError "unsupported, ill-typed, inexact or over-budget snapshot")
    let out ← IO.getStdout
    out.write "jihoo-verified-core-v1\n".toUTF8
    out.write bytes
    out.write "\n".toUTF8
    return 0
  catch error =>
    IO.eprintln s!"verified Core rejected: {error}"
    return 1
