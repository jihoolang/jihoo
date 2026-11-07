import Jihoo.TypingInput

open Jihoo.GraphCertificates Jihoo.GraphCertificates.TypingInput

def main (args : List String) : IO UInt32 := do
  try
    if args == ["--snapshot"] then
      let bytes ← input []
      let [snapshotBytes, certificateBytes] := bytes.data.toList.splitOn 10 |
        throw (IO.userError "expected snapshot LF certificate, with exactly one newline")
      let snapshot ← canonicalSnapshot snapshotBytes.toByteArray
      let certificate ← canonical certificateBytes.toByteArray
      unless Typing.Wire.validateAgainst snapshot certificate do
        throw (IO.userError "snapshot graph/root mismatch or invalid typing derivation")
      IO.println "snapshot-bound canonical typing artifact accepted"
    else
      let certificate ← canonical (← input args)
      unless Typing.validate certificate do
        throw (IO.userError "invalid graph, derivation, exact roots, context, or work bound")
      IO.println "canonical typing artifact accepted"
    return 0
  catch error =>
    IO.eprintln s!"canonical typing artifact rejected: {error}"
    return 1
