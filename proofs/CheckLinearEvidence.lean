import Jihoo.CheckedLinearEvidence
import Jihoo.TypingInput
open Jihoo.GraphCertificates Jihoo.GraphCertificates.TypingInput

private def root (s : String) : IO Nat := do
  if s.length > 10 then throw (IO.userError "excessive root")
  let some n := s.toNat? | throw (IO.userError "invalid root")
  if n ≥ idBound then throw (IO.userError "root exceeds ID bound")
  return n

def main (args : List String) : IO UInt32 := do
  try
    let [ts, as] := args | throw (IO.userError "expected TERM_ROOT TYPE_ROOT")
    let t ← root ts
    let a ← root as
    let bytes ← input []
    let s ← canonicalSnapshot bytes
    unless LinearEvidenceCheck.validate s t a do
      throw (IO.userError "root mismatch, unsupported evidence, false claim or resource limit")
    IO.println "closed linear evidence accepted"
    return 0
  catch error =>
    IO.eprintln s!"linear evidence rejected: {error}"
    return 1
