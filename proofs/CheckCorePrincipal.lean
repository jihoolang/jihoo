import Jihoo.CheckedCorePrincipal
import Jihoo.TypingInput
open Jihoo.GraphCertificates Jihoo.GraphCertificates.TypingInput

private def root (s : String) : IO Nat := do
  if s.length > 10 then throw (IO.userError "excessive root")
  let some n := s.toNat? | throw (IO.userError "invalid root")
  if n ≥ idBound then throw (IO.userError "root exceeds ID bound")
  return n

def main (args : List String) : IO UInt32 := do
  try
    let [ts, rs, ins] := args | throw (IO.userError "expected TERM_ROOT REQUESTED_ROOT INFERRED_ROOT")
    let t ← root ts
    let r ← root rs
    let i ← root ins
    let bytes ← input []
    let [rb, ib] := bytes.data.toList.splitOn 10 | throw (IO.userError "expected requested LF inferred")
    let requested ← canonicalSnapshot rb.toByteArray
    let inferred ← canonicalSnapshot ib.toByteArray
    unless CorePrincipalCheck.validate requested inferred t r i do
      throw (IO.userError "root/graph mismatch, unsupported proof, or incorrect principal type")
    IO.println "actual principal evidence types accepted"
    return 0
  catch error =>
    IO.eprintln s!"core principal rejected: {error}"
    return 1
