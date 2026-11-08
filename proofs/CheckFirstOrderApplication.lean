import Jihoo.CheckedFirstOrderApplication
import Jihoo.TypingInput
open Jihoo.GraphCertificates Jihoo.GraphCertificates.TypingInput

private def root (s : String) : IO Nat := do
  if s.length > 10 then throw (IO.userError "excessive root")
  let some n := s.toNat? | throw (IO.userError "invalid root")
  if n ≥ idBound then throw (IO.userError "root exceeds ID bound")
  return n

def main (args : List String) : IO UInt32 := do
  try
    let [f, ft, nt, a, it, rt] := args |
      throw (IO.userError "expected FUNCTION FUNCTION_TYPE NORMAL_TYPE APPLICATION INFERRED_TYPE REQUESTED_TYPE")
    let roots : FirstOrderApplication.Roots := ⟨← root f, ← root ft, ← root nt, ← root a, ← root it, ← root rt⟩
    let bytes ← input []
    let [fb, nb, ib, rb] := bytes.data.toList.splitOn 10 |
      throw (IO.userError "expected function LF normalized LF inferred LF requested")
    let trace : FirstOrderApplication.Trace := ⟨← canonicalSnapshot fb.toByteArray,
      ← canonicalSnapshot nb.toByteArray, ← canonicalSnapshot ib.toByteArray,
      ← canonicalSnapshot rb.toByteArray⟩
    unless FirstOrderApplication.validate trace roots do
      throw (IO.userError "association, type/substitution mismatch, unsupported application or resource limit")
    IO.println "first-order application accepted"
    return 0
  catch error =>
    IO.eprintln s!"first-order application rejected: {error}"
    return 1
