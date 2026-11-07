import Jihoo.TypingEvidence
import Jihoo.TypingInput

open Jihoo.GraphCertificates Jihoo.GraphCertificates.TypingInput

private def endpoint (s : String) : IO Nat := do
  if s.length > 20 then throw (IO.userError "literal exceeds 20 digits")
  let some n := s.toNat? | throw (IO.userError "invalid literal endpoint")
  if n ≥ Jihoo.CoreBridge.wordBound then throw (IO.userError "literal exceeds U64 bound")
  return n

def main (args : List String) : IO UInt32 := do
  try
    let [relation, left, right] := args |
      throw (IO.userError "expected eq|lt LEFT RIGHT; stdin is snapshot LF typing")
    let m ← endpoint left
    let n ← endpoint right
    let q ← match relation with
      | "eq" => pure (Typing.Evidence.Claim.equal m n)
      | "lt" => pure (Typing.Evidence.Claim.less m n)
      | _ => throw (IO.userError "expected eq or lt")
    let bytes ← input []
    let [snapshotBytes, typingBytes] := bytes.data.toList.splitOn 10 |
      throw (IO.userError "expected exactly snapshot LF typing")
    let s ← canonicalSnapshot snapshotBytes.toByteArray
    let c ← canonical typingBytes.toByteArray
    unless Typing.Evidence.validate s c q do
      throw (IO.userError "invalid association/typing, nonliteral requested type, or unfinished head beta")
    IO.println "certified closed literal evidence accepted"
    return 0
  catch error =>
    IO.eprintln s!"literal evidence rejected: {error}"
    return 1
