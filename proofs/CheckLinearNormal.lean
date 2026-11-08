import Jihoo.CheckedLinearNormalization
import Jihoo.TypingInput
open Jihoo.GraphCertificates Jihoo.GraphCertificates.TypingInput

private def canonicalRecord (bytes : ByteArray) : IO CoreNormal.Certificate := do
  let shape := do
    let cursor ← scanFields bytes 0 3
    let cursor ← scanFields bytes cursor 3
    let cursor ← scanGraph bytes cursor
    let cursor ← scanFields bytes cursor 3
    let cursor ← scanGraph bytes cursor
    if cursor = bytes.size then some () else none
  unless shape.isSome do throw (IO.userError "record shape or bounds")
  let some c := CoreNormal.Wire.decode bytes | throw (IO.userError "noncanonical normal record")
  return c

private def number (s : String) : IO Nat := do
  if s.length > 3 then throw (IO.userError "excessive parameter")
  let some n := s.toNat? | throw (IO.userError "invalid parameter")
  return n

def main (args : List String) : IO UInt32 := do
  try
    let (preflight, ns, ds, fs) ← match args with
      | ["--input", n, d, f] => pure (true, n, d, f)
      | [n, d, f] => pure (false, n, d, f)
      | _ => throw (IO.userError "expected [--input] ARITY DEPTH FUEL")
    let arity ← number ns
    let depth ← number ds
    let fuel ← number fs
    let bytes ← input []
    if preflight then
      let before ← canonicalSnapshot bytes
      unless LinearNormal.admit before arity depth fuel do
        throw (IO.userError "unsupported linear input or resource limit")
      IO.println "linear input admitted"
    else
      let [bb, ab, rb] := bytes.data.toList.splitOn 10 |
        throw (IO.userError "expected input LF output LF record")
      let before ← canonicalSnapshot bb.toByteArray
      let after ← canonicalSnapshot ab.toByteArray
      let record ← canonicalRecord rb.toByteArray
      unless LinearNormal.validate before after arity depth fuel record do
        throw (IO.userError "request mismatch or unequal linear semantics")
      IO.println "linear Core.normal result accepted"
    return 0
  catch error =>
    IO.eprintln s!"linear Core.normal rejected: {error}"
    return 1
