import Jihoo.CheckedCoreNormalizationCodec
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
    let (preflight, ds, fs) ← match args with
      | ["--input", d, f] => pure (true, d, f)
      | [d, f] => pure (false, d, f)
      | _ => throw (IO.userError "expected [--input] DEPTH FUEL")
    let depth ← number ds
    let fuel ← number fs
    let bytes ← input []
    let parts := bytes.data.toList.splitOn 10
    if preflight then
      let [beforeBytes, typingBytes] := parts | throw (IO.userError "expected input LF typing")
      let before ← canonicalSnapshot beforeBytes.toByteArray
      let typing ← canonical typingBytes.toByteArray
      unless CoreNormal.admit before typing depth fuel do
        throw (IO.userError "invalid typing, unsupported computation or resource limit")
      IO.println "Core.normal input admitted"
    else
      let [beforeBytes, afterBytes, typingBytes, recordBytes] := parts |
        throw (IO.userError "expected input LF output LF typing LF record")
      let before ← canonicalSnapshot beforeBytes.toByteArray
      let after ← canonicalSnapshot afterBytes.toByteArray
      let typing ← canonical typingBytes.toByteArray
      let record ← canonicalRecord recordBytes.toByteArray
      unless CoreNormal.validate before after typing depth fuel record do
        throw (IO.userError "request/snapshot mismatch or invalid normalization")
      IO.println "checked Core.normal output accepted"
    return 0
  catch error =>
    IO.eprintln s!"Core.normal rejected: {error}"
    return 1
