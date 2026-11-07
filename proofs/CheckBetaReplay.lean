import Jihoo.TypedBetaReplayCodec
import Jihoo.TypingInput

open Jihoo.GraphCertificates Jihoo.GraphCertificates.TypingInput

private def canonicalReplay (bytes : ByteArray) : IO TypedBeta.Certificate := do
  let shape := do
    let cursor ← scanFields bytes 0 1
    let cursor ← scanFields bytes cursor 3
    let cursor ← scanGraph bytes cursor
    let cursor ← scanFields bytes cursor 3
    let cursor ← scanGraph bytes cursor
    let cursor ← scanVector bytes cursor depthLimit
    if cursor = bytes.size then some () else none
  unless shape.isSome do throw (IO.userError "invalid replay shape or bounds")
  let some c := TypedBeta.Wire.decode bytes |
    throw (IO.userError "invalid or noncanonical beta replay")
  return c

def main (args : List String) : IO UInt32 := do
  try
    -- Each argument is an independent requested child index, never inferred
    -- from the artifact. No arguments requests one head beta contraction.
    if args.length > depthLimit then throw (IO.userError "path too long")
    let path ← args.mapM fun s => do
      if s.length > 10 then throw (IO.userError "path index too long")
      let some n := s.toNat? | throw (IO.userError "invalid path index")
      if n ≥ nodeLimit then throw (IO.userError "path index too large")
      pure n
    let bytes ← input []
    let [beforeBytes, afterBytes, typingBytes, replayBytes] := bytes.data.toList.splitOn 10 |
      throw (IO.userError "expected four canonical artifacts separated by LF")
    let before ← canonicalSnapshot beforeBytes.toByteArray
    let after ← canonicalSnapshot afterBytes.toByteArray
    let typing ← canonical typingBytes.toByteArray
    let replay ← canonicalReplay replayBytes.toByteArray
    unless TypedBeta.validate before after typing path replay do
      throw (IO.userError "snapshot/request mismatch, invalid typing or non-step")
    IO.println "snapshot-bound typed beta replay accepted"
    return 0
  catch error =>
    IO.eprintln s!"typed beta replay rejected: {error}"
    return 1
