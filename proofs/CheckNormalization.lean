import Jihoo.HeadNormalizationCodec
import Jihoo.TypingInput

open Jihoo.GraphCertificates Jihoo.GraphCertificates.TypingInput

private def scanSnapshot (bytes : ByteArray) (start used : Nat) : Option (Nat × Nat) := do
  let cursor ← scanFields bytes start 3
  let (count, _) ← scanNat bytes cursor
  if used + count > HeadNormalization.totalNodeLimit then none else do
    let cursor ← scanGraph bytes cursor
    pure (cursor, used + count)

private def canonicalChain (bytes : ByteArray) : IO HeadNormalization.Certificate := do
  let shape := do
    let cursor ← scanFields bytes 0 1
    let (count, cursor) ← scanNat bytes cursor
    if count > HeadNormalization.stepLimit then none else do
      let mut cursor := cursor
      let mut nodes := 0
      for _ in [:count] do
        cursor ← scanFields bytes cursor 1
        let (next, used) ← scanSnapshot bytes cursor nodes
        let (next, used) ← scanSnapshot bytes next used
        cursor ← scanVector bytes next depthLimit
        nodes := used
      if cursor = bytes.size then some () else none
  unless shape.isSome do throw (IO.userError "chain shape/count/aggregate node/path limit")
  let some cs := HeadNormalization.Wire.decode bytes |
    throw (IO.userError "noncanonical normalization witness")
  return cs

private def endpoint (s : String) : IO Nat := do
  if s.length > 20 then throw (IO.userError "literal too long")
  let some n := s.toNat? | throw (IO.userError "invalid literal")
  if n ≥ Jihoo.CoreBridge.wordBound then throw (IO.userError "literal out of range")
  return n

def main (args : List String) : IO UInt32 := do
  try
    let isPrefix := args == ["--prefix"]
    let claim ← match args with
      | ["--prefix"] => pure none
      | [] => pure none
      | [relation, left, right] => do
          let m ← endpoint left
          let n ← endpoint right
          match relation with
          | "eq" => pure (some (Typing.Evidence.Claim.equal m n))
          | "lt" => pure (some (Typing.Evidence.Claim.less m n))
          | _ => throw (IO.userError "expected eq or lt")
      | _ => throw (IO.userError "expected optional eq|lt LEFT RIGHT")
    let bytes ← input []
    let [beforeBytes, afterBytes, typingBytes, chainBytes] := bytes.data.toList.splitOn 10 |
      throw (IO.userError "expected input LF output LF typing LF chain")
    let before ← canonicalSnapshot beforeBytes.toByteArray
    let after ← canonicalSnapshot afterBytes.toByteArray
    let typing ← canonical typingBytes.toByteArray
    let cs ← canonicalChain chainBytes.toByteArray
    let valid := match claim with
      | none => if isPrefix then HeadNormalization.validatePrefix before after typing cs
          else HeadNormalization.validate before after typing cs
      | some q => HeadNormalization.validateLiteral before after typing cs q
    unless valid do throw (IO.userError "invalid typing, continuity, head step, final normality or work bound")
    IO.println (if isPrefix then "typed head normalization prefix accepted" else if claim.isSome then "finite head normalization and literal truth accepted"
      else "finite head normalization accepted")
    return 0
  catch error =>
    IO.eprintln s!"head normalization rejected: {error}"
    return 1
