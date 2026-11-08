import Jihoo.CheckedApplicationSpine
import Jihoo.TypingInput
open Jihoo.GraphCertificates Jihoo.GraphCertificates.TypingInput

private def root (s : String) : IO Nat := do
  if s.length > 10 then throw (IO.userError "excessive root")
  let some n := s.toNat? | throw (IO.userError "invalid root")
  if n ≥ idBound then throw (IO.userError "root exceeds ID bound")
  return n

private def pairs : List (List UInt8) → IO (List (Typing.Wire.Snapshot × Typing.Wire.Snapshot))
  | [] => pure []
  | n :: i :: rest => do
      let normal ← canonicalSnapshot n.toByteArray
      let inferred ← canonicalSnapshot i.toByteArray
      return (normal, inferred) :: (← pairs rest)
  | _ => throw (IO.userError "expected normalized/inferred pairs")

def main (args : List String) : IO UInt32 := do
  try
    let [f, ft, a, it, rt] := args |
      throw (IO.userError "expected INITIAL_TERM INITIAL_TYPE FINAL_TERM FINAL_INFERRED_TYPE REQUESTED_TYPE")
    let roots : ApplicationSpine.Roots := ⟨← root f, ← root ft, ← root a, ← root it, ← root rt⟩
    let bytes ← input []
    let lines := bytes.data.toList.splitOn 10
    if lines.length < 4 || lines.length > 2 * ApplicationSpine.linkLimit + 2 then
      throw (IO.userError "expected 1..16 application links")
    let initial ← canonicalSnapshot lines.head!.toByteArray
    let requested ← canonicalSnapshot lines.getLast!.toByteArray
    let steps ← pairs (lines.drop 1 |>.take (lines.length - 2))
    unless ApplicationSpine.validate ⟨initial, steps, requested⟩ roots do
      throw (IO.userError "association, type/substitution mismatch, unsupported spine or resource limit")
    IO.println "application spine accepted"
    return 0
  catch error =>
    IO.eprintln s!"application spine rejected: {error}"
    return 1
