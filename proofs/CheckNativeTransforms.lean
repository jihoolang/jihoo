import Jihoo.NativeWire
import Jihoo.NativePartialRenaming
import Jihoo.TypingInput

/-! Differential adapter for retained actual Core.shift/substitute/rewrite
observations. The expected tree transformations are the mechanized definitions,
not an independent Python reimplementation. IO/source association is trusted. -/
open Jihoo.NativeKernel NativeArena NativeWire

private def snapshot (text : String) : IO Snapshot := do
  let some s := decodeSnapshot text.toUTF8 | throw (IO.userError "invalid canonical arena")
  unless graphValid s.arena do throw (IO.userError "invalid complete graph")
  return s

private def decoded (s : Snapshot) (root : Nat) : IO Term := do
  let some t := decode 128 s.arena root | throw (IO.userError "invalid selected root")
  return t

private def checkLine (line : String) : IO Unit := do
  let [countText, name, mode, status, beforeText, afterText] := line.splitOn "\t" |
    throw (IO.userError "invalid transform observation shape")
  let some count := countText.toNat? | throw (IO.userError "invalid vector count")
  unless count = 0 ∨ count = 1 ∨ count = 3 do throw (IO.userError "unexpected vector count")
  let before ← snapshot beforeText
  let after ← snapshot afterText
  unless before.termRoot = after.termRoot do throw (IO.userError "original root changed")
  unless before.arena.toList = after.arena.toList.take before.arena.size do
    throw (IO.userError "native operation changed existing arena entries")
  let body ← decoded before before.termRoot
  let value ← decoded before before.typeRoot
  let expected ← match mode with
    | "shift-up" => pure (PartialRenaming.shift 2 0 body)
    | "shift-down" => pure (PartialRenaming.shift (-1) 0 body)
    | "substitute" => pure (some (body.subst (single value)))
    | "rewrite" => pure (some (PartialRenaming.rewrite 0 value body))
    | _ => throw (IO.userError "unknown native operation")
  if status = "1" then
    let result ← decoded after after.typeRoot
    unless expected = some result do throw (IO.userError s!"{name}/{count}/{mode}: result differs")
  else if status = "0" then
    unless expected = none do throw (IO.userError s!"{name}/{count}/{mode}: unexpected rejection")
  else throw (IO.userError "invalid result status")

def main (args : List String) : IO UInt32 := do
  try
    let bytes ← Jihoo.GraphCertificates.TypingInput.input args
    let some text := String.fromUTF8? bytes | throw (IO.userError "invalid observation text")
    let lines := (text.splitOn "\n").filter (· != "")
    unless lines.length = 660 do throw (IO.userError "incomplete constructor/operation coverage")
    for line in lines do checkLine line
    IO.println "native transforms: 660 actual Core operations match proved binding transformations"
    return 0
  catch error =>
    IO.eprintln s!"native transform correspondence rejected: {error}"
    return 1
