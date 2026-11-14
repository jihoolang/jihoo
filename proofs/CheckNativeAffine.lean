import Jihoo.NativeAffineSum
import Jihoo.NativeWire
import Jihoo.TypingInput

/-! Actual Core.normal comparisons against the proved affine canonicalizer.
This adapter does not assume source execution or graph allocation refinement. -/
open Jihoo.NativeKernel NativeArena NativeWire

private def snapshot (text : String) : IO Snapshot := do
  let some s := decodeSnapshot text.toUTF8 | throw (IO.userError "invalid canonical affine arena")
  unless graphValid s.arena do throw (IO.userError "invalid complete affine graph")
  return s

private def decoded (s : Snapshot) (root : Nat) : IO Term := do
  let some term := decode 128 s.arena root | throw (IO.userError "invalid affine root")
  return term

private def checkLine (line : String) : IO Nat := do
  let [variablesText, literalsText, groupText, beforeText, afterText] := line.splitOn "\t" |
    throw (IO.userError "invalid affine observation shape")
  let some variables := variablesText.toNat? | throw (IO.userError "invalid variable count")
  let some literals := literalsText.toNat? | throw (IO.userError "invalid literal count")
  let some group := groupText.toNat? | throw (IO.userError "invalid grouping")
  unless variables < 5 ∧ literals < 6 ∧ group < 3 do throw (IO.userError "affine case outside grid")
  let before ← snapshot beforeText
  let after ← snapshot afterText
  unless before.ghost && after.ghost do throw (IO.userError "expected pure normalization")
  unless before.termRoot = after.termRoot do throw (IO.userError "original affine root changed")
  unless before.arena.toList = after.arena.toList.take before.arena.size do
    throw (IO.userError "normalization changed an existing arena entry")
  let input ← decoded before before.termRoot
  let result ← decoded after after.typeRoot
  let some form := AffineSum.canonical input | throw (IO.userError "input outside affine profile")
  unless form.emit = result do
    throw (IO.userError s!"affine result differs at {variables}/{literals}/{group}")
  return variables * 18 + literals * 3 + group

def main (args : List String) : IO UInt32 := do
  try
    let bytes ← Jihoo.GraphCertificates.TypingInput.input args
    let some text := String.fromUTF8? bytes | throw (IO.userError "invalid affine observations")
    let lines := (text.splitOn "\n").filter (· != "")
    unless lines.length = 90 do throw (IO.userError "incomplete affine observation count")
    let keys ← lines.mapM checkLine
    unless keys.eraseDups.length = 90 do throw (IO.userError "duplicate affine grid entries")
    IO.println "native affine sums: 90 actual Core.normal results match proved canonical forms"
    return 0
  catch error =>
    IO.eprintln s!"native affine correspondence rejected: {error}"
    return 1
