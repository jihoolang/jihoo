import Jihoo.NativeACUBoundedNormalizer
import Jihoo.NativeWire
import Jihoo.TypingInput

/-! Differential observations from the actual Core.normal implementation.
Source execution/export/allocation association remains regression evidence;
normalizer conversion and forward soundness are independent universal proofs. -/
open Jihoo.NativeKernel NativeArena NativeWire

private def snapshot (text : String) : IO Snapshot := do
  let some s := decodeSnapshot text.toUTF8 | throw (IO.userError "invalid canonical native arena")
  unless graphValid s.arena do throw (IO.userError "invalid complete native graph")
  return s

private def decoded (s : Snapshot) (root : Nat) : IO Term := do
  let some term := decode 128 s.arena root | throw (IO.userError "invalid native root")
  return term

private def checkLine (line : String) : IO Nat := do
  let [keyText,beforeText,afterText] := line.splitOn "\t" |
    throw (IO.userError "invalid full ACU observation shape")
  let some key := keyText.toNat? | throw (IO.userError "invalid case key")
  unless key < 204 do throw (IO.userError "case outside native grid")
  let before ← snapshot beforeText
  let after ← snapshot afterText
  unless before.ghost && after.ghost do throw (IO.userError "expected pure normalization")
  unless before.termRoot = after.termRoot do throw (IO.userError "original native root changed")
  unless before.arena.toList = after.arena.toList.take before.arena.size do
    throw (IO.userError "normalization changed an existing arena entry")
  let input ← decoded before before.termRoot
  let result ← decoded after after.typeRoot
  let some canonical := ACU.Bounded.run 32 4096 input | throw (IO.userError "full ACU normalization exceeded budget")
  unless ACU.Bounded.equal 32 4096 input result do throw (IO.userError "actual Core.normal output is not proved convertible")
  if key < 202 then
    unless canonical = result do throw (IO.userError s!"full ACU result differs at case {key}")
  else if key = 202 then
    unless canonical != result do throw (IO.userError "missing selected-read normalization boundary")
  else
    unless canonical != result do throw (IO.userError "missing proof-slot ordering boundary")
    let p1 := Term.pack (.var 7) (.var 2) (.var 1)
    let p2 := Term.pack (.var 7) (.var 2) (.var 2)
    if ACU.Bounded.equal 32 4096 p1 p2 then throw (IO.userError "raw Pack proof irrelevance was admitted")
  return key

def main (args : List String) : IO UInt32 := do
  try
    let bytes ← Jihoo.GraphCertificates.TypingInput.input args
    let some text := String.fromUTF8? bytes | throw (IO.userError "invalid native observations")
    let lines := (text.splitOn "\n").filter (· != "")
    unless lines.length = 204 do throw (IO.userError "incomplete full ACU observation count")
    let keys ← lines.mapM checkLine
    unless keys.eraseDups.length = 204 do throw (IO.userError "duplicate full ACU case keys")
    IO.println "native full ACU: 204 actual outputs convert; 202 exact forms match; read and proof-slot boundaries checked"
    return 0
  catch error =>
    IO.eprintln s!"native full ACU correspondence rejected: {error}"
    return 1
