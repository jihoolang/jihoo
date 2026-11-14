import Jihoo.NativeEnvironmentContextualPreservation
import Jihoo.NativeUnifiedAdmission
import Jihoo.TypingInput

/-! Actual-source regression adapter; source/IO association remains outside
the universal delta/ACU forward, confluence and bounded-soundness proofs. -/
open Jihoo.NativeKernel

def main (args : List String) : IO UInt32 := do
  try
    let bytes ← Jihoo.GraphCertificates.TypingInput.input args
    let some text := String.fromUTF8? bytes | throw (IO.userError "invalid UTF8")
    let [programText, beforeText, afterText] := text.splitOn "\t" |
      throw (IO.userError "expected program and before/after arenas")
    let some program := NativeFamilyWire.decodeSnapshot programText.toUTF8 |
      throw (IO.userError "invalid canonical mixed program")
    let some (definitions, families) := NativeFamilyWire.decodeProgram program |
      throw (IO.userError "invalid mixed graph or roots")
    let some env := UnifiedProgram.checkProgram 64 128 definitions (families.map NativeUnifiedAdmission.declaration) |
      throw (IO.userError "mixed admission rejected")
    let some before := NativeWire.decodeSnapshot beforeText.toUTF8 |
      throw (IO.userError "invalid before arena")
    let some after := NativeWire.decodeSnapshot afterText.toUTF8 |
      throw (IO.userError "invalid after arena")
    unless NativeWire.graphValid before.arena && NativeWire.graphValid after.arena do
      throw (IO.userError "invalid complete graph")
    unless before.ghost && after.ghost && before.termRoot == before.typeRoot && before.termRoot == after.termRoot do
      throw (IO.userError "invalid observation mode or original root")
    unless program.arena.toList == before.arena.toList &&
        before.arena.toList == after.arena.toList.take before.arena.size do
      throw (IO.userError "native arena prefix changed")
    let some roots := program.definitions.getLast? | throw (IO.userError "missing final declaration")
    unless roots.valueRoot == before.termRoot do throw (IO.userError "wrong observed source root")
    let some term := NativeArena.decode 128 before.arena before.termRoot | throw (IO.userError "bad input root")
    let some result := NativeArena.decode 128 after.arena after.typeRoot | throw (IO.userError "bad output root")
    unless Environment.Conversion.equal env 64 term result do
      throw (IO.userError "native normal output fails proved delta/ACU comparator")
    let some declaration := env.globals.toList.getLast? | throw (IO.userError "missing interpreted declaration")
    let some sort := Environment.Checker.sort 64 env [] declaration.type |
      throw (IO.userError "interpreted declaration has no checked sort")
    unless Environment.Checker.check 64 env [] (Definitions.bodyMode sort) term declaration.type do
      throw (IO.userError "original global term fails installed typing checker")
    unless Environment.Checker.check 64 env [] true result declaration.type do
      throw (IO.userError "normal output fails original-type ghost checking")
    IO.println "native checked delta/ACU observation accepted"
    return 0
  catch error =>
    IO.eprintln s!"native delta correspondence rejected: {error}"
    return 1
