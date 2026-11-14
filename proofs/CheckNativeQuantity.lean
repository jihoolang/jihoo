import Jihoo.NativeWire
import Jihoo.NativeQuantityAtoms
import Jihoo.TypingInput

/-! Native observation adapter. A row retains its entire native arena, context
type references/erasure flags and queried variable. Runtime_uses alone does not
check local binder validity: deliberate stricter local-scope cases are recorded
separately from agreement. This fixture is not a source execution theorem. -/
open Jihoo.NativeKernel NativeArena NativeWire

private def number (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError "invalid natural metadata")

private def checkLine (line : String) : IO String := do
  let [name, policy, queryText, contextText, status, arenaText] := line.splitOn "\t" |
    throw (IO.userError "invalid quantity observation shape")
  let some snapshot := decodeSnapshot arenaText.toUTF8 |
    throw (IO.userError "invalid canonical native arena")
  unless graphValid snapshot.arena do throw (IO.userError "invalid complete arena")
  let some term := decode 128 snapshot.arena snapshot.termRoot |
    throw (IO.userError "invalid native selected root")
  let context := contextText.splitOn ","
  let query ← number queryText
  unless query < context.length do throw (IO.userError "queried variable is outside context")
  for binding in context do
    let [rootText, erased] := binding.splitOn ":" |
      throw (IO.userError "invalid context binding")
    unless erased = "0" ∨ erased = "1" do throw (IO.userError "invalid context erasure flag")
    let root ← number rootText
    let some _ := decode 128 snapshot.arena root |
      throw (IO.userError "context type is not decodable")
  let native ← if status = "reject" then pure none else do
    let ["ok", countText] := status.splitOn ":" |
      throw (IO.userError "invalid native quantity status")
    pure (some (← number countText))
  let projection := NativeQuantity.project 128 term
  let actual := projection.bind (Jihoo.Quantity.Control.demand query)
  match policy with
  | "equal" =>
      unless actual = native do throw (IO.userError s!"{name}: quantity count/rejection differs")
  | "local-gap" =>
      unless projection.isSome ∧ actual = none ∧ native.isSome do
        throw (IO.userError s!"{name}: expected stricter local scope rejection")
  | "unsupported" =>
      unless projection = none ∧ native.isSome do
        throw (IO.userError s!"{name}: expected explicit projection boundary")
  | _ => throw (IO.userError "unknown comparison policy")
  return policy

def main (args : List String) : IO UInt32 := do
  try
    let bytes ← Jihoo.GraphCertificates.TypingInput.input args
    let some text := String.fromUTF8? bytes | throw (IO.userError "invalid observation text")
    let lines := (text.splitOn "\n").filter (· != "")
    unless lines.length = 40 do throw (IO.userError "incomplete quantity fixture")
    let mut agreements := 0
    let mut locals := 0
    let mut unsupported := 0
    let mut labels : List String := []
    for line in lines do
      let name := (line.splitOn "\t").head!
      if name ∈ labels then throw (IO.userError "duplicate quantity observation")
      labels := name :: labels
      let policy ← checkLine line
      if policy = "equal" then agreements := agreements + 1
      else if policy = "local-gap" then locals := locals + 1
      else unsupported := unsupported + 1
    unless agreements = 31 ∧ locals = 7 ∧ unsupported = 2 do
      throw (IO.userError "quantity coverage classification changed")
    IO.println "native quantity: 31 count/rejection agreements, 7 stricter local scope checks, 2 explicit call gaps"
    return 0
  catch error =>
    IO.eprintln s!"native quantity correspondence rejected: {error}"
    return 1
