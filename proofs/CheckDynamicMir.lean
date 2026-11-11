import Jihoo.DynamicMirSnapshot
import Jihoo.DynamicMirCorrespondence
import Jihoo.TypingInput
import Jihoo.GraphCertificateJson

/-! Test adapter for one fixed parametric theorem association. No sample runtime
inputs are accepted. Complete JSON structural equality binds the native source
and MIR snapshots to the retained formal fixtures. Parsing/export fidelity is
trusted, not a general compiler-refinement theorem. -/
open Lean
namespace CheckDynamicMir

private def lexicalGuard (text : String) : Bool := Id.run do
  let mut inside := false
  let mut depth := 0
  let mut digits := 0
  let mut length := 0
  for c in text.toList do
    if inside then
      if c == '"' then inside := false
      else
        if c == '\\' || c.toNat > 127 || length ≥ 64 then return false
        length := length + 1
    else if c == '"' then
      if digits > 0 then return false
      inside := true
      length := 0
    else if c == '[' then
      depth := depth + 1
      if depth > 16 then return false
      digits := 0
    else if c == ']' then
      if depth == 0 then return false
      depth := depth - 1
      digits := 0
    else if c.isDigit then
      digits := digits + 1
      if digits > 20 then return false
    else
      if c == '{' || c == '}' || c == '.' || c == '+' || c == '-' ||
          ((c == 'e' || c == 'E') && digits > 0) then return false
      digits := 0
  return !inside && depth == 0


private def check (text : String) : Except String Unit := do
  if !lexicalGuard text then throw "JSON bound/syntax"
  let json ← Json.parse text
  if json != Jihoo.DynamicMirSnapshot.expected then
    throw "complete source/MIR/entry fixture mismatch"

end CheckDynamicMir

def main (args : List String) : IO UInt32 := do
  try
    unless args.isEmpty do throw (IO.userError "stdin only")
    let bytes ← Jihoo.GraphCertificates.TypingInput.readBounded (← IO.getStdin)
    let some text := String.fromUTF8? bytes | throw (IO.userError "invalid UTF8")
    match CheckDynamicMir.check text with
    | .error e => throw (IO.userError e)
    | .ok _ => IO.println "dynamic-mir accepted"; return 0
  catch e => IO.eprintln s!"dynamic-mir rejected: {e}"; return 1
