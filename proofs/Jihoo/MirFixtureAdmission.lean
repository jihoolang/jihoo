import Lean

/-! Bounded strict JSON admission for complete theorem-backed fixture snapshots.
This compares retained rows; it is not a general MIR decoder or compiler proof. -/
namespace Jihoo.MirFixtureAdmission
open Lean

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


def check (expected : Json) (text : String) : Except String Unit := do
  if !lexicalGuard text then throw "JSON bound/syntax"
  let json ← Json.parse text
  if json != expected then
    throw "complete source/MIR/entry fixture mismatch"


end Jihoo.MirFixtureAdmission
