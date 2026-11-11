import Jihoo.MirCallerValidation
import Jihoo.TypingInput
import Jihoo.GraphCertificateJson

/-! Test adapter only. JSON parsing/export association is trusted; graph
recognition and its execution theorem begin with the parsed immutable graph. -/
open Lean Jihoo.ScopedLend.Graph
namespace CheckMirCaller

private def bit (j : Json) : Except String Bool := do
  match ← j.getNat? with
  | 0 => return false
  | 1 => return true
  | _ => throw "invalid mode bit"

private def node (j : Json) : Except String Node := do
  match (← j.getArr?).toList with
  | [.str "opaque"] => return .opaque
  | [.str "var", k] => return .var (← k.getNat?)
  | [.str "natural", v] => return .natural (← v.getNat?)
  | [.str "integer", v] => return .integer (← v.getNat?)
  | [.str "i64"] => return .i64
  | [.str "u64"] => return .u64
  | [.str "buffer", a] => return .buffer (← a.getNat?)
  | [.str "ref", a] => return .ref (← a.getNat?)
  | [.str "pi", e, a, b] => return .pi (← bit e) (← a.getNat?) (← b.getNat?)
  | [.str "lam", e, a, b] => return .lam (← bit e) (← a.getNat?) (← b.getNat?)
  | [.str "alloc", a, b] => return .alloc (← a.getNat?) (← b.getNat?)
  | [.str "app", a, b] => return .app (← a.getNat?) (← b.getNat?)
  | [.str "index", a, b, c] => return .index (← a.getNat?) (← b.getNat?) (← c.getNat?)
  | [.str "decide", a, b] => return .decide (← a.getNat?) (← b.getNat?)
  | [.str "strict", a, b] => return .strict (← a.getNat?) (← b.getNat?)
  | [.str "borrow", a] => return .borrow (← a.getNat?)
  | [.str "lend", a, b, c] => return .lend (← a.getNat?) (← b.getNat?) (← c.getNat?)
  | [.str "free", a, b] => return .free (← a.getNat?) (← b.getNat?)
  | [.str "store", a, b, c, d] => return .store (← a.getNat?) (← b.getNat?) (← c.getNat?) (← d.getNat?)
  | [.str "ifLt", a, b, c, d] => return .ifLt (← a.getNat?) (← b.getNat?) (← c.getNat?) (← d.getNat?)
  | _ => throw "unsupported row or arity"

private def ty (j : Json) : Except String Jihoo.BoundedMir.Ty := do
  match ← j.getStr? with
  | "i64" => return .i64 | "u64" => return .u64 | "bool" => return .bool
  | "ptr" => return .ptr | "unit" => return .unit
  | _ => throw "unsupported local type"

private def place (j : Json) : Except String Jihoo.BoundedMir.Place := do
  let [slot, deref] := (← j.getArr?).toList | throw "place arity"
  return ⟨← slot.getNat?, ← bit deref⟩

private def operand (j : Json) : Except String Jihoo.BoundedMir.Operand := do
  match (← j.getArr?).toList with
  | [.str "copy", p] => return .copy (← place p)
  | [.str "int", .str "i64", n] => return .constant (.i64 (← n.getNat?))
  | [.str "int", .str "u64", n] => return .constant (.u64 (← n.getNat?))
  | [.str "bool", b] => return .constant (.boolean (← bit b))
  | [.str "unit"] => return .constant .unit
  | _ => throw "unsupported operand or arity"

private def rvalue (j : Json) : Except String Jihoo.BoundedMir.Rvalue := do
  match (← j.getArr?).toList with
  | [.str "use", a] => return .use (← operand a)
  | [.str "cast", a, .str "u64"] => return .ptrCast (← operand a)
  | [.str "offset", a, b] => return .offset (← operand a) (← operand b)
  | [.str "add", a, b] => return .bin .add (← operand a) (← operand b)
  | [.str "mul", a, b] => return .bin .mul (← operand a) (← operand b)
  | [.str "lt", a, b] => return .bin .lt (← operand a) (← operand b)
  | [.str "ne", a, b] => return .bin .ne (← operand a) (← operand b)
  | _ => throw "unsupported rvalue or arity"

private def statement (j : Json) : Except String Jihoo.BoundedMir.Stmt := do
  let [p, value] := (← j.getArr?).toList | throw "statement arity"
  return ⟨← place p, ← rvalue value⟩

private def caseTarget (j : Json) : Except String (Nat × Nat) := do
  let [value, target] := (← j.getArr?).toList | throw "switch case arity"
  return (← value.getNat?, ← target.getNat?)

private def term (j : Json) : Except String Jihoo.BoundedMir.Term := do
  match (← j.getArr?).toList with
  | [.str "goto", b] => return .goto (← b.getNat?)
  | [.str "switch", value, cases, other] =>
      let rows ← cases.getArr?
      if rows.size > 512 then throw "switch size"
      return .switch (← operand value) (← rows.toList.mapM caseTarget) (← other.getNat?)
  | [.str "assert", value, next] => return .assert (← operand value) (← next.getNat?)
  | [.str "malloc", bytes, dest, next] => return .malloc (← operand bytes) (← place dest) (← next.getNat?)
  | [.str "free", pointer, dest, next] => return .free (← operand pointer) (← place dest) (← next.getNat?)
  | [.str "return"] => return .ret
  | _ => throw "unsupported terminator or arity"

private def block (j : Json) : Except String Jihoo.BoundedMir.Block := do
  let [statements, ending] := (← j.getArr?).toList | throw "block arity"
  let statements ← statements.getArr?
  if statements.size > 4096 then throw "block statement size"
  return ⟨← statements.mapM statement, ← term ending⟩

/-- This envelope is deeper than the source-only certificate format. Bound its
nesting before invoking Lean's JSON parser; arrays only, ASCII/no escapes,
20-digit natural tokens. It is a trusted parser preflight, not a kernel theorem. -/
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
  let [schema, source, mir, fuel] := (← json.getArr?).toList | throw "envelope arity"
  if (← schema.getNat?) != 1 then throw "envelope schema"
  let [sourceSchema, root, type, nodes] := (← source.getArr?).toList | throw "source arity"
  if (← sourceSchema.getNat?) != 1 then throw "source schema"
  let nodes ← nodes.getArr?
  if nodes.size > 4096 then throw "source graph size"
  let graph ← nodes.mapM node
  let [mirSchema, locals, blocks] := (← mir.getArr?).toList | throw "MIR arity"
  if (← mirSchema.getNat?) != 1 then throw "MIR schema"
  let locals ← locals.getArr?
  let blocks ← blocks.getArr?
  if locals.size > 512 || blocks.size > 512 then throw "MIR size"
  let mut statementCount := 0
  for row in blocks do
    let [statements, _] := (← row.getArr?).toList | throw "block arity"
    statementCount := statementCount + (← statements.getArr?).size
    if statementCount > 4096 then throw "total statement bound"
  let code : Jihoo.BoundedMir.Code := ⟨← locals.mapM ty, ← blocks.mapM block⟩
  let fuel ← fuel.getNat?
  if fuel > 10000 then throw "fuel bound"
  let some _ := Jihoo.MirCallerValidation.admit graph (← root.getNat?) (← type.getNat?) code fuel
    | throw "source/MIR admission or result/lifecycle mismatch"

end CheckMirCaller

def main (args : List String) : IO UInt32 := do
  try
    unless args.isEmpty do throw (IO.userError "stdin only")
    let bytes ← Jihoo.GraphCertificates.TypingInput.readBounded (← IO.getStdin)
    let some text := String.fromUTF8? bytes | throw (IO.userError "invalid UTF8")
    match CheckMirCaller.check text with
    | .error e => throw (IO.userError e)
    | .ok _ => IO.println "mir-caller accepted"; return 0
  catch e => IO.eprintln s!"mir-caller rejected: {e}"; return 1
