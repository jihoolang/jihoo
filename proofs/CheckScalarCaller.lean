import Jihoo.ScalarCoreCallers
import Jihoo.TypingInput
import Jihoo.GraphCertificateJson

/-! Test adapter only. JSON parsing/export association is trusted; graph
recognition and its execution theorem begin with the parsed immutable graph. -/
open Lean Jihoo.ScopedLend.Graph

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

private def check (text : String) : Except String Unit := do
  if !Jihoo.GraphCertificates.JsonAdapter.lexicalGuard text then throw "JSON bound/syntax"
  let json ← Json.parse text
  let [.num schema, root, type, graph] := (← json.getArr?).toList | throw "snapshot arity"
  if schema != 1 then throw "schema"
  let nodes ← graph.getArr?
  if nodes.size > 4096 then throw "graph size"
  let g ← nodes.mapM node
  let some _ := Jihoo.ScalarCoreCallers.admit g (← root.getNat?) (← type.getNat?) | throw "unsupported or invalid linear caller graph"

def main (args : List String) : IO UInt32 := do
  try
    unless args.isEmpty do throw (IO.userError "stdin only")
    let bytes ← Jihoo.GraphCertificates.TypingInput.readBounded (← IO.getStdin)
    let some text := String.fromUTF8? bytes | throw (IO.userError "invalid UTF8")
    match check text with
    | .error e => throw (IO.userError e)
    | .ok _ => IO.println "scalar-caller-graph accepted"; return 0
  catch e => IO.eprintln s!"scalar-caller-graph rejected: {e}"; return 1
