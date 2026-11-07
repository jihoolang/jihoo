import Jihoo.GraphCertificates
import Lean

/-! Unverified serialization adapter. The pure validation theorems start at
`Certificate`, not at bytes. This deliberately accepts a small canonical JSON
language: ASCII strings without escapes, integral numbers with at most 20
 digits, fixed fields, and at most 8 nested containers. -/
namespace Jihoo.GraphCertificates.JsonAdapter

open Lean

private def fields : List String :=
  ["schema", "operation", "amount", "cutoff", "depth", "input", "output",
    "replacement", "before", "after"]

/-- Operational parser preflight, not a theorem about Lean's JSON parser. It
also rejects duplicate top-level keys before the JSON object map can erase them. -/
def lexicalGuard (s : String) : Bool := Id.run do
  let mut inside := false
  let mut nesting : Nat := 0
  let mut digits : Nat := 0
  let mut token := ""
  let mut seen : List String := []
  for ch in s.toList do
    if inside then
      if ch == '"' then
        inside := false
        if nesting == 1 && fields.contains token then
          if seen.contains token then return false
          seen := token :: seen
      else
        if ch == '\\' || ch.toNat > 127 || token.length ≥ 64 then return false
        token := token.push ch
    else
      if ch == '"' then
        if digits > 0 then return false
        inside := true
        token := ""
      else if ch == '{' || ch == '[' then
        nesting := nesting + 1
        if nesting > 8 then return false
        digits := 0
      else if ch == '}' || ch == ']' then
        if nesting == 0 then return false
        nesting := nesting - 1
        digits := 0
      else if ch.isDigit then
        digits := digits + 1
        if digits > 20 then return false
      else
        if ch == '.' || ch == '+' || ((ch == 'e' || ch == 'E') && digits > 0) then
          return false
        digits := 0
  return !inside && nesting == 0

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def nat (j : Json) : Except String Nat := j.getNat?

private def node (j : Json) : Except String Node := do
  let xs := (← j.getArr?).toList
  match xs with
  | [.str "var", k] => return .var (← nat k)
  | [.str "natural", n] => return .natural (← nat n)
  | [.str "integer", n] => return .integer (← n.getInt?)
  | [.str "u64"] => return .u64
  | [.str "i64"] => return .i64
  | [.str "array", a] => return .array (← nat a)
  | [.str "lt", a, b] => return .lt (← nat a) (← nat b)
  | [.str "eq", a, b] => return .eq (← nat a) (← nat b)
  | [.str "pi", e, a, b] => return .pi (← e.getBool?) (← nat a) (← nat b)
  | [.str "lam", e, a, b] => return .lam (← e.getBool?) (← nat a) (← nat b)
  | [.str "app", a, b] => return .app (← nat a) (← nat b)
  | [.str "elements", items] =>
      let items ← items.getArr?
      require (items.size ≤ nodeLimit) "child vector exceeds limit"
      return .elements (← items.toList.mapM nat)
  | [.str "index", a, b, p] => return .index (← nat a) (← nat b) (← nat p)
  | [.str "refl", a] => return .refl (← nat a)
  | [.str "zeroLe", a] => return .zeroLe (← nat a)
  | [.str "decide", a, b] => return .decide (← nat a) (← nat b)
  | [.str "uadd", a, b] => return .uadd (← nat a) (← nat b)
  | [.str "usub", a, b, p] => return .usub (← nat a) (← nat b) (← nat p)
  | [.str "prop"] => return .prop
  | [.str "universe", level] =>
      let level ← nat level
      require (level < universeBound) "universe level exceeds transport bound"
      return .universe level
  | _ => throw "unsupported constructor, payload, or arity"

private def graph (j : Json) : Except String Graph := do
  let xs ← j.getArr?
  require (xs.size ≤ nodeLimit) "graph exceeds node limit"
  xs.mapM node

def parse (text : String) : Except String Certificate := do
  require (lexicalGuard text) "noncanonical or excessive JSON syntax"
  let j ← Json.parse text
  let obj ← j.getObj?
  let keys := obj.toList.map Prod.fst
  require (keys.length == fields.length && keys.all fields.contains) "unexpected or missing fields"
  let field := j.getObjVal?
  require ((← nat (← field "schema")) == 1) "unsupported schema"
  require ((← nat (← field "cutoff")) == 0) "only cutoff zero is supported"
  require ((← nat (← field "depth")) == depthLimit) "unsupported depth"
  let amount ← nat (← field "amount")
  let replacement ← nat (← field "replacement")
  let op ← (← field "operation").getStr?
  let operation ← match op with
    | "shift" => do
        require (replacement == 0) "shift replacement must be zero"
        require (amount < CoreBridge.signedBound.toNat) "shift amount exceeds signed i64"
        pure (.shift amount)
    | "substitute" => do
        require (amount == 0) "substitution amount must be zero"
        pure (.substitute replacement)
    | _ => throw "unsupported operation"
  return {
    before := ← graph (← field "before")
    after := ← graph (← field "after")
    input := ← nat (← field "input")
    output := ← nat (← field "output")
    operation := operation
  }

end Jihoo.GraphCertificates.JsonAdapter
