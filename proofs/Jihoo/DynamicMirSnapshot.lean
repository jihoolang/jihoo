import Lean
import Jihoo.DynamicMir
import Jihoo.DependentBufferGraph

/-! Serialize every retained MIR row of the kernel-tested fixture. The native
exporter independently emits this schema; check.sh compares the full snapshots,
not merely local/block counts or the final execution result. -/
open Lean Jihoo.BoundedMir

namespace Jihoo.DynamicMirSnapshot

private def nat (n : Nat) : Json := toJson n
private def bit (b : Bool) : Json := nat (if b then 1 else 0)
private def row (xs : List Json) : Json := .arr xs.toArray

private def ty : Ty → Json
  | .i64 => .str "i64" | .u64 => .str "u64" | .bool => .str "bool"
  | .ptr => .str "ptr" | .unit => .str "unit"

private def place (p : Place) : Json := row [nat p.slot, bit p.deref]

private def operand : Operand → Json
  | .copy p => row [.str "copy", place p]
  | .constant (.i64 n) => row [.str "int", .str "i64", nat n]
  | .constant (.u64 n) => row [.str "int", .str "u64", nat n]
  | .constant (.boolean b) => row [.str "bool", bit b]
  | .constant .unit => row [.str "unit"]

private def bin : Bin → String
  | .add => "add" | .mul => "mul" | .lt => "lt" | .ne => "ne"

private def rvalue : Rvalue → Json
  | .use a => row [.str "use", operand a]
  | .bin op a b => row [.str (bin op), operand a, operand b]
  | .ptrCast a => row [.str "cast", operand a, .str "u64"]
  | .offset a b => row [.str "offset", operand a, operand b]

private def statement (s : Stmt) : Json := row [place s.place, rvalue s.value]

private def term : Jihoo.BoundedMir.Term → Json
  | .goto b => row [.str "goto", nat b]
  | .switch value cases other => row [.str "switch", operand value,
      row (cases.map fun (v, b) => row [nat v, nat b]), nat other]
  | .assert value next => row [.str "assert", operand value, nat next]
  | .malloc bytes dest next => row [.str "malloc", operand bytes, place dest, nat next]
  | .free pointer dest next => row [.str "free", operand pointer, place dest, nat next]
  | .ret => row [.str "return"]

private def block (b : Block) : Json := row [.arr (b.statements.map statement), term b.term]

def code (c : Code) (entry : Entry) : Json := row [nat 2, .arr (entry.argumentSlots.map nat), .arr (c.locals.map ty), .arr (c.blocks.map block)]

def mir : Json := code Jihoo.DynamicMir.code Jihoo.DynamicMir.entry

end Jihoo.DynamicMirSnapshot

namespace Jihoo.DynamicMirSnapshot.Source
open Lean Jihoo.ScopedLend

private def row (tag : String) (fields : List Nat) : Json :=
  .arr ((Json.str tag :: fields.map toJson).toArray)

private def node : Graph.Node → Json
  | .opaque => row "opaque" []
  | .var k => row "var" [k]
  | .natural n => row "natural" [n]
  | .integer n => row "integer" [n]
  | .i64 => row "i64" []
  | .u64 => row "u64" []
  | .buffer n => row "buffer" [n]
  | .ref t => row "ref" [t]
  | .pi e t b => row "pi" [if e then 1 else 0, t, b]
  | .lam e t b => row "lam" [if e then 1 else 0, t, b]
  | .alloc n v => row "alloc" [n, v]
  | .app f a => row "app" [f, a]
  | .index a i p => row "index" [a, i, p]
  | .decide a b => row "decide" [a, b]
  | .strict a b => row "strict" [a, b]
  | .borrow x => row "borrow" [x]
  | .lend x f g => row "lend" [x, f, g]
  | .free x rest => row "free" [x, rest]
  | .store x i v p => row "store" [x, i, v, p]
  | .ifLt a b yes no => row "ifLt" [a, b, yes, no]

def serialize (graph : Array Graph.Node) (root typeRoot : Nat) : Json := .arr #[toJson (1 : Nat),
  toJson root, toJson typeRoot, .arr (graph.map node)]

def snapshot : Json := serialize Jihoo.DependentBufferGraph.graph
  Jihoo.DependentBufferGraph.root Jihoo.DependentBufferGraph.typeRoot
end Jihoo.DynamicMirSnapshot.Source

namespace Jihoo.DynamicMirSnapshot

/-- Fixed complete source/MIR association. Comparing JSON is a trusted adapter,
not a theorem of arbitrary native lowering or parsing correctness. -/
def expected : Json := .arr #[toJson (1 : Nat), Source.snapshot, mir]

end Jihoo.DynamicMirSnapshot
