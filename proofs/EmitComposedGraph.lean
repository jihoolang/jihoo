import Lean
import Jihoo.ComposedCoreExamples

/-! Exact original-Core graph association for the closed composition fixture.
All constructor rows, IDs, roots and type roots are compared with the independent
native exporter. The exporter/source association remains a tested trust boundary. -/
namespace EmitComposedGraph
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

def snapshot : Json := .arr #[toJson (1 : Nat),
  toJson Jihoo.ComposedCoreExamples.root, toJson Jihoo.ComposedCoreExamples.typeRoot,
  .arr (Jihoo.ComposedCoreExamples.graph.map node)]
end EmitComposedGraph

def main : IO Unit := IO.println EmitComposedGraph.snapshot.compress
