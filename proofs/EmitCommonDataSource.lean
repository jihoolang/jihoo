import Lean
import Jihoo.CommonDataSourceExamples

namespace EmitCommonDataSource
open Lean Jihoo.CommonDataSource
private def row (tag : String) (fields : List Nat) : Json :=
  .arr ((Json.str tag :: fields.map toJson).toArray)

private def coreNode : Jihoo.ScopedLend.Graph.Node → Json
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

private def node : Node → Json
  | .core n => coreNode n
  | .ind family args => row "ind" ([family,args.length] ++ args)
  | .con family constructor args => row "con" ([family,constructor,args.length] ++ args)
  | .caseOf family motive branches value => row "case" ([family,motive,value,branches.length] ++ branches)
  | .drop family owner rest => row "drop" [family,owner,rest]

def snapshot : Json :=
  let s := Jihoo.CommonDataSourceExamples.source
  .arr #[toJson (1 : Nat),toJson s.root,toJson s.typeRoot,
    .arr #[toJson (if s.family.data then (1 : Nat) else 0),toJson s.family.params,
      toJson s.family.arity,toJson s.family.globals,toJson s.family.constructors],
    .arr (s.nodes.map node)]
end EmitCommonDataSource

def main : IO Unit := IO.println EmitCommonDataSource.snapshot.compress
