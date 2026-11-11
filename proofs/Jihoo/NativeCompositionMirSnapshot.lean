import Jihoo.DynamicMirSnapshot
import Jihoo.NativeCompositionMir
import Jihoo.SizedCompositionGraph

/-! Complete retained native source/MIR association, including ordered argument
slots and every local, instruction and control-flow edge. Native export fidelity
is tested externally, not proved as generic compiler correctness. -/
namespace Jihoo.NativeCompositionMirSnapshot
open Lean

def mir : Json := DynamicMirSnapshot.code NativeCompositionMir.code NativeCompositionMir.entry

def source : Json := DynamicMirSnapshot.Source.serialize SizedCompositionGraph.graph
  SizedCompositionGraph.root SizedCompositionGraph.typeRoot

def expected : Json := .arr #[toJson (1 : Nat), source, mir]

end Jihoo.NativeCompositionMirSnapshot
