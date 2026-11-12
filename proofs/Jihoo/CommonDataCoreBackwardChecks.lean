import Jihoo.CommonDataCoreBackward
import Jihoo.CommonDataCoreDeterminism
import Jihoo.CommonDataCoreCompilerChecks
import Jihoo.CommonDataExamples

namespace Jihoo.CommonDataCoreBackwardChecks
open CommonDataCoreErasure RecursiveLexicalFields CommonDataCoreCompilerChecks
open CommonDataExamples (start)

/-- Case scrutinee moves from slot 1 to 0 after erasing an interleaved ghost. -/
def ghostCase : CommonDataSource.Graph := caseGraph.set! 4 (.core (.var 1))

-- Use a scalar branch to isolate Case entry from field reconstruction indices.
def scalarCase : CommonDataSource.Graph := ghostCase.set! 6 (.core (.integer 9))

theorem ghost_case_compiles : compileTarget scalarCase 2 [false,true] [false,false] 9 =
    some (.caseTree 0 (.literal 7) (.literal 9)) := by decide +kernel

theorem ghost_bridge : Bridge [false,true] [false,false]
    [.ghost,.data ref] [.data ref] :=
  ⟨.erase (.keep .nil), .consGhost (.consGhost .nil)⟩

/-- A target node run is constructed directly, without source execution. -/
theorem node_target : Eval [.data (some 0)] (.caseTree 0 (.literal 7) (.literal 9))
    start (.scalar 9) [.free 0] (CommonData.finish start 0) :=
  .nodeCase rfl .literal

theorem node_source : CommonDataSourceExecution.Eval scalarCase [.ghost,.data (some 0)] 9
    start (.scalar 9) [.free 0] (CommonData.finish start 0) :=
  (compileTarget_adequate ghost_case_compiles ghost_bridge).mp node_target

theorem nil_source : CommonDataSourceExecution.Eval scalarCase [.ghost,.data none] 9
    start (.scalar 7) [] start :=
  (compileTarget_adequate ghost_case_compiles ghost_bridge).mp (.emptyCase rfl .literal)

/-- Core results retain the exact state and full projected trace on reflection. -/
theorem dynamic_backward
    (success : compileTarget CommonDataBufferProducerChecks.delayedNodes 64
      [true,true,true,true,true,true] [false,true,true,true,true,true] 33 = some target)
    (bridge : Bridge [true,true,true,true,true,true] [false,true,true,true,true,true] source compacted)
    (run : Eval compacted target s v es t) :
    CommonDataSourceExecution.Eval CommonDataBufferProducerChecks.delayedNodes source 33 s v es t :=
  (compileTarget_adequate success bridge).mp run

/-- Scalar island reflection uses the Core mask, not the common slot number. -/
theorem scalar_island_source : CommonDataSourceExecution.Eval twoMasks
    [.data none,.scalar 5] 4 s (.scalar 7) [] s := by
  apply (compileTarget_adequate different_masks
    (show Bridge [true,true] [false,true] [.data none,.scalar 5] [.data none,.scalar 5] from
      ⟨.keep (.keep .nil), .consGhost (.consKeep (.scalar 5) .nil)⟩)).mp
  exact .scalarLet (.var rfl) .literal

def ownerGraph : CommonDataSource.Graph := #[
  .core (.var 0), .core (.buffer 2), .core (.integer 7),
  .core (.lam false 1 2), .core (.app 3 0)]

theorem owner_compiles : compileTarget ownerGraph 2 [true] [true] 4 =
    some (.ownerLet (.var 0) (.literal 7)) := by decide +kernel

theorem owner_island_source : CommonDataSourceExecution.Eval ownerGraph
    [.buffer x] 4 s (.scalar 7) [] s := by
  apply (compileTarget_adequate owner_compiles
    (show Bridge [true] [true] [.buffer x] [.buffer x] from
      ⟨.keep .nil, .consKeep (.owner x) .nil⟩)).mp
  exact .ownerLet (.var rfl) .literal

end Jihoo.CommonDataCoreBackwardChecks
