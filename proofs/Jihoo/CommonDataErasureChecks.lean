import Jihoo.CommonDataErasure
import Jihoo.CommonDataSourceExecutionChecks

namespace Jihoo.CommonDataErasureChecks
open CommonDataErasure RecursiveLexicalFields CommonDataSourceRules
open CommonDataSourceRulesChecks CommonDataSourceExecutionChecks
open CommonData RecursiveFieldOwnership RecursiveFieldRuntime HeapLeases LinearHeapPrograms
open CommonDataExamples (start parent)

-- Reuse the existing source fixture, changing only the outer scrutinee to var 1.
-- The initial source environment has a real ghost hole before and after the tree.
def nodes := CommonDataSourceRulesChecks.nodes.set! 33 (.caseOf 0 9 [8,32] 6)
def target : Term := .caseTree 0 (.literal 9)
  (.caseTree 1 (.drop 0 (.literal 9)) (.drop 1 (.drop 0 (.drop 2 (.literal 9)))))

theorem lowered : Lower nodes [false,true,false] 33 target :=
  .caseTree rfl rfl rfl rfl rfl (.literal rfl)
    (.caseTree rfl rfl rfl rfl rfl (.drop rfl rfl rfl (.literal rfl))
      (.drop rfl rfl rfl (.drop rfl rfl rfl (.drop rfl rfl rfl (.literal rfl)))))

theorem typed : CommonDataSourceRules.Typing nodes [.ghost,.data 0,.ghost] 1 [] 33 .scalar :=
  .caseTree rfl rfl rfl rfl rfl (.literal rfl (by decide))
    (.caseTree rfl rfl rfl rfl rfl
      (.drop rfl rfl rfl (.literal rfl (by decide)))
      (.drop rfl rfl rfl (.drop rfl rfl rfl (.drop rfl rfl rfl (.literal rfl (by decide))))))

theorem compacted : Env [false,true,false]
    [.ghost,.data (some 0),.ghost] [.data (some 0)] := .erase (.keep (.erase .nil))

/-- No execution assumption; this uses the original source typing and resources. -/
theorem target_exists : ∃ v es t, CommonDataErasure.Eval [.data (some 0)] target start v es t ∧
    Steps start.buffers.heap es t.buffers.heap ∧ Valid t.buffers.heap ∧
    AccountedPost .scalar t v [4,5,6] parent.owners es :=
  CommonDataErasure.total_accounted typed lowered compacted (trees := [parent]) (owners := []) rfl
    (.cons rfl (.cons ⟨parent,rfl,rfl⟩ (.cons rfl .nil))) empty_layout
    CommonDataExamples.valid_start CommonDataDropExamples.input_owned CommonDataDropExamples.input_fields

theorem source_run : CommonDataSourceExecution.Eval nodes [.ghost,.data (some 0),.ghost] 33
    start (.scalar 9) [.free 2,.free 3,.free 1,.free 0] nestedFinal :=
  .nodeCase rfl rfl rfl rfl rfl
    (.nodeCase rfl rfl rfl rfl rfl
      (.drop (before := []) rfl rfl rfl .empty
        (.drop (before := []) rfl rfl rfl .empty
          (.drop (before := [.free 2,.free 3]) rfl rfl rfl
            (.node (left := [.free 3]) (right := []) rfl
              (.node (left := []) (right := []) rfl .empty .empty) .empty)
            (.literal rfl)))))

theorem target_run : CommonDataErasure.Eval [.data (some 0)] target start (.scalar 9)
    [.free 2,.free 3,.free 1,.free 0] nestedFinal := lowered.preserves compacted source_run

-- The outer ghost hole moves from source index 0 to 2 on Case entry;
-- the surviving outer tree moves from source index 1 to 3, target 0 to 2.
example : position [false,true,false] 1 = some 0 ∧
    position [true,true,false,true,false] 3 = some 2 ∧
    position [true,true,false,true,false] 2 = none := by decide
example : ¬ Env [false] [.data none] [] := by intro h; cases h

#print axioms CommonDataErasure.Env.lookup
#print axioms CommonDataErasure.position_injective
#print axioms CommonDataErasure.Env.enter
#print axioms CommonDataErasure.Lower.preserves
#print axioms CommonDataErasure.total_accounted
#print axioms target_exists
#print axioms target_run
end Jihoo.CommonDataErasureChecks
