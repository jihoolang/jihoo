import Jihoo.CommonCaseSourceConsumption
import Jihoo.CommonCaseChildTransferChecks
import Jihoo.CommonDataSourceExecutionChecks

namespace Jihoo.CommonCaseSourceConsumption.Checks
open CommonData RecursiveLexicalFields
open CommonDataReferenceChecks (source)

/-- A validated restricted source entry, not a production frontend export. -/
def entry : CommonDataSource.Source := ⟨11,12,⟨true,0,0,0,[5,14]⟩,graph 7⟩

theorem checked_entry : CommonDataSourceRules.CheckedEntry entry .scalar := by
  refine ⟨?_, ?_, 10,5,6,5,rfl,rfl,rfl,rfl,rfl,typed (by decide)⟩ <;> decide

/-- Same initial source state and environment as the closed target fixture.
Both Nil drops occur as source rules even though their source traces are empty.
The parent is freed only after the literal. No run is assumed. -/
theorem node_run : CommonDataSourceExecution.Eval (graph 7)
    CommonCaseChildTransfer.Checks.before.env 10 source (.scalar 7) [.free 7]
    (finish source 7) :=
  .nodeCase rfl rfl rfl rfl rfl
    (.drop (before := []) rfl rfl rfl .empty
      (.drop (before := []) rfl rfl rfl .empty (.literal rfl)))

theorem nil_run : CommonDataSourceExecution.Eval (graph n) [.data none]
    10 s (.scalar n) [] s :=
  .emptyCase rfl rfl rfl rfl rfl (.literal rfl)

/-- Nonempty recursive children: the two drops produce actual source frees,
followed by the enclosing parent free. -/
theorem recursive_run : CommonDataSourceExecution.Eval (graph 7) [.data (some 0)]
    10 CommonDataExamples.start (.scalar 7) [.free 1,.free 2,.free 3,.free 0]
    CommonDataSourceRulesChecks.scalarFinal :=
  .nodeCase rfl rfl rfl rfl rfl
    (.drop (before := [.free 1]) rfl rfl rfl
      (.node (left := []) (right := []) rfl .empty .empty)
      (.drop (before := [.free 2,.free 3]) rfl rfl rfl
        (.node (left := [.free 3]) (right := []) rfl
          (.node (left := []) (right := []) rfl .empty .empty) .empty)
        (.literal rfl)))

theorem recursive_accounted : AccountedPost .scalar
    CommonDataSourceRulesChecks.scalarFinal (.scalar 7) [4,5,6]
    CommonDataExamples.parent.owners [.free 1,.free 2,.free 3,.free 0] :=
  CommonDataSourceExecution.every_run_accounted (typed (ctx := []) (by decide))
    (trees := [CommonDataExamples.parent]) (owners := []) rfl
    (.cons ⟨_,rfl,rfl⟩ .nil) empty_layout CommonDataExamples.valid_start
    CommonDataDropExamples.input_owned CommonDataDropExamples.input_fields recursive_run

/-- Closed fixture connection: actual enclosing source evaluation, exact target
walk, identical final source state, and matching scalar. Target frees boxed Nils
1,2 and shell 3; source frees only shell 7. This is not trace equality or a
parametric lowering theorem. Target entry has one administrative ghost slot;
the source branch has none, so no lexical-context identity is claimed. -/
theorem closed_connection :
    CommonDataSourceRules.Typing (graph 7) CommonCaseChildTransfer.Checks.before.ctx
      1 [] 10 .scalar ∧
    CommonDataSourceExecution.Eval (graph 7) CommonCaseChildTransfer.Checks.before.env
      10 CommonCaseChildTransfer.Checks.before.source (.scalar 7) [.free 7]
      CommonCaseChildTransfer.Checks.done.source ∧
    CommonDataCaseRelocation.walk CommonCaseChildTransfer.Checks.program 24 3
      CommonCaseChildTransfer.Checks.before.target =
      some (CommonCaseChildTransfer.Checks.done.target, [.free 1,.free 2,.free 3]) ∧
    CommonDataTargetContext.Local CommonCaseChildTransfer.Checks.done.target.frame 1 (.i64 7) :=
  ⟨typed (by decide), node_run, CommonCaseChildTransfer.Checks.exact_walk, rfl⟩

/-- Bypassing the explicit drops is rejected even for empty logical children. -/
theorem unconsumed_literal_rejected : ¬ CommonDataSourceRules.Typing (graph 7)
    (bindContext 0 [.data 0]) 2 [] 2 .scalar := by
  intro h
  have impossible := (CommonCaseChildConsumption.literal_inventory_zero rfl h).1
  contradiction

/-- Every observed run of the closed source fixture agrees with the derived run. -/
theorem node_run_unique
    (run : CommonDataSourceExecution.Eval (graph 7)
      CommonCaseChildTransfer.Checks.before.env 10 source v es t) :
    v = .scalar 7 ∧ es = [.free 7] ∧ t = finish source 7 :=
  run.deterministic node_run

#print axioms frame_survives
#print axioms unconsumed_literal_rejected
#print axioms node_run_unique
#print axioms typed
#print axioms total
#print axioms tree_released
#print axioms checked_entry
#print axioms node_run
#print axioms nil_run
#print axioms recursive_run
#print axioms recursive_accounted
#print axioms closed_connection
end Jihoo.CommonCaseSourceConsumption.Checks
