import Jihoo.CommonDataSourceRules
import Jihoo.CommonDataAccountingChecks

namespace Jihoo.CommonDataSourceRulesChecks
open CommonDataSource CommonDataSourceRules RecursiveLexicalFields

/-- Hand-written source syntax exercises general rules, not a new compiler export. -/
def nodes : CommonDataSource.Graph := #[
  .ind 0 [], .core .i64, .core (.pi false 0 0), .core (.pi false 0 2),
  .core (.pi false 0 1), .core (.var 0), .core (.var 1), .core (.var 2),
  .core (.integer 9), .core (.lam false 0 1), .core (.lam false 0 0), .con 0 0 [],
  .drop 0 5 8, .drop 0 6 12, .core (.lam false 0 13), .core (.lam false 0 14),
  .caseOf 0 9 [8,15] 5, .core (.lam false 0 16),
  .drop 0 5 11, .core (.lam false 0 18), .core (.app 19 11),
  .con 0 1 [6,5], .core (.lam false 0 21), .core (.lam false 0 22),
  .caseOf 0 10 [20,23] 5,
  .drop 0 7 8, .drop 0 5 25, .drop 0 6 26, .core (.lam false 0 27),
  .core (.lam false 0 28), .caseOf 0 9 [12,29] 6,
  .core (.lam false 0 30), .core (.lam false 0 31), .caseOf 0 9 [8,32] 5,
  .caseOf 0 10 [8,23] 5, .caseOf 0 9 [11,15] 5,
  .core (.lam false 0 5), .core (.lam true 0 1), .core (.lam false 1 1),
  .core (.lam true 0 13), .core (.lam false 1 14),
  .drop 0 7 8, .caseOf 0 9 [8,23] 5,
  .con 0 1 [5,7], .core (.lam false 0 43), .core (.app 44 5)]

def source : Source := ⟨17,4,⟨true,0,0,0,[0,3]⟩,nodes⟩

theorem source_valid : valid source = true ∧ familyValid source = true := by decide

theorem scalar_case : Typing nodes [.data 0] 1 [] 16 .scalar :=
  .caseTree rfl rfl rfl rfl rfl (.literal rfl (by decide))
    (.drop rfl rfl rfl (.drop rfl rfl rfl (.literal rfl (by decide))))

theorem checked_entry : CheckedEntry source .scalar :=
  ⟨source_valid.1,source_valid.2,16,0,1,0,rfl,rfl,rfl,rfl,rfl,scalar_case⟩

/-- The nil arm computes an empty tree through application and Drop. -/
theorem computed_nil : Typing nodes [.data 0] 1 [] 24 .data :=
  .caseTree rfl rfl rfl rfl rfl
    (.dataLet rfl rfl rfl (.empty rfl) (.drop rfl rfl rfl (.empty rfl)))
    (.construct rfl rfl rfl rfl rfl)

/-- Nested Case keeps the outer right child at lexical index 2; all three
inner-branch capabilities are consumed before either parent shell is freed. -/
theorem nested_case : Typing nodes [.data 0] 1 [] 33 .scalar :=
  .caseTree rfl rfl rfl rfl rfl (.literal rfl (by decide))
    (.caseTree rfl rfl rfl rfl rfl
      (.drop rfl rfl rfl (.literal rfl (by decide)))
      (.drop rfl rfl rfl (.drop rfl rfl rfl (.drop rfl rfl rfl (.literal rfl (by decide))))))

theorem motive_rejections : motiveKind nodes 36 = none ∧ motiveKind nodes 37 = none ∧
    motiveKind nodes 38 = none ∧ branchBody nodes 39 = none ∧ branchBody nodes 40 = none := by decide

theorem wrong_result_rejected : ¬ Typing nodes [.data 0] 1 [] 16 .data := by
  intro typed
  have h := typed.case_motive (show CommonDataSource.nodeAt nodes 16 = .caseOf 0 9 [8,15] 5 from rfl)
  contradiction

theorem nil_kind_mismatch : ¬ Typing nodes [.data 0] 1 [] 34 .data ∧
    ¬ Typing nodes [.data 0] 1 [] 35 .scalar := by
  constructor
  · intro typed
    have shape : CommonDataSource.nodeAt nodes 34 = .caseOf 0 10 [8,23] 5 := rfl
    have nilShape : CommonDataSource.nodeAt nodes 8 = .core (.integer 9) := rfl
    cases typed <;> simp_all
    rename_i nilTyped _
    cases nilTyped <;> simp_all
  · intro typed
    have shape : CommonDataSource.nodeAt nodes 35 = .caseOf 0 9 [11,15] 5 := rfl
    have nilShape : CommonDataSource.nodeAt nodes 11 = .con 0 0 [] := rfl
    cases typed <;> simp_all
    rename_i nilTyped _
    cases nilTyped <;> simp_all

theorem node_kind_mismatch : ¬ Typing nodes [.data 0] 1 [] 42 .scalar := by
  intro typed
  have shape : CommonDataSource.nodeAt nodes 42 = .caseOf 0 9 [8,23] 5 := rfl
  have branch : branchBody nodes 23 = some 21 := rfl
  have nodeShape : CommonDataSource.nodeAt nodes 21 = .con 0 1 [6,5] := rfl
  cases typed <;> simp_all
  rename_i nodeTyped
  cases nodeTyped <;> simp_all

theorem parent_alias_rejected :
    ¬ Typing nodes (bindContext 0 [.data 0]) 2 [] 41 .scalar := by
  intro typed
  have shape : CommonDataSource.nodeAt nodes 41 = .drop 0 7 8 := rfl
  have owner : CommonDataSource.nodeAt nodes 7 = .core (.var 2) := rfl
  cases typed <;> simp_all [bindContext,retire,retireEntry]
  all_goals subst_vars; simp_all

theorem split_application : Typing nodes [.data 0,.data 1] 2 [] 45 .data :=
  .dataLetSplit (activeCount := 1) (retainedCount := 1) (usedSizes := []) (savedSizes := [])
    rfl rfl rfl rfl rfl (.dataVar rfl rfl) (.construct rfl rfl rfl rfl rfl)

theorem wrong_entry_annotation : ¬ CheckedEntry source .data := by
  rintro ⟨_,_,body,domain,result,annotation,ty,_,_,_,kind,_⟩
  have shape : CommonDataSource.nodeAt source.nodes source.typeRoot = .core (.pi false 0 1) := rfl
  rw [shape] at ty
  cases ty
  contradiction

open CommonDataExamples (start parent)
open CommonData (finish)

def scalarFinal := finish (finish (finish (finish start 1) 2) 3) 0

local macro "adapt_shape" : term => `(by rw [CommonDataSourceRules.adapted_at]; rfl)

theorem scalar_run : CommonData.Eval (graph nodes) [.data (some 0)] 16 start (.scalar 9)
    [.free 1,.free 2,.free 3,.free 0] scalarFinal :=
  .nodeCase adapt_shape adapt_shape rfl
    (.drop (before := [.free 1]) adapt_shape adapt_shape rfl
      (.node (left := []) (right := []) rfl .empty .empty)
      (.drop (before := [.free 2,.free 3]) adapt_shape adapt_shape rfl
        (.node (left := [.free 3]) (right := []) rfl
          (.node (left := []) (right := []) rfl .empty .empty) .empty)
        (.literal adapt_shape)))

theorem scalar_accounted : CommonData.AccountedPost .scalar scalarFinal (.scalar 9)
    [4,5,6] parent.owners [.free 1,.free 2,.free 3,.free 0] := by
  exact scalar_case.elaborate.every_run_accounted (trees := [parent]) (owners := []) rfl
    (.cons ⟨parent,rfl,rfl⟩ .nil) CommonData.empty_layout CommonDataExamples.valid_start
    CommonDataDropExamples.input_owned CommonDataDropExamples.input_fields scalar_run

end Jihoo.CommonDataSourceRulesChecks
