import Jihoo.NativeUnifiedProgram
import Jihoo.NativeEnvironmentScope

/-! Same-judgment data checks and resource admission, using raw declarations
that are independently admitted by the existing family checker. -/
namespace Jihoo.NativeKernel.Environment.DataExamples
open UnifiedProgram

private def nat : Term := .node (.ind 0 0) []
private def z : Term := .node (.con 0 0 0) []
private def s (n : Term) : Term := .node (.con 0 1 1) [n]
private def natDeclaration : FamilyDeclaration :=
  ⟨true, 0, 0, [nat, .pi false nat nat], 0⟩
private def natEntry : CheckedFamily :=
  ⟨natDeclaration, [⟨[],[]⟩,⟨[⟨false,nat,some []⟩],[]⟩], true⟩
private def natEnv : Environment := ⟨#[],#[natEntry]⟩
private def motive : Term := .lam false nat .u64
private def count : Term := .node (.elim 0 2)
  [motive, .natural 0, .lam true nat (.lam false .u64 (.uadd (.var 0) (.natural 1))), s z]
private def discard : Term := .node (.caseOf 0 2)
  [motive, .natural 0, .lam false nat (.node (.drop 0) [.var 0,.natural 1]), s z]

 theorem raw_recursive_family_admitted :
    Families.checkFamily 24 empty natDeclaration = some natEntry := by cbv
 theorem recursive_elimination_checked : Checker.check 32 natEnv [] false count .u64 = true := by cbv
 theorem recursive_elimination_typed : HasType natEnv [] false count .u64 :=
    Checker.check_sound recursive_elimination_checked
 theorem recursive_elimination_resource_safe : EnvironmentQuantity.check 32 natEnv count = true := by cbv
 theorem case_consumes_recursive_field_once : Checker.check 32 natEnv [] false discard .u64 = true := by cbv
 theorem case_quantity_checked : EnvironmentQuantity.check 32 natEnv discard = true := by cbv
 theorem case_scoped : discard.Scoped 0 := Checker.check_scoped case_consumes_recursive_field_once
 theorem drop_recursive_family :
    Checker.infer 16 natEnv [] false (.node (.drop 0) [s z,.natural 7]) = some .u64 := by cbv
 theorem ref_recursive_family : Checker.infer 16 natEnv [] false (.ref nat) = some (.univ 0) := by cbv
 theorem ghost_borrow_family : Checker.check 16 natEnv [] true (.borrow (s z)) (.ref nat) = true := by cbv
 theorem ghost_deref_family : Checker.check 16 natEnv [] true (.deref (.borrow (s z))) nat = true := by cbv
 theorem code_borrow_without_loan_rejected : Checker.infer 16 natEnv [] false (.borrow (s z)) = none := by cbv
 theorem code_deref_rejected : Checker.infer 16 natEnv [] false (.deref (.borrow (s z))) = none := by cbv

private def bitDeclaration : FamilyDeclaration := ⟨true,0,0,[nat,nat],0⟩
private def bitEntry : CheckedFamily := ⟨bitDeclaration,[⟨[],[]⟩,⟨[],[]⟩],false⟩
private def bitEnv : Environment := ⟨#[],#[bitEntry]⟩
 theorem flat_data_elimination :
    Checker.check 24 bitEnv [] false (.node (.elim 0 2) [motive,.natural 0,.natural 1,z]) .u64 = true := by cbv
 theorem flat_case_rejected :
    Checker.infer 24 bitEnv [] false (.node (.caseOf 0 2) [motive,.natural 0,.natural 1,z]) = none := by cbv
 theorem flat_drop_rejected :
    Checker.infer 16 bitEnv [] false (.node (.drop 0) [z,.natural 7]) = none := by cbv
 theorem wrong_drop_family_rejected :
    Checker.infer 16 natEnv [] false (.node (.drop 1) [s z,.natural 7]) = none := by cbv
 theorem missing_branch_rejected :
    Checker.infer 24 natEnv [] false (.node (.elim 0 1) [motive,.natural 0,s z]) = none := by cbv
 theorem wrong_recursive_erasure_rejected :
    Checker.infer 24 natEnv [] false (.node (.elim 0 2)
      [motive,.natural 0,.lam false nat (.lam false .u64 (.var 0)),s z]) = none := by cbv

private def leak : Term := .node (.caseOf 0 2)
  [motive,.natural 0,.lam false nat (.natural 1),s z]
private def duplicate : Term := .node (.caseOf 0 2)
  [motive,.natural 0,.lam false nat (.node (.drop 0) [.var 0,.node (.drop 0) [.var 0,.natural 1]]),s z]
 theorem typed_case_leak_rejected_by_quantities :
    Checker.check 24 natEnv [] false leak .u64 = true ∧ EnvironmentQuantity.check 24 natEnv leak = false := by cbv
 theorem typed_case_duplicate_rejected_by_quantities :
    Checker.check 24 natEnv [] false duplicate .u64 = true ∧ EnvironmentQuantity.check 24 natEnv duplicate = false := by cbv
 theorem branch_imbalance_rejected :
    EnvironmentQuantity.check 32 natEnv (.lam false (.buffer (.natural 2))
      (.node (.caseOf 0 2) [motive,.free (.var 0) (.natural 0),
        .lam false nat (.node (.drop 0) [.var 0,.natural 1]),s z])) = false := by cbv
 theorem recursive_outer_owner_capture_rejected :
    EnvironmentQuantity.check 32 natEnv (.lam false (.buffer (.natural 2))
      (.node (.elim 0 2) [motive,.free (.var 0) (.natural 0),
        .lam true nat (.lam false .u64 (.free (.var 2) (.var 0))),s z])) = false := by cbv

private def boxed : Term := .node (.ind 0 0) []
private def dependentDecl : FamilyDeclaration :=
  ⟨true,0,0,[.pi false .u64 (.pi false (.buffer (.var 0)) boxed)],0⟩
private def dependentEntry : CheckedFamily :=
  ⟨dependentDecl,[⟨[⟨false,.u64,none⟩,⟨false,.buffer (.var 0),none⟩],[]⟩],true⟩
private def dependentEnv : Environment := ⟨#[],#[dependentEntry]⟩
private def dependentCase : Term := .node (.caseOf 0 1)
  [.lam false boxed .u64,.lam false .u64 (.lam false (.buffer (.var 0)) (.free (.var 0) (.var 1))),
    .node (.con 0 0 2) [.natural 2,.alloc (.natural 2) (.integer 0)]]
 theorem dependent_field_signature_admitted : Families.checkFamily 24 empty dependentDecl = some dependentEntry := by cbv
 theorem dependent_fields_case_checked : Checker.check 32 dependentEnv [] false dependentCase .u64 = true := by cbv
 theorem dependent_fields_quantity_checked : EnvironmentQuantity.check 32 dependentEnv dependentCase = true := by cbv

private def paramNat (index : Term) : Term := .node (.ind 0 1) [index]
private def paramDecl : FamilyDeclaration :=
  ⟨true,1,1,[.pi true .u64 (paramNat (.var 0)),
    .pi true .u64 (.pi false (paramNat (.var 0)) (paramNat (.var 1)))],0⟩
private def paramEntry : CheckedFamily :=
  ⟨paramDecl,[⟨[⟨true,.u64,none⟩],[.var 0]⟩,
    ⟨[⟨true,.u64,none⟩,⟨false,paramNat (.var 0),some [.var 0]⟩],[.var 1]⟩],true⟩
private def paramEnv : Environment := ⟨#[],#[paramEntry]⟩
private def paramCase : Term := .node (.elim 0 2)
  [.lam false (paramNat (.var 0)) .u64,.natural 0,
    .lam true (paramNat (.var 0)) (.lam false .u64 (.var 0)),
    .node (.con 0 0 1) [.var 0]]
 theorem parameter_signature_admitted : Families.checkFamily 24 empty paramDecl = some paramEntry := by cbv
 theorem outer_parameter_substitution_checked :
    Checker.check 32 paramEnv [⟨.u64,false⟩] false paramCase .u64 = true := by cbv
 theorem parameter_case_telescope_exact :
    dataCaseType 0 1 1 1 ⟨[⟨true,.u64,none⟩,⟨false,paramNat (.var 0),some [.var 0]⟩],[.var 1]⟩ [.var 0]
      (.lam false (paramNat (.var 0)) .u64) true false = some
      (.pi true (paramNat (.var 0)) (.pi false
        (.app ((Term.lam false (paramNat (.var 0)) .u64).rename (fun x => x + 1)) (.var 0))
        (.app ((Term.lam false (paramNat (.var 0)) .u64).rename (fun x => x + 2))
          (.node (.con 0 1 2) [.var 2,.var 1])))) := by cbv

private def vec (n : Term) : Term := .node (.ind 0 1) [n]
private def indexedDecl : FamilyDeclaration :=
  ⟨true,0,1,[vec (.natural 0),.pi true .u64
    (.pi false (vec (.var 0)) (vec (.uadd (.var 1) (.natural 1))))],0⟩
private def indexedEntry : CheckedFamily :=
  ⟨indexedDecl,[⟨[],[.natural 0]⟩,
    ⟨[⟨true,.u64,none⟩,⟨false,vec (.var 0),some [.var 0]⟩],[.uadd (.var 1) (.natural 1)]⟩],true⟩
private def indexedEnv : Environment := ⟨#[],#[indexedEntry]⟩
private def indexedValue : Term := .node (.con 0 1 2)
  [.natural 0,.node (.con 0 0 0) []]
private def indexedCount : Term := .node (.elim 0 2)
  [.lam false .u64 (.lam false (vec (.var 0)) .u64),.natural 0,
    .lam true .u64 (.lam true (vec (.var 0)) (.lam false .u64 (.uadd (.var 0) (.natural 1)))),indexedValue]
 theorem indexed_signature_admitted : Families.checkFamily 32 empty indexedDecl = some indexedEntry := by cbv
 theorem indexed_runtime_motive_checked : Checker.check 40 indexedEnv [] false indexedCount .u64 = true := by cbv
 theorem indexed_runtime_quantity_checked : EnvironmentQuantity.check 40 indexedEnv indexedCount = true := by cbv
 theorem genuinely_index_dependent_proposition :
    Checker.check 40 indexedEnv [] false (.node (.elim 0 2)
      [.lam false .u64 (.lam false (vec (.var 0)) (.eq (.var 1) (.var 1))),.refl (.natural 0),
        .lam true .u64 (.lam true (vec (.var 0))
          (.lam true (.eq (.var 1) (.var 1)) (.refl (.uadd (.var 2) (.natural 1))))),indexedValue])
      (.eq (.natural 1) (.natural 1)) = true := by cbv

end Jihoo.NativeKernel.Environment.DataExamples
