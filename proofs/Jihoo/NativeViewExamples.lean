import Jihoo.NativeUnifiedProgram
import Jihoo.NativeEnvironmentScope
import Jihoo.NativeViewMotiveCongruence

/-! Same-judgment view inference and checked-program admission. Raw family
signatures are independently recomputed; no live loan or iota law is assumed. -/
namespace Jihoo.NativeKernel.Environment.ViewExamples
open UnifiedProgram

private def nat : Term := .node (.ind 0 0) []
private def natDeclaration : FamilyDeclaration := ⟨true,0,0,[nat,.pi false nat nat],0⟩
private def natEntry : CheckedFamily :=
  ⟨natDeclaration,[⟨[],[]⟩,⟨[⟨false,nat,some []⟩],[]⟩],true⟩
private def env : Environment := ⟨#[],#[natEntry]⟩
private def z : Term := .node (.con 0 0 0) []
private def step : Term := .node (.con 0 1 1) [z]
private def viewTerm (recursion : Bool) (motive : Term) (cases : List Term) (scrutinee : Term) : Term :=
  .node (.view recursion 0 cases.length) (motive :: (cases ++ [scrutinee]))
private def viewFunction (recursion : Bool) (motive : Term) (cases : List Term) : Term :=
  .lam false (.ref nat) (viewTerm recursion motive cases (.var 0))
private def oneCases : List Term := [.natural 0,.lam false (.ref nat) (.natural 1)]
private def recursiveCases : List Term :=
  [.natural 0,.lam false (.ref nat) (.lam false .u64 (.uadd (.var 0) (.natural 1)))]
private def countFunction : Term := viewFunction false .u64 oneCases
private def recursiveFunction : Term := viewFunction true .u64 recursiveCases
private def dependentFunction : Term := viewFunction false (.lam false (.ref nat) .u64) oneCases

theorem original_family_admitted : Families.checkFamily 24 empty natDeclaration = some natEntry := by cbv

theorem one_level_view_checked : Checker.check 32 env [] false countFunction (.pi false (.ref nat) .u64) = true := by cbv
theorem one_level_view_typed : HasType env [] false countFunction (.pi false (.ref nat) .u64) :=
  Checker.check_sound one_level_view_checked

theorem one_level_view_resources : EnvironmentQuantity.check 32 env countFunction = true := by cbv

theorem recursive_view_checked : Checker.check 32 env [] false recursiveFunction (.pi false (.ref nat) .u64) = true := by cbv
theorem recursive_view_resources : EnvironmentQuantity.check 32 env recursiveFunction = true := by cbv

theorem dependent_borrow_motive_checked :
    Checker.check 32 env [] false dependentFunction (.pi false (.ref nat) .u64) = true := by cbv

theorem dependent_borrow_motive_resources : EnvironmentQuantity.check 32 env dependentFunction = true := by cbv

theorem closed_program_recomputes_view_metadata :
    (checkProgram 32 64 [⟨.pi false (.ref nat) .u64,countFunction⟩] [natDeclaration]).isSome = true := by cbv

theorem ghost_known_constructor_view_checked :
    Checker.check 32 env [] true (viewTerm false .u64 oneCases (.borrow step)) .u64 = true := by cbv

theorem code_borrow_without_loan_still_rejected :
    Checker.infer 32 env [] false (viewTerm false .u64 oneCases (.borrow step)) = none := by cbv

theorem owner_cannot_replace_reference :
    Checker.infer 32 env [] false (.lam false nat (viewTerm false .u64 oneCases (.var 0))) = none := by cbv

theorem field_owner_cannot_replace_borrow :
    Checker.infer 32 env [] false (viewFunction false .u64 [.natural 0,.lam false nat (.natural 1)]) = none := by cbv

theorem motive_domain_must_be_reference :
    Checker.infer 32 env [] false (viewFunction false (.lam false nat .u64) oneCases) = none := by cbv

theorem motive_cannot_return_a_universe :
    Checker.infer 32 env [] false (viewFunction false (.lam false (.ref nat) (.univ 0)) oneCases) = none := by cbv

theorem missing_view_branch_rejected :
    Checker.infer 32 env [] false (viewFunction false .u64 [.natural 0]) = none := by cbv

theorem recursive_hypothesis_is_not_erased :
    Checker.infer 32 env [] false (viewFunction true .u64
      [.natural 0,.lam false (.ref nat) (.lam true .u64 (.natural 1))]) = none := by cbv

theorem a_borrowed_field_cannot_be_dropped :
    Checker.infer 32 env [] false (viewFunction false .u64
      [.natural 0,.lam false (.ref nat) (.node (.drop 0) [.var 0,.natural 1])]) = none := by cbv

theorem a_borrowed_field_cannot_be_dereferenced_in_code :
    Checker.infer 32 env [] false (viewFunction false .u64
      [.natural 0,.lam false (.ref nat) (.node (.drop 0) [.deref (.var 0),.natural 1])]) = none := by cbv

private def ownedCases (leak : Bool) : List Term :=
  [.alloc (.natural 2) (.integer 0),.lam false (.ref nat) (.lam false (.buffer (.natural 2))
    (if leak then .alloc (.natural 2) (.integer 0) else .free (.var 0) (.alloc (.natural 2) (.integer 0))))]
private def ownedFunction (leak : Bool) : Term := viewFunction true (.buffer (.natural 2)) (ownedCases leak)

theorem recursive_owned_result_typed :
    Checker.check 32 env [] false (ownedFunction false) (.pi false (.ref nat) (.buffer (.natural 2))) = true := by cbv

theorem recursive_owned_hypothesis_consumed_once : EnvironmentQuantity.check 32 env (ownedFunction false) = true := by cbv

theorem typed_recursive_hypothesis_leak_rejected :
    Checker.check 32 env [] false (ownedFunction true) (.pi false (.ref nat) (.buffer (.natural 2))) = true ∧
      EnvironmentQuantity.check 32 env (ownedFunction true) = false := by cbv

private def fixedArray : Term := viewFunction false (.lam false (.ref nat) (.array (.natural 0)))
  [.elements 0 [],.lam false (.ref nat) (.elements 0 [])]

theorem dependent_fixed_array_checked :
    Checker.check 32 env [] false fixedArray (.pi false (.ref nat) (.array (.natural 0))) = true := by cbv

theorem dependent_fixed_array_resources : EnvironmentQuantity.check 32 env fixedArray = true := by cbv

theorem returned_borrow_depends_on_no_unknown_layout :
    Checker.infer 32 env [] false (viewFunction false (.lam false (.ref nat) (.ref nat))
      [.var 0,.lam false (.ref nat) (.var 0)]) = none := by cbv

private def indexed : Term := .node (.ind 0 1) [.natural 0]
private def indexedEnv : Environment :=
  ⟨#[],#[⟨⟨true,0,1,[],0⟩,[],true⟩]⟩

theorem extra_indices_rejected_before_branch_generation :
    Checker.infer 24 indexedEnv [] false (.lam false (.ref indexed)
      (.node (.view false 0 0) [.u64,.var 0])) = none := by cbv

private def paramNat (n : Term) : Term := .node (.ind 0 1) [n]
private def paramDeclaration : FamilyDeclaration :=
  ⟨true,1,1,[.pi true .u64 (paramNat (.var 0)),
    .pi true .u64 (.pi false (paramNat (.var 0)) (paramNat (.var 1)))],0⟩
private def paramEntry : CheckedFamily :=
  ⟨paramDeclaration,[⟨[⟨true,.u64,none⟩],[.var 0]⟩,
    ⟨[⟨true,.u64,none⟩,⟨false,paramNat (.var 0),some [.var 0]⟩],[.var 1]⟩],true⟩
private def paramEnv : Environment := ⟨#[],#[paramEntry]⟩
private def paramFunction : Term := .lam false (.ref (paramNat (.natural 3)))
  (.node (.view true 0 2) [.u64,.natural 0,
    .lam false (.ref (paramNat (.natural 3))) (.lam false .u64 (.uadd (.var 0) (.natural 1))),.var 0])

theorem parameterized_view_checked :
    Checker.check 40 paramEnv [] false paramFunction (.pi false (.ref (paramNat (.natural 3))) .u64) = true := by cbv

theorem parameterized_view_resources : EnvironmentQuantity.check 40 paramEnv paramFunction = true := by cbv

private def parameterContextFunction : Term := .lam true .u64 (.lam false (.ref (paramNat (.var 0)))
  (.node (.view true 0 2) [.u64,.natural 0,
    .lam false (.ref (paramNat (.var 1))) (.lam false .u64 (.uadd (.var 0) (.natural 1))),.var 0]))

theorem erased_outer_parameter_is_preserved :
    Checker.check 40 paramEnv [] false parameterContextFunction
      (.pi true .u64 (.pi false (.ref (paramNat (.var 0))) .u64)) = true := by cbv

theorem erased_parameter_has_no_runtime_read :
    EnvironmentQuantity.check 40 paramEnv parameterContextFunction = true := by cbv

private def boxDeclaration : FamilyDeclaration :=
  ⟨true,0,0,[.pi false .u64 (.pi false (.buffer (.var 0))
    (.pi true (.lt (.natural 0) (.var 1)) nat))],0⟩
private def boxEntry : CheckedFamily :=
  ⟨boxDeclaration,[⟨[⟨false,.u64,none⟩,⟨false,.buffer (.var 0),none⟩,
    ⟨true,.lt (.natural 0) (.var 1),none⟩],[]⟩],true⟩
private def boxEnv : Environment := ⟨#[],#[boxEntry]⟩
private def readFunction : Term := .lam false (.ref nat) (.node (.view false 0 1)
  [.i64,.lam false .u64 (.lam false (.ref (.buffer (.var 0)))
    (.lam true (.lt (.natural 0) (.var 1)) (.index (.var 1) (.natural 0) (.var 0)))),.var 0])

theorem dependent_buffer_and_evidence_family_admitted : Families.checkFamily 40 empty boxDeclaration = some boxEntry := by cbv

theorem borrowed_dependent_buffer_read_checked :
    Checker.check 40 boxEnv [] false readFunction (.pi false (.ref nat) .i64) = true := by cbv

theorem borrowed_read_preserves_erased_evidence : EnvironmentQuantity.check 40 boxEnv readFunction = true := by cbv

theorem borrowed_read_closed_program_admitted :
    (checkProgram 40 64 [⟨.pi false (.ref nat) .i64,readFunction⟩] [boxDeclaration]).isSome = true := by cbv

/-- Direct checker regression: the same installed delta comparator exposes
both the scrutinee's family alias and the motive's checked lambda. -/
private def global (index : Nat) : Term := .node (.global index) []
private def aliasDefinitions : List GlobalDeclaration :=
  [⟨.univ 0,nat⟩,⟨.pi false (.ref nat) (.univ 0),.lam false (.ref nat) .u64⟩]
private def aliasEnv : Environment := ⟨aliasDefinitions.toArray,#[natEntry]⟩
private def aliasFunction : Term := .lam false (.ref (global 0))
  (viewTerm false (global 1) oneCases (.var 0))

theorem direct_delta_view_prefix_authentically_checked :
    checkProgram 40 64 aliasDefinitions [natDeclaration] = some aliasEnv := by cbv

theorem direct_delta_family_and_motive_aliases_checked :
    Checker.check 40 aliasEnv [] false aliasFunction (.pi false (.ref (global 0)) .u64) = true := by cbv

theorem direct_delta_view_has_original_alias_type :
    HasType aliasEnv [] false aliasFunction (.pi false (.ref (global 0)) .u64) :=
  Checker.check_sound direct_delta_family_and_motive_aliases_checked

theorem view_aliases_come_from_checked_program :
    (checkProgram 40 64 (aliasDefinitions ++ [⟨.pi false (.ref (global 0)) .u64,aliasFunction⟩])
      [natDeclaration]).isSome = true := by cbv

theorem unresolved_delta_view_motive_rejected :
    Checker.infer 40 aliasEnv [] false (viewFunction false (global 9) oneCases) = none := by cbv

theorem malformed_delta_view_motive_rejected :
    Checker.infer 40 aliasEnv [] false
      (viewFunction false (.node (.global 1) [.natural 0]) oneCases) = none := by cbv

end Jihoo.NativeKernel.Environment.ViewExamples
