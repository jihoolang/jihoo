import Jihoo.NativeEnvironmentAdmission

namespace Jihoo.NativeKernel.Environment.Examples

def declaration : FamilyDeclaration := ⟨false, 0, 0, [.node (.ind 0 0) []], 0⟩
def entry : CheckedFamily := ⟨declaration, [⟨[], []⟩], false⟩
def env : Environment := ⟨#[⟨.i64, .integer 7⟩], #[entry]⟩
def evidence : Term := .node (.con 0 0 0) []
def proposition : Term := .eq (.natural 0) (.natural 0)
def induction : Term := .node (.elim 0 1) [proposition, .refl (.natural 0), evidence]

theorem global_under_strict :
    Checker.check 32 env [] false (.strict (.node (.global 0) []) (.integer 2)) .i64 = true := by cbv

theorem constructor_checked : Checker.check 32 env [] true evidence (.node (.ind 0 0) []) = true := by cbv

theorem proposition_induction : Checker.check 32 env [] true induction proposition = true := by cbv

theorem family_under_erased_lambda :
    Checker.check 32 env [] false
      (.app (.lam true (.node (.ind 0 0) []) (.integer 9)) evidence) .i64 = true := by cbv

theorem rejects_unknown_global : Checker.infer 32 env [] true (.node (.global 1) []) = none := by cbv

theorem rejects_bad_ind_count : Checker.infer 32 env [] true (.node (.ind 0 1) []) = none := by cbv

theorem rejects_missing_case :
    Checker.infer 32 env [] true (.node (.elim 0 0) [proposition, evidence]) = none := by cbv

theorem rejects_bad_constructor_fields :
    Checker.infer 32 env [] true (.node (.con 0 0 1) [.natural 0]) = none := by cbv

theorem admitted_source_constructor :
    (inferProgram 32 [] [declaration] true evidence).map Prod.snd = some (.node (.ind 0 0) []) := by cbv

theorem admitted_source_induction :
    (inferProgram 32 [] [declaration] true induction).map Prod.snd = some proposition := by cbv

def dataDeclaration : FamilyDeclaration := ⟨true, 0, 0, [.node (.ind 0 0) []], 0⟩
def flatData : Environment := ⟨#[], #[⟨dataDeclaration, [⟨[], []⟩], false⟩]⟩
def boxedData : Environment := ⟨#[], #[⟨dataDeclaration, [⟨[], []⟩], true⟩]⟩

theorem erased_data_binder :
    Checker.check 32 flatData [] false (.lam true (.node (.ind 0 0) []) (.integer 8))
      (.pi true (.node (.ind 0 0) []) .i64) = true := by cbv

theorem erased_data_runtime_read_rejected :
    Checker.infer 32 flatData [] false (.lam true (.node (.ind 0 0) []) (.var 0)) = none := by cbv

theorem flat_family_type_argument :
    Checker.check 32 flatData [] false
      (.app (.lam false (.univ 0) (.natural 2)) (.node (.ind 0 0) [])) .u64 = true := by cbv

theorem boxed_family_type_argument_rejected :
    Checker.infer 32 boxedData [] false
      (.app (.lam false (.univ 0) (.natural 2)) (.node (.ind 0 0) [])) = none := by cbv

def indexedDeclaration : FamilyDeclaration := ⟨true, 1, 1,
  [.pi true .u64 (.pi true (.eq (.var 0) (.var 0)) (.node (.ind 0 1) [.var 1]))], 0⟩

theorem dependent_constructor_instantiation :
    (inferProgram 40 [] [indexedDeclaration] false
      (.node (.con 0 0 2) [.natural 7, .refl (.natural 7)])).map Prod.snd =
      some (.node (.ind 0 1) [.natural 7]) := by cbv

end Jihoo.NativeKernel.Environment.Examples
