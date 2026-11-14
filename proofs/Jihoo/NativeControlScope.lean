import Jihoo.NativeCallControl

namespace Jihoo.NativeKernel.Environment.ContextQuantity
open Jihoo.Quantity NativeQuantity CallReplay
variable {control : Control}

/-- The finite control tree contains only source-local events. All four binder
modes occupy a slot; closures and repetitions introduce no hidden slots. -/
def ControlScoped : Nat → Control → Prop
  | _, .pure | _, .trap | _, .erased _ => True
  | depth, .use resource => resource < depth
  | depth, .seq first second | depth, .branch first second =>
      ControlScoped depth first ∧ ControlScoped depth second
  | depth, .repeat body | depth, .once body | depth, .closure body => ControlScoped depth body
  | depth, .scope _ body => ControlScoped (depth + 1) body

/-- A recomputed finite control certificate, never a caller-supplied flag. -/
def scopeCheck : Nat → Control → Bool
  | _, .pure | _, .trap | _, .erased _ => true
  | depth, .use resource => resource < depth
  | depth, .seq first second | depth, .branch first second => scopeCheck depth first && scopeCheck depth second
  | depth, .repeat body | depth, .once body | depth, .closure body => scopeCheck depth body
  | depth, .scope _ body => scopeCheck (depth + 1) body

theorem scopeCheck_correct : scopeCheck depth control = true ↔ ControlScoped depth control := by
  induction control generalizing depth <;> simp_all [scopeCheck, ControlScoped]

theorem ControlScoped.demand_above (scope : ControlScoped depth control)
    (locals : LocalScopes control) (outside : depth ≤ resource) : control.demand resource = some 0 := by
  induction control generalizing depth resource with
  | pure | trap | erased => rfl
  | use index =>
      have different : index ≠ resource := by simp only [ControlScoped] at scope; omega
      simp [Control.demand, different]
  | seq first second ihfirst ihsecond =>
      simp only [Control.demand, ihfirst scope.1 locals.1 outside, ihsecond scope.2 locals.2 outside]
      rfl
  | branch first second ihfirst ihsecond =>
      simp only [Control.demand, ihfirst scope.1 locals.1 outside, ihsecond scope.2 locals.2 outside]
      rfl
  | «repeat» body ih | closure body ih =>
      simp only [Control.demand, ih scope locals outside]
      rfl
  | once body ih => exact ih scope locals outside
  | scope mode body ih =>
      cases mode with
      | linear =>
          simp only [Control.demand, locals.1, ih scope locals.2 (by omega : depth + 1 ≤ resource + 1)]
          rfl
      | erased =>
          simp only [Control.demand, locals.1, ih scope locals.2 (by omega : depth + 1 ≤ resource + 1)]
          rfl
      | unrestricted | borrowed => exact ih scope locals (by omega)

theorem ControlScoped.bodyContract (scope : ControlScoped 0 (.scopes modes body))
    (locals : LocalScopes (.scopes modes body)) : BodyContract modes body :=
  ⟨locals,fun _ => scope.demand_above locals (Nat.zero_le _)⟩

theorem ControlScoped.sequence (controls : List Control)
    (scope : ∀ control ∈ controls, ControlScoped depth control) : ControlScoped depth (NativeQuantity.sequence controls) := by
  induction controls with
  | nil => trivial
  | cons first rest ih => exact ⟨scope _ (by simp), ih (fun _ member => scope _ (by simp [member]))⟩

theorem ControlScoped.scopes (scope : ControlScoped (depth + modes.length) body) :
    ControlScoped depth (.scopes modes body) := by
  induction modes generalizing depth with
  | nil => exact scope
  | cons mode modes ih =>
      apply ih (depth := depth + 1)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using scope

theorem ControlScoped.unclose (scope : ControlScoped depth control) :
    ControlScoped depth (NativeQuantity.unclose control) := by
  cases control <;> exact scope

theorem ControlScoped.functionTail (scope : ControlScoped depth control) :
    ControlScoped depth (NativeQuantity.functionTail term control) := by
  unfold NativeQuantity.functionTail
  split
  · exact scope.unclose
  · exact scope

theorem ControlScoped.reclose (scope : ControlScoped depth control) :
    ControlScoped depth (NativeQuantity.reclose control) := by
  cases control <;> exact scope

theorem ControlScoped.openScopes (scope : ControlScoped depth control)
    (opened : NativeQuantity.openScopes count control = some result) : ControlScoped depth result := by
  induction count generalizing depth control result with
  | zero => simp only [openScopes, Option.some.injEq] at opened; cases opened; exact scope.reclose
  | succ count ih =>
      cases control <;> try simp [NativeQuantity.openScopes] at opened
      case scope mode body =>
        obtain ⟨inside, found, same⟩ := opened
        cases same
        have insideScope : ControlScoped (depth + 1) body := scope
        exact ih (depth := depth + 1) insideScope found

theorem ControlScoped.openFunctions (scope : ControlScoped depth control)
    (opened : NativeQuantity.openFunctions count control = some result) : ControlScoped depth result := by
  cases count with
  | zero => cases opened; exact scope
  | succ count =>
      cases control <;> try simp [NativeQuantity.openFunctions] at opened
      case closure body =>
        have insideScope : ControlScoped depth body := scope
        exact insideScope.openScopes opened

theorem ControlScoped.caseBody (scope : ControlScoped depth control) :
    ControlScoped depth (NativeQuantity.caseBody count control) := by
  cases opened : NativeQuantity.openFunctions count control with
  | none => simpa only [NativeQuantity.caseBody, opened, Option.getD_none] using scope
  | some result => simpa only [NativeQuantity.caseBody, opened, Option.getD_some] using scope.openFunctions opened

end Jihoo.NativeKernel.Environment.ContextQuantity
