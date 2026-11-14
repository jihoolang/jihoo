import Jihoo.NativeCallReplay
import Jihoo.NativeQuantity
import Jihoo.NativeQuantityFunctions
import Jihoo.NativeEnvironmentBindingAlgebra

/-! Control accounting for a checked unknown call. Its signature supplies the
runtime argument positions. A closing function supplies its independently
validated local scopes and zero capture demand. This theorem substitutes no
effectful code tree for a variable and asserts no heap semantics. -/
namespace Jihoo.NativeKernel.Environment.CallReplay
open Jihoo.Quantity NativeQuantity

/-- The body of an interpreted function has passed its binder obligations and
cannot consume any owner from the caller. This is the contract obtained from
an admitted closure; it is not inferred from HasType alone. -/
def BodyContract (modes : List BinderMode) (body : Control) : Prop :=
  LocalScopes (Control.scopes modes body) ∧ ∀ resource, (Control.scopes modes body).demand resource = some 0

/-- The callee expression and every relevant argument are projected once.
No normalization of the runtime callee expression takes place here. -/
def callControl (head : Control) (arguments : List Control) : Control :=
  .seq head (sequence arguments)

theorem sequence_demand (arguments : List Control) (resource : Nat) :
    (sequence arguments).demand resource =
      arguments.foldr (fun control total => do return (← control.demand resource) + (← total)) (some 0) := by
  induction arguments with
  | nil => rfl
  | cons first rest ih => simp only [sequence, Control.demand, List.foldr_cons, ih]

theorem contracted_body_demand (contract : BodyContract modes body) :
    (Control.seq (callControl head arguments) (Control.scopes modes body)).demand resource =
      (callControl head arguments).demand resource := by
  simp only [Control.demand, contract.2]
  cases found : head.demand resource <;> cases tail : (sequence arguments).demand resource <;>
    simp [callControl, Control.demand, found, tail]

theorem contracted_local_scopes (contract : BodyContract modes body) :
    LocalScopes (Control.scopes modes body) := contract.1

theorem contracted_finished (contract : BodyContract modes body)
    (checked : (callControl head arguments).demand resource = some count)
    (run : Jihoo.Quantity.Finishes (Control.seq (callControl head arguments) (Control.scopes modes body)) events) :
    events.count resource = count := by
  apply run.count_eq
  exact (contracted_body_demand contract).trans checked

theorem contracted_prefix (contract : BodyContract modes body)
    (checked : (callControl head arguments).demand resource = some count)
    (run : Jihoo.Quantity.Prefix (Control.seq (callControl head arguments) (Control.scopes modes body)) events) :
    events.count resource ≤ count := by
  apply run.count_le
  exact (contracted_body_demand contract).trans checked

/-- A successful sentinel query on a genuinely closed projected function
establishes the unknown-call body contract for every caller resource. -/
theorem closed_raw_body_contract (closed : term.Scoped 0)
    (projected : NativeQuantity.project fuel term = some (.closure (.scopes modes body)))
    (checked : NativeQuantity.check fuel 0 [] [] term = true) : BodyContract modes body := by
  obtain ⟨control, found, sentinel, _, _⟩ := NativeQuantity.checked_origin checked
  have same : control = .closure (.scopes modes body) := Option.some.inj (found.symm.trans projected)
  subst control
  have inner : (Control.scopes modes body).demand 0 = some 0 := by
    cases value : (Control.scopes modes body).demand 0 <;> simp_all [Control.demand]
  refine ⟨NativeQuantity.demand_localScopes _ inner,?_⟩
  intro resource
  let ρ : Nat → Nat := fun x => if x = resource then 0 else x + 1
  have fiber : ∀ x, ρ x = 0 ↔ x = resource := by
    intro x
    simp [ρ]
  have stable := NativeQuantity.project_rename fuel term ρ
  rw [Environment.closed_rename closed ρ, projected] at stable
  simp only [Option.map_some, Option.some.injEq, Control.rename] at stable
  have bodyStable : (Control.scopes modes body).rename ρ = Control.scopes modes body :=
    (Control.closure.inj stable).symm
  have demand := NativeQuantity.demand_rename (Control.scopes modes body) fiber
  rw [bodyStable] at demand
  exact demand.symm.trans inner

end Jihoo.NativeKernel.Environment.CallReplay
