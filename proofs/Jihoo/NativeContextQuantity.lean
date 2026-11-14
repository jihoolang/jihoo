import Jihoo.NativeContextModes
import Jihoo.NativeRelevantFields
import Jihoo.NativeControlScope
import Jihoo.NativeEnvironmentCaseQuantity

/-! Context-indexed resource projection at the unified resource boundary. Source
contexts are retained while representations are resolved. Calls replay authentic
native signatures; their runtime syntax is never normalized. Semantic closing
interpretation proofs remain downstream of this executable dependency graph. -/
namespace Jihoo.NativeKernel.Environment.ContextQuantity
open Jihoo.Quantity NativeQuantity ContextModes CallReplay
variable {control : Control}

structure Opened where
  context : Context
  modes : List BinderMode
  body : Term
  deriving Repr

/-- Consume only syntactically leading source lambdas. Later computed function
expressions remain intact and are evaluated once through their checked signature. -/
def openHead : Nat → Environment → Context → Term → List Term → Option Opened
  | 0 => fun _ _ _ _ => none
  | fuel + 1 => fun env ctx head supplied => match head, supplied with
      | .lam erased domain body, _ :: arguments => do
          if !CodeKinds.contextOK fuel env ctx || !(Checker.binder fuel env ctx erased domain).isSome then none else
          let mode ← resolve fuel env ctx erased domain
          let rest ← openHead fuel env (⟨domain,erased⟩ :: ctx) body arguments
          pure ⟨rest.context,mode :: rest.modes,rest.body⟩
      | _, _ => some ⟨ctx,[],head⟩

/-- Native runtime positions outside calls and binding-sensitive operators. -/
def runtimeFields : Op → Option (List Nat)
  | .arith _ | .strict | .uadd | .usub | .alloc | .free | .drop _ | .index => some [0,1]
  | .store => some [0,1,2]
  | .elements count => some (List.range count)
  | .pack => some [1]
  | .witness => some [0]
  | .give erased => some (if erased then [1] else [1,2])
  | _ => none

/-- Types and evidence have no runtime ownership contribution. -/
def erasedNode : Op → Bool
  | .universe _ | .prop | .u64 | .i64 | .array | .lt | .eq | .refl |
      .transport | .ind _ _ | .ltAdd | .ltCancel | .ltLe | .zeroLe |
      .refine | .proof | .buffer | .ref | .back _ | .borrow | .deref |
      .absurd | .pi _ | .natural _ | .integer _ | .decide => true
  | _ => false

def projectRaw : Nat → Environment → Context → Term → Option Control
  | 0, _, _, _ => none
  | _ + 1, _, ctx, .var index => do
      let binding ← lookup ctx index
      if binding.erased then none else some (.use index)
  | fuel + 1, env, ctx, .node op arguments => do
      if arguments.length != op.arity then none else
      match op with
      | .global _ | .lend => none
      | .con family constructor count => do
          let entry ← env.families[family]?
          let signature ← entry.signatures[constructor]?
          if count != arguments.length then none else
          let relevant ← EnvironmentQuantity.relevantFields entry.declaration.data signature.fields arguments
          let controls ← relevant.mapM (projectRaw fuel env ctx)
          pure (sequence controls)
      | .elim family count | .caseOf family count => do
          let table := EnvironmentCaseQuantity.compileTable env
          let entry ← EnvironmentCaseQuantity.findFamily table family
          if !entry.declaration.data then some .pure else
          let recursion := entry.boxed && match op with | .elim _ _ => true | _ => false
          let (cases, scrutinee) ← Checker.splitCases count (arguments.drop 1)
          let first ← projectRaw fuel env ctx scrutinee
          let controls ← EnvironmentCaseQuantity.caseControls (projectRaw fuel env ctx)
            entry.declaration.params recursion entry.signatures cases
          pure (.seq first (EnvironmentCaseQuantity.alternatives controls))
      | .view recursion family count => do
          let table := EnvironmentCaseQuantity.compileTable env
          let entry ← EnvironmentCaseQuantity.findFamily table family
          if !entry.boxed then none else
          let (cases, scrutinee) ← Checker.splitCases count (arguments.drop 1)
          let first ← projectRaw fuel env ctx scrutinee
          let controls ← EnvironmentCaseQuantity.caseControls (projectRaw fuel env ctx)
            entry.declaration.params recursion entry.signatures cases
          pure (.seq first (EnvironmentCaseQuantity.alternatives controls))
      | .app => do
          let (head, supplied) ← splitSpine fuel (.node .app arguments) []
          let (entries, result) ← CallReplay.checked fuel env ctx false head supplied
          if !partialOK fuel env ctx entries result then none else
          let opened ← openHead fuel env ctx head supplied
          let runtime ← (runtimeArguments entries).mapM (projectRaw fuel env ctx)
          let body ← projectRaw fuel env opened.context opened.body
          pure (if opened.modes.isEmpty then callControl body runtime
            else .seq (sequence runtime) (.scopes opened.modes body))
      | .lam erased =>
          match arguments with
          | [domain, bodyTerm] => do
              if !CodeKinds.contextOK fuel env ctx || !(Checker.binder fuel env ctx erased domain).isSome then none else
              let mode ← resolve fuel env ctx erased domain
              let body ← projectRaw fuel env (⟨domain,erased⟩ :: ctx) bodyTerm
              pure (.closure (.scope mode (functionTail bodyTerm body)))
          | _ => none
      | .ifLt | .ifEq =>
          match arguments with
          | [left,right,yes,no] => do
              let first ← fields (projectRaw fuel env ctx) arguments [0,1]
              let proof := if op = .ifLt then Term.lt left right else Term.eq left right
              let yesControl ← projectRaw fuel env (⟨proof,true⟩ :: ctx) yes
              let noControl ← projectRaw fuel env ctx no
              pure (.seq first (.branch (.scope .erased yesControl) noControl))
          | _ => none
      | .fold => do
          let first ← fields (projectRaw fuel env ctx) arguments [0,1]
          let body ← fetch (projectRaw fuel env ctx) arguments 2
          pure (.seq first (.repeat (caseBody 3 body)))
      | .loop => do
          let first ← fields (projectRaw fuel env ctx) arguments [0,2]
          let body ← fetch (projectRaw fuel env ctx) arguments 3
          pure (.seq first (.repeat (caseBody 3 body)))
      | .load => do
          let first ← fields (projectRaw fuel env ctx) arguments [0,1]
          let body ← fetch (projectRaw fuel env ctx) arguments 3
          pure (.seq first (.once (caseBody 2 body)))
      | .take => do
          let first ← fetch (projectRaw fuel env ctx) arguments 0
          let body ← fetch (projectRaw fuel env ctx) arguments 1
          pure (.seq first (.once (caseBody 2 body)))
      | _ =>
          if erasedNode op then some .pure else do
          let relevant ← runtimeFields op
          fields (projectRaw fuel env ctx) arguments relevant

/-- Validate the computed control's source-local scope. The check is derived
from the same context depth and complete finite control tree. -/
def project (fuel : Nat) (env : Environment) (ctx : Context) (term : Term) : Option Control := do
  let control ← projectRaw fuel env ctx term
  if scopeCheck ctx.length control then some control else none

theorem project_scope (h : project fuel env ctx term = some control) :
    ControlScoped ctx.length control := by
  unfold project at h
  obtain ⟨candidate, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i accepted
    cases h
    exact scopeCheck_correct.mp accepted
  · contradiction

/-- The single closed control gate; its context and outer owner list are
always genuinely empty. Declaration typing is checked by the same program path. -/
def checkResource (fuel : Nat) (env : Environment) (term : Term) : Bool :=
  (project fuel env [] term).any (fun control => control.demand 0 == some 0)

def ResourceSafe (env : Environment) (term : Term) : Prop :=
  EnvironmentCaseQuantity.TableValid env (EnvironmentCaseQuantity.compileTable env) ∧
    ∃ fuel control, project fuel env [] term = some control ∧
      control.demand 0 = some 0 ∧ LocalScopes control ∧ ControlScoped 0 control

theorem checkResource_sound (checked : checkResource fuel env term = true) : ResourceSafe env term := by
  refine ⟨EnvironmentCaseQuantity.compileTable_valid,?_⟩
  cases projected : project fuel env [] term with
  | none => simp [checkResource, projected] at checked
  | some control =>
      have demand : control.demand 0 = some 0 := by
        simpa only [checkResource, projected, Option.any_some, beq_iff_eq] using checked
      exact ⟨fuel,control,projected,demand,NativeQuantity.demand_localScopes _ demand,project_scope projected⟩

/-- Convenience conjunction of same-checker typing and the authentic closed
resource query. The unified declaration path checks these same components. -/
def checkClosed (fuel quantityFuel : Nat) (env : Environment) (term expected : Term) : Bool :=
  Checker.check fuel env [] false term expected &&
    checkResource quantityFuel env term

def ClosedSafe (env : Environment) (term expected : Term) : Prop :=
  HasType env [] false term expected ∧
    EnvironmentCaseQuantity.TableValid env (EnvironmentCaseQuantity.compileTable env) ∧ ∃ fuel control,
    project fuel env [] term = some control ∧ control.demand 0 = some 0 ∧ LocalScopes control ∧ ControlScoped 0 control

theorem checkClosed_sound (checked : checkClosed fuel quantityFuel env term expected = true) :
    ClosedSafe env term expected := by
  obtain ⟨typed, safe⟩ := Bool.and_eq_true_iff.mp checked
  refine ⟨Checker.check_sound typed,EnvironmentCaseQuantity.compileTable_valid,?_⟩
  cases projected : project quantityFuel env [] term with
  | none => simp [checkResource, projected] at safe
  | some control =>
      have demand : control.demand 0 = some 0 := by
        simpa only [checkResource, projected, Option.any_some, beq_iff_eq] using safe
      exact ⟨quantityFuel,control,projected,demand,NativeQuantity.demand_localScopes _ demand,project_scope projected⟩

/-- The checked closed boundary supplies the resource contract of a closing
function value. Function typing alone is insufficient for this theorem. -/
theorem checked_body_contract
    (checked : checkClosed fuel quantityFuel env term expected = true)
    (projected : project quantityFuel env [] term = some (.closure (.scopes modes body))) :
    BodyContract modes body := by
  have safe := (Bool.and_eq_true_iff.mp checked).2
  have demand : (Control.closure (.scopes modes body)).demand 0 = some 0 := by
    simpa only [checkResource, projected, Option.any_some, beq_iff_eq] using safe
  have locals := NativeQuantity.demand_localScopes _ demand
  have scope := project_scope projected
  exact (show ControlScoped 0 (.scopes modes body) from scope).bodyContract locals

theorem checked_linear_head
    (checked : checkClosed fuel quantityFuel env term expected = true)
    (projected : project quantityFuel env [] term = some (.closure (.scopes (.linear :: modes) body))) :
    (Control.scopes modes body).demand 0 = some 1 :=
  (checked_body_contract checked projected).1.1

theorem checked_erased_head
    (checked : checkClosed fuel quantityFuel env term expected = true)
    (projected : project quantityFuel env [] term = some (.closure (.scopes (.erased :: modes) body))) :
    (Control.scopes modes body).demand 0 = some 0 :=
  (checked_body_contract checked projected).1.1

theorem closed_finished_empty (scope : ControlScoped 0 control) (locals : LocalScopes control)
    (run : Jihoo.Quantity.Finishes control events) : events = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro resource member
  have count := run.count_eq (scope.demand_above locals (Nat.zero_le resource))
  have positive : 0 < events.count resource := List.count_pos_iff.mpr member
  omega

theorem closed_prefix_empty (scope : ControlScoped 0 control) (locals : LocalScopes control)
    (run : Jihoo.Quantity.Prefix control events) : events = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro resource member
  have count := run.count_le (scope.demand_above locals (Nat.zero_le resource))
  have positive : 0 < events.count resource := List.count_pos_iff.mpr member
  omega

end Jihoo.NativeKernel.Environment.ContextQuantity
