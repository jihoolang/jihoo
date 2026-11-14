import Jihoo.NativeSubstitution
import Jihoo.QuantitySubstitution

/-! Executable resource projection of the complete native Term vocabulary.

This layer checks resource use, not typing, allocation, lease lifetime, or heap
safety. The runtime positions follow Core.uses. Signature-dependent calls and
family cases, and alias-sensitive Lend, fail explicitly. Types and evidence are
not traversed at runtime. The successful fragment includes ownership primitives,
balanced evidence branches, exact-once continuations, and repeated loop bodies.
No Buffer typing rule or general code substitution theorem is introduced.

Fuel bounds recursive tree depth. Local scopes are checked even when there are no outer
owners, by querying a fresh sentinel in check. A native-source correspondence
proof for Core.uses itself is a separate obligation from this tree theorem. -/
namespace Jihoo.NativeKernel.NativeQuantity

open Jihoo.Quantity

/-- Only syntactically resolved native binder domains are classified. Family
ownership and conversion of neutral domains require checked signature metadata.
Universe/type binders are conservatively deferred; first-order code admission
is a separate typing obligation. -/
def binderMode (erased : Bool) (domain : Term) : Option BinderMode :=
  if erased then some .erased else
  match domain with
  | .node .buffer [_] | .node (.back _) [_, _] => some .linear
  | .node .ref [_] => some .borrowed
  | .node .u64 [] | .node .i64 [] | .node .array [_] | .node .refine [_] |
      .node (.pi _) [_, _] => some .unrestricted
  | _ => none

/-- A remaining leading telescope is a returned closure. Opening exactly n
callback arguments must not open a later returned function as well. -/
def reclose : Control → Control
  | c@(.scope _ _) => .closure c
  | c => c

/-- Open scopes inside one leading function telescope. Failure preserves the
source's ordinary-closure fallback through `caseBody`. -/
def openScopes : Nat → Control → Option Control
  | 0, c => some (reclose c)
  | n + 1, .scope mode body => (openScopes n body).map (Control.scope mode)
  | _, _ => none

/-- A function's complete leading lambdas share a single closure boundary.
Callbacks open exactly the requested prefix; residual lambdas are reclosed. -/
def openFunctions : Nat → Control → Option Control
  | 0, c => some c
  | n + 1, .closure body => openScopes (n + 1) body
  | _, _ => none

/-- Exactly a syntactically complete leading native lambda node. -/
def lambdaHead : Term → Bool
  | .node (.lam _) [_, _] => true
  | _ => false

def unclose : Control → Control
  | .closure body => body
  | body => body

/-- Merge only syntactically adjacent leading lambdas. An effect, application,
or other operation between lambdas retains the genuine closure boundary. -/
def functionTail (t : Term) (body : Control) : Control :=
  if lambdaHead t then unclose body else body

def caseBody (count : Nat) (c : Control) : Control :=
  (openFunctions count c).getD c

def sequence : List Control → Control
  | [] => .pure
  | c :: cs => .seq c (sequence cs)

def fetch (f : Term → Option Control) (args : List Term) (i : Nat) : Option Control :=
  args[i]?.bind f

def fields (f : Term → Option Control) (args : List Term) : List Nat → Option Control
  | [] => some .pure
  | i :: indices => do
      let c ← fetch f args i
      let cs ← fields f args indices
      pure (.seq c cs)

/-- A resolved binder domain whose inhabitants cannot be functions. This is a
syntactic conservative gate; neutral domains and family signatures are deferred. -/
def domainNonFunction : Term → Bool
  | .node .u64 _ | .node .i64 _ | .node .array _ | .node .refine _ |
      .node .buffer _ | .node .ref _ | .node (.back _) _ | .node .lt _ | .node .eq _ => true
  | _ => false

/-- Bound variable results consult the consumed lambda domains. Free variables,
residual lambdas, neutral calls, and operations returning arbitrary continuation
types are rejected. This prevents counting owned arguments in partial calls. -/
def callResult (locals : List Bool) : Term → Bool
  | .var x => locals[x]?.getD false
  | .node op _ => match op with
      | .natural _ | .integer _ | .elements _ | .arith _ | .uadd | .usub | .index |
          .witness | .pack | .alloc | .store | .give _ | .fold => true
      | _ => false

structure CallPlan where
  modes : List BinderMode
  runtimeArgs : List Term
  body : Term
  deriving Repr

/-- Gather the whole left-associated application spine in argument order. -/
def splitSpine : Nat → Term → List Term → Option (Term × List Term)
  | 0, _, _ => none
  | fuel + 1, .node .app [f, a], args => splitSpine fuel f (a :: args)
  | _ + 1, head, args => some (head, args)

/-- Each consumed lambda contributes one scope. Runtime arguments stay outside
all scopes and are visited exactly once; erased arguments contribute no events. -/
def peelCallAux : Nat → List Bool → Bool → Term → List Term → Option CallPlan
  | 0, _, _, _, _ => none
  | _ + 1, locals, linearSeen, body, [] =>
      if callResult locals body || !linearSeen
      then some ⟨[], [], body⟩ else none
  | fuel + 1, locals, linearSeen, .node (.lam erased) [domain, body], a :: args => do
      let mode ← binderMode erased domain
      let rest ← peelCallAux fuel (domainNonFunction domain :: locals)
        (linearSeen || mode == .linear) body args
      pure ⟨mode :: rest.modes,
        (if erased then rest.runtimeArgs else a :: rest.runtimeArgs), rest.body⟩
  | _ + 1, _, _, _, _ :: _ => none

/-- Native partial calls may return any value after only non-linear runtime
arguments. An owned argument still requires a known nonfunction result. -/
def peelCall (fuel : Nat) (locals : List Bool) (head : Term) (args : List Term) : Option CallPlan :=
  peelCallAux fuel locals false head args

def finishCall (f : Term → Option Control) (p : CallPlan) : Option Control := do
  let arguments ← p.runtimeArgs.mapM f
  let body ← f p.body
  pure (.seq (sequence arguments) (.scopes p.modes body))

def projectCall (fuel : Nat) (f : Term → Option Control) (t : Term) : Option Control := do
  let (head, args) ← splitSpine fuel t []
  let plan ← peelCall fuel [] head args
  finishCall f plan

/-- All 54 native constructors are dispatched here. Rejection is intentional
for dynamic signatures and unresolved call spines, rather than treating them as
zero use. Erased nodes need no runtime analysis of their children. -/
def project : Nat → Term → Option Control
  | 0, _ => none
  | _ + 1, .var x => some (.use x)
  | fuel + 1, .node op args => do
      if args.length != op.arity then none else
      match op with
      | .global _ | .con _ _ _ | .elim _ _ | .caseOf _ _ | .view _ _ _ | .lend => none
      | .app => projectCall fuel (project fuel) (.node .app args)
      | .universe _ | .prop | .u64 | .i64 | .array | .lt | .eq | .refl |
          .transport | .ind _ _ | .ltAdd | .ltCancel | .ltLe | .zeroLe |
          .refine | .proof | .buffer | .ref | .back _ | .borrow | .deref |
          .absurd | .pi _ | .natural _ | .integer _ | .decide => some .pure
      | .arith _ | .strict | .uadd | .usub | .alloc | .free | .drop _ | .index =>
          fields (project fuel) args [0, 1]
      | .store => fields (project fuel) args [0, 1, 2]
      | .elements count => fields (project fuel) args (List.range count)
      | .pack => fetch (project fuel) args 1
      | .witness => fetch (project fuel) args 0
      | .give erased => fields (project fuel) args (if erased then [1] else [1, 2])
      | .lam erased => do
          let domain ← args[0]?
          let mode ← binderMode erased domain
          let bodyTerm ← args[1]?
          let body ← project fuel bodyTerm
          pure (.closure (.scope mode (functionTail bodyTerm body)))
      | .ifLt | .ifEq => do
          let first ← fields (project fuel) args [0, 1]
          let yes ← fetch (project fuel) args 2
          let no ← fetch (project fuel) args 3
          pure (.seq first (.branch (.scope .erased yes) no))
      | .fold => do
          let first ← fields (project fuel) args [0, 1]
          let body ← fetch (project fuel) args 2
          pure (.seq first (.repeat (caseBody 3 body)))
      | .loop => do
          let first ← fields (project fuel) args [0, 2]
          let body ← fetch (project fuel) args 3
          pure (.seq first (.repeat (caseBody 3 body)))
      | .load => do
          let first ← fields (project fuel) args [0, 1]
          let body ← fetch (project fuel) args 3
          pure (.seq first (.once (caseBody 2 body)))
      | .take => do
          let first ← fetch (project fuel) args 0
          let body ← fetch (project fuel) args 1
          pure (.seq first (.once (caseBody 2 body)))

/-- The fresh sentinel forces local linear/erased/capture checks even for an
empty owner list. Runtime scope of the input is an independent typing premise.
An out-of-scope use of sentinel itself is rejected as well. -/
def check (fuel depth : Nat) (owners erased : List Nat) (t : Term) : Bool :=
  match project fuel t with
  | none => false
  | some c => c.demand depth == some 0 &&
      owners.all (fun r => c.demand r == some 1) &&
      erased.all (fun r => c.demand r == some 0)

def Finishes (fuel : Nat) (t : Term) (events : List Nat) : Prop :=
  ∃ c, project fuel t = some c ∧ Jihoo.Quantity.Finishes c events

def Prefix (fuel : Nat) (t : Term) (events : List Nat) : Prop :=
  ∃ c, project fuel t = some c ∧ Jihoo.Quantity.Prefix c events

/-- Every analyzed local scope is checked, including scopes in alternatives,
closures and loop bodies. Erased subtrees have no runtime obligations. -/
def LocalScopes : Control → Prop
  | .seq a b | .branch a b => LocalScopes a ∧ LocalScopes b
  | .repeat c | .once c | .closure c => LocalScopes c
  | .scope .linear c => c.demand 0 = some 1 ∧ LocalScopes c
  | .scope .erased c => c.demand 0 = some 0 ∧ LocalScopes c
  | .scope .unrestricted c | .scope .borrowed c => LocalScopes c
  | _ => True

theorem demand_localScopes (c : Control) (h : c.demand r = some n) : LocalScopes c := by
  induction c generalizing r n with
  | pure | use | erased | trap => trivial
  | seq a b iha ihb =>
      cases ha : a.demand r <;> cases hb : b.demand r <;>
        simp [Control.demand, ha, hb] at h
      exact ⟨iha ha, ihb hb⟩
  | branch a b iha ihb =>
      cases ha : a.demand r <;> cases hb : b.demand r <;>
        simp [Control.demand, ha, hb] at h
      exact ⟨iha ha, ihb hb⟩
  | «repeat» c ih | closure c ih =>
      cases hc : c.demand r <;> simp [Control.demand, hc] at h
      exact ih hc
  | once c ih => exact ih h
  | scope mode c ih =>
      cases mode with
      | linear =>
          cases hc : c.demand 0 <;> simp [Control.demand, hc] at h
          exact ⟨by simpa [h.1] using hc, ih hc⟩
      | erased =>
          cases hc : c.demand 0 <;> simp [Control.demand, hc] at h
          exact ⟨by simpa [h.1] using hc, ih hc⟩
      | unrestricted | borrowed => exact ih h

theorem checked_origin (h : check fuel depth owners erased t = true) :
    ∃ c, project fuel t = some c ∧ c.demand depth = some 0 ∧
      (∀ r ∈ owners, c.demand r = some 1) ∧
      (∀ r ∈ erased, c.demand r = some 0) := by
  unfold check at h
  cases hp : project fuel t with
  | none => simp [hp] at h
  | some c =>
      refine ⟨c, rfl, ?_⟩
      simpa [hp, Bool.and_eq_true, List.all_eq_true, and_assoc] using h

theorem checked_finished (h : check fuel depth owners erased t = true)
    (run : Finishes fuel t events) : ∀ r ∈ owners, events.count r = 1 := by
  obtain ⟨c, hc, _, ho, _⟩ := checked_origin h
  obtain ⟨c', hc', run⟩ := run
  have : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  exact fun r hr => run.count_eq (ho r hr)

theorem checked_prefix (h : check fuel depth owners erased t = true)
    (run : Prefix fuel t events) : ∀ r ∈ owners, events.count r ≤ 1 := by
  obtain ⟨c, hc, _, ho, _⟩ := checked_origin h
  obtain ⟨c', hc', run⟩ := run
  have : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  exact fun r hr => run.count_le (ho r hr)

theorem checked_erased (h : check fuel depth owners erased t = true)
    (run : Prefix fuel t events) : ∀ r ∈ erased, r ∉ events := by
  obtain ⟨c, hc, _, _, he⟩ := checked_origin h
  obtain ⟨c', hc', run⟩ := run
  have : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  exact fun r hr => erased_unreachable (he r hr) run

theorem checked_sentinel (h : check fuel depth owners erased t = true)
    (run : Prefix fuel t events) : depth ∉ events := by
  obtain ⟨c, hc, hs, _, _⟩ := checked_origin h
  obtain ⟨c', hc', run⟩ := run
  have : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  exact erased_unreachable hs run

theorem checked_localScopes (h : check fuel depth owners erased t = true) :
    ∃ c, project fuel t = some c ∧ LocalScopes c := by
  obtain ⟨c, hc, hs, _, _⟩ := checked_origin h
  exact ⟨c, hc, demand_localScopes c hs⟩

end Jihoo.NativeKernel.NativeQuantity
