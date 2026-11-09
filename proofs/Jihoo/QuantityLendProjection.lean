import Jihoo.QuantityContextProjection

/-! Structural projection of a deliberately bounded Core execution fragment.
The graph view, contextual domain observer and whole-Core typing are trusted
interfaces, not proved implementations. Unlike the preceding alias endpoint,
reader and continuation controls are recursively derived from original nodes. -/
namespace Jihoo.Quantity.LendProjection
open Binders ContextProjection

inductive Node where
  | var (k : Nat)
  | literal
  | seq (first second : Nat)
  | borrow (owner : Nat)
  | lam (erased : Bool) (domain body : Nat)
  | lend (owner reader continuation : Nat)
  | unsupported
  deriving DecidableEq, Repr

abbrev Syntax := Nat → Node

def head (graph : Syntax) (id : Nat) : Head := match graph id with
  | .var k => .var k
  | .lam e t b => .lam e t b
  | .lend x _ _ => .lend x
  | _ => .other

structure Shape where
  owner : Nat
  reader : Nat
  continuation : Nat
  readerContext : List Entry
  continuationContext : List Entry
  resultMode : BinderMode
  deriving DecidableEq, Repr

/-- Same known non-borrow-holding result classes used by Core.outlived.
Their formation/instantiation safety remains a typing assumption. -/
def resultAllowed : Domain → Bool
  | .index | .scalar | .flatData | .boxedData | .buffer | .back => true
  | _ => false

/-- Original annotations are observed in their original contexts, before each
binder is appended. Whole-Core typing additionally checks domain conversion:
Ref(owner type), reader result type, and shifted returned-owner type. -/
def prepare (graph : Syntax) (observe : Observe) (ctx : List Entry) (root : Nat) :
    Option Shape := do
  let .lend x f g := graph root | none
  let .var k := graph x | none
  let owner ← lookup ctx k
  let _ ← projectAlias (ctx.reverse.map Entry.descriptor) k .pure
  let .lam false refTy read := graph f | none
  let readerDomain ← observe (ctx.map Entry.raw) refTy
  if readerDomain != .borrow then none else do
  let readerContext ← enter observe ctx false refTy
  let .lam false resultTy inner := graph g | none
  let resultDomain ← observe (ctx.map Entry.raw) resultTy
  if !resultAllowed resultDomain then none else do
  let resultCap ← classify false resultDomain
  let resultContext ← enter observe ctx false resultTy
  let .lam false ownerTy rest := graph inner | none
  let returnedDomain ← observe (resultContext.map Entry.raw) ownerTy
  if returnedDomain != owner.domain then none else do
  let continuationContext ← enter observe resultContext false ownerTy
  pure ⟨k, read, rest, readerContext, continuationContext, resultCap.mode⟩

/-- The returned-owner slot is opened under the result binder. The result itself
is fresh (possibly linear); treating both slots as aliases would lose ownership. -/
def scopedLend (owner : Nat) (mode : BinderMode) (reader rest : Control) : Control :=
  .seq (.scope .borrowed reader) (.scope mode (.alias (owner + 1) rest))

def checkedLend (owner : Nat) (mode : BinderMode) (reader rest : Control) : Option Control := do
  let before ← (Control.scope .borrowed reader).demand owner
  let after ← (Control.scope mode (.alias (owner + 1) rest)).demand owner
  if before = 0 ∧ after = 1 then some (scopedLend owner mode reader rest) else none

theorem checked_lend_origin (h : checkedLend owner mode reader rest = some c) :
    c = scopedLend owner mode reader rest ∧
    (Control.scope .borrowed reader).demand owner = some 0 ∧
    (Control.scope mode (.alias (owner + 1) rest)).demand owner = some 1 := by
  unfold checkedLend at h
  cases hb : (Control.scope .borrowed reader).demand owner <;> simp_all
  cases ha : (Control.scope mode (.alias (owner + 1) rest)).demand owner <;> simp_all

theorem checked_lend_demand (h : checkedLend owner mode reader rest = some c) :
    c.demand owner = some 1 := by
  obtain ⟨rfl, hb, ha⟩ := checked_lend_origin h
  change reader.demand (owner + 1) = some 0 at hb
  simp [scopedLend, Control.demand, hb, ha]

theorem checked_lend_finished (h : checkedLend owner mode reader rest = some c)
    (run : Finishes c xs) : xs.count owner = 1 := run.count_eq (checked_lend_demand h)

theorem checked_lend_prefix (h : checkedLend owner mode reader rest = some c)
    (run : Prefix c xs) : xs.count owner ≤ 1 := run.count_le (checked_lend_demand h)

/-- A successful reader discharges only its borrow slot. The continuation
first identifies the returned slot, then discharges the distinct result slot. -/
theorem scoped_lend_finishes (readRun : Finishes reader xs) (restRun : Finishes rest ys) :
    Finishes (scopedLend owner mode reader rest)
      (discharge xs ++ discharge (ys.map (openOwner (owner + 1)))) :=
  .seq (.bind readRun) (.bind (restRun.rename (openOwner (owner + 1))))

theorem lend_trace_count (xs ys : List Nat) :
    (discharge xs ++ discharge (ys.map (openOwner (owner + 1)))).count r =
      xs.count (r + 1) + ys.count (r + 2) + (if owner = r then ys.count 0 else 0) := by
  simp [List.count_append, discharge_count, openOwner_count, Nat.add_assoc]

theorem checked_lend_body_traces (h : checkedLend owner mode reader rest = some c)
    (readRun : Finishes reader xs) (restRun : Finishes rest ys) :
    xs.count (owner + 1) + ys.count (owner + 2) + ys.count 0 = 1 := by
  have origin := (checked_lend_origin h).1
  have run := scoped_lend_finishes (owner := owner) (mode := mode) readRun restRun
  rw [← origin] at run
  have count := checked_lend_finished h run
  rw [lend_trace_count] at count
  simpa using count

/-- Two independent limits: depth bounds recursion, remaining work bounds total
visited nodes including repeated references. The owner and three lambda inspections in prepare
are charged as well. No partial control escapes a failed recursive projection. -/
def project (graph : Syntax) (observe : Observe) :
    Nat → List Entry → Nat → Nat → Option (Control × Nat)
  | 0, _, _, _ => none
  | _ + 1, _, _, 0 => none
  | depth + 1, ctx, root, budget + 1 => match graph root with
    | .literal => some (.pure, budget)
    | .var k => do
        let entry ← lookup ctx k
        if entry.raw.erased then none else some (.use k, budget)
    | .borrow owner => if budget = 0 then none else match graph owner with
        | .var k => do
            let entry ← lookup ctx k
            if entry.raw.erased then none else some (.pure, budget - 1)
        | _ => none
    | .seq first second => do
        let (a, remaining) ← project graph observe depth ctx first budget
        let (b, remaining) ← project graph observe depth ctx second remaining
        pure (.seq a b, remaining)
    | .lend _ _ _ => do
        if budget < 4 then none else do
        let shape ← prepare graph observe ctx root
        let (reader, remaining) ← project graph observe depth shape.readerContext shape.reader (budget - 4)
        let (rest, remaining) ← project graph observe depth shape.continuationContext shape.continuation remaining
        let c ← checkedLend shape.owner shape.resultMode reader rest
        pure (c, remaining)
    | _ => none

/-- Source/control correspondence for this structural fragment. The primitive
sequence view must match real evaluation order; borrow emits no ownership use.
The prepare premise retains the contextual observer/typing boundary explicitly. -/
inductive Projects (graph : Syntax) (observe : Observe) : List Entry → Nat → Control → Prop where
  | literal : graph root = .literal → Projects graph observe ctx root .pure
  | var : graph root = .var k → lookup ctx k = some entry → entry.raw.erased = false →
      Projects graph observe ctx root (.use k)
  | borrow : graph root = .borrow owner → graph owner = .var k →
      lookup ctx k = some entry → entry.raw.erased = false → Projects graph observe ctx root .pure
  | seq : graph root = .seq first second → Projects graph observe ctx first a →
      Projects graph observe ctx second b → Projects graph observe ctx root (.seq a b)
  | lend : prepare graph observe ctx root = some shape →
      Projects graph observe shape.readerContext shape.reader reader →
      Projects graph observe shape.continuationContext shape.continuation rest →
      checkedLend shape.owner shape.resultMode reader rest = some c →
      Projects graph observe ctx root c

theorem project_sound (h : project graph observe depth ctx root budget = some (c, left)) :
    Projects graph observe ctx root c := by
  induction depth generalizing ctx root budget c left with
  | zero => simp [project] at h
  | succ depth ih =>
    cases budget with
    | zero => simp [project] at h
    | succ budget =>
      cases hv : graph root with
      | literal => simp [project, hv] at h; obtain ⟨rfl, rfl⟩ := h; exact .literal hv
      | var k =>
        simp only [project, hv] at h
        cases hl : lookup ctx k <;> simp_all
        obtain ⟨he, rfl, rfl⟩ := h
        exact .var hv hl he
      | borrow owner =>
        by_cases hz : budget = 0
        · simp [project, hv, hz] at h
        simp only [project, hv, hz, ↓reduceIte] at h
        cases ho : graph owner <;> simp only [ho] at h
        all_goals try contradiction
        case var k =>
          cases hl : lookup ctx k <;> simp_all
          obtain ⟨he, rfl, rfl⟩ := h
          exact .borrow hv ho hl he
      | seq first second =>
        simp only [project, hv] at h
        cases ha : project graph observe depth ctx first budget <;> simp_all
        case some ra =>
          obtain ⟨a, rem⟩ := ra
          cases hb : project graph observe depth ctx second rem <;> simp_all
          case some rb =>
            obtain ⟨b, rem'⟩ := rb
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            exact .seq hv (ih ha) (ih hb)
      | lend x f g =>
        simp only [project, hv] at h
        split at h <;> simp_all
        cases hs : prepare graph observe ctx root <;> simp_all
        case some shape =>
          cases ha : project graph observe depth shape.readerContext shape.reader (budget - 4) <;> simp_all
          case some ra =>
            obtain ⟨a, rem⟩ := ra
            cases hb : project graph observe depth shape.continuationContext shape.continuation rem <;> simp_all
            case some rb =>
              obtain ⟨b, rem'⟩ := rb
              cases hc : checkedLend shape.owner shape.resultMode a b <;> simp_all
              exact .lend hs (ih ha) (ih hb) hc
      | lam _ _ _ | unsupported => simp [project, hv] at h

theorem project_budget_decreases (h : project graph observe depth ctx root budget = some (c, left)) :
    left < budget := by
  induction depth generalizing ctx root budget c left with
  | zero => simp [project] at h
  | succ depth ih =>
    cases budget with
    | zero => simp [project] at h
    | succ budget =>
      cases hv : graph root with
      | literal => simp [project, hv] at h; obtain ⟨rfl, rfl⟩ := h; omega
      | var k =>
        simp only [project, hv] at h
        cases hl : lookup ctx k <;> simp_all
      | borrow owner =>
        by_cases hz : budget = 0
        · simp [project, hv, hz] at h
        simp only [project, hv, hz, ↓reduceIte] at h
        cases ho : graph owner <;> simp only [ho] at h
        all_goals try contradiction
        case var k =>
          cases hl : lookup ctx k <;> simp_all
          obtain ⟨he, rfl, rfl⟩ := h
          omega
      | seq first second =>
        simp only [project, hv] at h
        cases ha : project graph observe depth ctx first budget <;> simp_all
        case some ra =>
          obtain ⟨a, rem⟩ := ra
          cases hb : project graph observe depth ctx second rem <;> simp_all
          case some rb =>
            obtain ⟨b, rem'⟩ := rb
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            have hfirst := ih ha
            have hsecond := ih hb
            omega
      | lend x f g =>
        simp only [project, hv] at h
        split at h <;> simp_all
        cases hs : prepare graph observe ctx root <;> simp_all
        case some shape =>
          cases ha : project graph observe depth shape.readerContext shape.reader (budget - 4) <;> simp_all
          case some ra =>
            obtain ⟨a, rem⟩ := ra
            cases hb : project graph observe depth shape.continuationContext shape.continuation rem <;> simp_all
            case some rb =>
              obtain ⟨b, rem'⟩ := rb
              cases hc : checkedLend shape.owner shape.resultMode a b <;> simp_all
              have hfirst := ih ha
              have hsecond := ih hb
              omega
      | lam _ _ _ | unsupported => simp [project, hv] at h

/-- Public structural entry point: obtain the ambient descriptors from the
original leading telescope, rather than accepting a caller's context. The
returned control runs in that context; it is the function body, not a closure. -/
def rootedProject (graph : Syntax) (observe : Observe) (depth budget root : Nat) :
    Option (List Entry × Control × Nat) := do
  let (ctx, leaf) ← walk (head graph) observe depth [] root
  let (control, remaining) ← project graph observe depth ctx leaf budget
  pure (ctx, control, remaining)

theorem rooted_project_sound
    (h : rootedProject graph observe depth budget root = some (ctx, c, remaining)) :
    ∃ leaf, Path (head graph) observe [] root ctx leaf ∧ Authentic observe ctx ∧
      Projects graph observe ctx leaf c ∧ remaining < budget := by
  unfold rootedProject at h
  cases hw : walk (head graph) observe depth [] root with
  | none => simp [hw] at h
  | some result =>
    obtain ⟨original, leaf⟩ := result
    simp only [hw] at h
    cases hp : project graph observe depth original leaf budget with
    | none => simp [hp] at h
    | some projected =>
      obtain ⟨control, left⟩ := projected
      simp [hp] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨leaf, walk_sound hw, rooted_authentic hw, project_sound hp, project_budget_decreases hp⟩

end Jihoo.Quantity.LendProjection
