import Jihoo.LeaseErasure

/-! Result-carrying finite callers. Owner slots, scalar result slots and lexical
tombstones are distinct. Native exporter association and machine arithmetic are
not formalized; the target is the independent lease-free heap, not MIR CFG. -/
namespace Jihoo.ScalarCoreCallers
open HeapLeases ScopedLend LinearHeapPrograms

inductive Binding where
  | owner (slot : Nat)
  | scalar (slot : Nat)
  | dead
  deriving DecidableEq, Repr
abbrev Context := List Binding

def fresh (ctx : Context) : Context := .owner 0 :: ctx.map fun b => match b with
  | .owner k => .owner (k + 1)
  | other => other

def consumed (slot : Nat) (ctx : Context) : Context := .scalar 0 :: ctx.map fun b => match b with
  | .owner k => if k = slot then .dead else .owner (if slot < k then k - 1 else k)
  | .scalar k => .scalar (k + 1)
  | .dead => .dead

inductive Result where
  | literal (value : Nat)
  | scalar (slot : Nat)
  deriving DecidableEq, Repr

def Result.eval (values : List Nat) : Result → Option Nat
  | .literal v => some v
  | .scalar k => values[k]?

def Result.check (count : Nat) : Result → Bool
  | .literal _ => true
  | .scalar k => k < count

theorem Result.total {result : Result} {values : List Nat} (checked : result.check count = true) (length : values.length = count) :
    ∃ v, result.eval values = some v := by
  cases result with
  | literal v => exact ⟨v, rfl⟩
  | scalar k =>
    have bound : k < values.length := by simpa [Result.check, length] using checked
    exact ⟨values[k], List.getElem?_eq_getElem bound⟩

def ownerSlot (g : Graph.Graph) (ctx : Context) (root : Nat) : Option Nat := do
  let .var k := Graph.nodeAt g root | none
  let .owner slot ← ctx[k]? | none
  pure slot

def resultAt (g : Graph.Graph) (ctx : Context) (root : Nat) : Option Result := do
  match Graph.nodeAt g root with
  | .integer v => pure (.literal v)
  | .var k =>
    let .scalar slot ← ctx[k]? | none
    pure (.scalar slot)
  | _ => none

/-- Lexical scalar interpretation keeps owner/dead entries unavailable. -/
def scalarBindings (ctx : Context) (values : List Nat) : List (Option Nat) :=
  ctx.map fun binding => match binding with | .scalar k => values[k]? | _ => none

def ownerView (ctx : Context) : LinearCoreCallers.Context :=
  ctx.map fun binding => match binding with | .owner k => some k | _ => none

theorem fresh_scalarBindings : scalarBindings (fresh ctx) values = none :: scalarBindings ctx values := by
  simp only [scalarBindings, fresh, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro binding _
  cases binding <;> rfl

theorem consumed_scalarBindings : scalarBindings (consumed slot ctx) (v :: values) =
    some v :: scalarBindings ctx values := by
  simp only [scalarBindings, consumed, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro binding _
  cases binding with
  | scalar | dead => rfl
  | owner k => by_cases eq : k = slot <;> simp [eq]

theorem fresh_ownerView : ownerView (fresh ctx) = LinearCoreCallers.fresh (ownerView ctx) := by
  simp only [ownerView, fresh, LinearCoreCallers.fresh, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro binding _
  cases binding <;> rfl

theorem consumed_ownerView : ownerView (consumed slot ctx) =
    none :: LinearCoreCallers.consumed slot (ownerView ctx) := by
  simp only [ownerView, consumed, LinearCoreCallers.consumed, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro binding _
  cases binding with
  | scalar | dead => rfl
  | owner k => by_cases eq : k = slot <;> simp [eq]

theorem scalarBinding_identity {ctx : Context} {values : List Nat} {k slot v : Nat} (bound : ctx[k]? = some (.scalar slot))
    (value : values[slot]? = some v) : (scalarBindings ctx values)[k]? = some (some v) := by
  simp [scalarBindings, List.getElem?_map, bound, value]

theorem scalar_not_owner (shape : Graph.nodeAt g root = .var k) (bound : ctx[k]? = some (.scalar slot)) :
    ownerSlot g ctx root = none := by simp [ownerSlot, shape, bound]

theorem dead_not_scalar (shape : Graph.nodeAt g root = .var k) (bound : ctx[k]? = some .dead) :
    resultAt g ctx root = none := by simp [resultAt, shape, bound]

theorem owner_not_scalar (shape : Graph.nodeAt g root = .var k) (bound : ctx[k]? = some (.owner slot)) :
    resultAt g ctx root = none := by simp [resultAt, shape, bound]

theorem ownerSlot_view : ownerSlot g ctx root = LinearCoreCallers.ownerSlot g (ownerView ctx) root := by
  unfold ownerSlot LinearCoreCallers.ownerSlot
  cases shape : Graph.nodeAt g root <;> simp
  next k =>
    simp only [ownerView, List.getElem?_map]
    cases hc : ctx[k]? with
    | none => rfl
    | some binding => cases binding <;> rfl

theorem ownerBinding_identity (shape : Graph.nodeAt g root = .var k)
    (resolved : ownerSlot g ctx root = some slot) (selected : Select owners slot x rest) :
    (LinearCoreCallers.bindings (ownerView ctx) owners)[k]? = some (some x) := by
  apply LinearCoreCallers.ownerSlot_identity shape _ selected
  simpa [ownerSlot_view] using resolved

inductive Action where
  | finish (result : Result)
  | allocate (value body : Nat)
  | call (slot callee type body : Nat)
  deriving DecidableEq, Repr

def inspect (g : Graph.Graph) (ctx : Context) (root : Nat) : Option Action := do
  match Graph.nodeAt g root with
  | .app f arg =>
    let .lam false ty body := Graph.nodeAt g f | none
    if Graph.bufferOne g ty then
      let .alloc length value := Graph.nodeAt g arg | none
      if Graph.nodeAt g length != .natural 1 then none else do
      let .integer v := Graph.nodeAt g value | none
      return .allocate v body
    else if Graph.nodeAt g ty == .i64 then
      let .app callee owner := Graph.nodeAt g arg | none
      let slot ← ownerSlot g ctx owner
      let type ← LinearCoreCallers.calleeType g callee
      return .call slot callee type body
    else none
  | _ => return .finish (← resultAt g ctx root)

inductive Program where
  | finish (result : Result)
  | allocate (value : Nat) (body : Program)
  | call (slot : Nat) (graph : Graph.Graph) (root type : Nat) (body : Program)

def forget : Program → LinearHeapPrograms.Program
  | .finish _ => .done
  | .allocate v body => .allocate v (forget body)
  | .call slot g root type body => .call slot g root type (forget body)

inductive Checked : Nat → Nat → Program → Prop where
  | finish : result.check m = true → Checked 0 m (.finish result)
  | allocate : Checked (n + 1) m body → Checked n m (.allocate v body)
  | call : slot < n → Graph.Accepted g root type → Checked (n - 1) (m + 1) body →
      Checked n m (.call slot g root type body)

def check (n m : Nat) : Program → Bool
  | .finish result => n == 0 && result.check m
  | .allocate _ body => check (n + 1) m body
  | .call slot g root type body => slot < n && (Graph.admit g root type).isSome && check (n - 1) (m + 1) body

theorem check_sound (h : check n m p = true) : Checked n m p := by
  induction p generalizing n m with
  | finish result =>
    simp only [check, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    exact .finish h
  | allocate v body ih => exact .allocate (ih h)
  | call slot g root type body ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨bound, admitted⟩, rest⟩ := h
    cases ha : Graph.admit g root type with
    | none => simp [ha] at admitted
    | some a => exact .call bound a (ih rest)

theorem Checked.forget (h : Checked n m p) : LinearHeapPrograms.Checked n (forget p) := by
  induction h with
  | finish => exact .done
  | allocate _ ih => exact .allocate ih
  | call bound a _ ih => exact .call bound a ih

inductive Represents (g : Graph.Graph) : Context → Nat → Program → Prop where
  | finish : inspect g ctx root = some (.finish result) → Represents g ctx root (.finish result)
  | allocate : inspect g ctx root = some (.allocate v body) → Represents g (fresh ctx) body p →
      Represents g ctx root (.allocate v p)
  | call : inspect g ctx root = some (.call slot callee type body) → Represents g (consumed slot ctx) body p →
      Represents g ctx root (.call slot g callee type p)

def project : Nat → Nat → Graph.Graph → Context → Nat → Option (Program × Nat)
  | 0, _, _, _, _ | _, 0, _, _, _ => none
  | fuel + 1, budget + 1, g, ctx, root => do
    match ← inspect g ctx root with
    | .finish result => pure (.finish result, budget)
    | .allocate v body =>
      let (p, rest) ← project fuel budget g (fresh ctx) body
      pure (.allocate v p, rest)
    | .call slot callee type body =>
      let (p, rest) ← project fuel budget g (consumed slot ctx) body
      pure (.call slot g callee type p, rest)

theorem project_sound (h : project fuel budget g ctx root = some (p, rest)) : Represents g ctx root p := by
  induction fuel generalizing budget ctx root p rest with
  | zero => simp [project] at h
  | succ fuel ih => cases budget with
    | zero => simp [project] at h
    | succ budget =>
      simp only [project] at h
      cases hs : inspect g ctx root with
      | none => simp [hs] at h
      | some action => cases action with
        | finish result => simp [hs] at h; obtain ⟨rfl, rfl⟩ := h; exact .finish hs
        | allocate v body =>
          cases hp : project fuel budget g (fresh ctx) body with
          | none => simp [hs, hp] at h
          | some pair => obtain ⟨q, remaining⟩ := pair; simp [hs, hp] at h; obtain ⟨rfl, rfl⟩ := h
                         exact .allocate hs (ih hp)
        | call slot callee type body =>
          cases hp : project fuel budget g (consumed slot ctx) body with
          | none => simp [hs, hp] at h
          | some pair => obtain ⟨q, remaining⟩ := pair; simp [hs, hp] at h; obtain ⟨rfl, rfl⟩ := h
                         exact .call hs (ih hp)

structure Accepted (g : Graph.Graph) (root type : Nat) where
  graph_valid : Graph.valid g = true
  root_bound : root < g.size
  type_bound : type < g.size
  result_type : Graph.nodeAt g type = .i64
  program : Program
  source : Represents g [] root program
  checked : Checked 0 0 program

def admit (g : Graph.Graph) (root type : Nat) : Option (Accepted g root type) :=
  if hv : Graph.valid g = true then
  if hr : root < g.size then
  if ht : type < g.size then
  if hi : Graph.nodeAt g type = .i64 then
    match hp : project 32 512 g [] root with
    | none => none
    | some (p, _) => if hc : check 0 0 p = true then
        some ⟨hv, hr, ht, hi, p, project_sound hp, check_sound hc⟩ else none
  else none else none else none else none

inductive Runs : Program → List Nat → List Nat → State → Nat → List HeapLeases.Event → State → Prop where
  | finish : result.eval values = some v → Runs (.finish result) [] values s v [] s
  | allocate : Runs body (s.nextObject :: owners) values (allocatedState s v) result es t →
      Runs (.allocate v body) owners values s result (.alloc s.nextObject v :: es) t
  | call : Select owners slot x rest → Graph.CoreRuns g root type s x v first middle →
      Runs body rest (v :: values) middle result second t →
      Runs (.call slot g root type body) owners values s result (first ++ second) t

theorem Runs.forget (run : Runs p owners values s v es t) : LinearHeapPrograms.Runs (forget p) owners s es t := by
  induction run with
  | finish => exact .done
  | allocate _ ih => exact .allocate ih
  | call selected first _ ih => exact .call selected first ih

theorem total (checked : Checked n m p) (ownerLength : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) : ∃ v es t, Runs p owners values s v es t := by
  induction checked generalizing owners values s with
  | finish result =>
    have : owners = [] := List.length_eq_zero_iff.mp ownerLength
    subst owners
    obtain ⟨v, hv⟩ := Result.total result scalarLength
    exact ⟨v, [], s, .finish hv⟩
  | allocate _ ih =>
    obtain ⟨v, es, t, run⟩ := ih (owners := s.nextObject :: owners) (values := values) (by simp [ownerLength]) scalarLength (step_valid valid .alloc) (allocate_owns valid owned)
    exact ⟨v, _, t, .allocate run⟩
  | call bound a _ ih =>
    obtain ⟨x, rest, selected⟩ := select_total (xs := owners) (Nat.lt_of_lt_of_eq bound ownerLength.symm)
    obtain ⟨v, first, middle, run, _⟩ := Graph.accepted_execution a valid (owned.live _ selected.member)
      (owned.leaseFree _ selected.member)
    obtain ⟨_, middleValid, middleOwns⟩ := call_owns valid owned selected a run
    have len := selected.length
    obtain ⟨result, second, t, tail⟩ := ih (owners := rest) (values := v :: values) (by omega) (by simp [scalarLength]) middleValid middleOwns
    exact ⟨result, _, t, .call selected run tail⟩

/-- The original constructor semantics retains the scalar value returned by
finish, and stores each callee result in a separate scalar environment. -/
inductive CoreRuns (g : Graph.Graph) : Context → Nat → List Nat → List Nat → State → Nat → List HeapLeases.Event → State → Prop where
  | finish : inspect g ctx root = some (.finish result) → result.eval values = some v →
      CoreRuns g ctx root owners values s v [] s
  | allocate : inspect g ctx root = some (.allocate v body) →
      CoreRuns g (fresh ctx) body (s.nextObject :: owners) values (allocatedState s v) result es t →
      CoreRuns g ctx root owners values s result (.alloc s.nextObject v :: es) t
  | call : inspect g ctx root = some (.call slot callee type body) → Select owners slot x rest →
      Graph.CoreRuns g callee type s x v first middle →
      CoreRuns g (consumed slot ctx) body rest (v :: values) middle result second t →
      CoreRuns g ctx root owners values s result (first ++ second) t

theorem Represents.execution (h : Represents g ctx root p) (run : Runs p owners values s v es t) :
    CoreRuns g ctx root owners values s v es t := by
  induction h generalizing owners values s v es t with
  | finish shape => cases run with | finish result => exact .finish shape result
  | allocate shape _ ih => cases run with | allocate run => exact .allocate shape (ih run)
  | call shape _ ih => cases run with | call selected first second => exact .call shape selected first (ih second)

theorem Represents.reflect (h : Represents g ctx root p) (checked : Checked n m p)
    (length : owners.length = n) (run : CoreRuns g ctx root owners values s v es t) : Runs p owners values s v es t := by
  induction h generalizing n m owners values s v es t with
  | finish shape =>
    cases run <;> simp_all
    cases checked
    have : owners = [] := List.length_eq_zero_iff.mp length
    subst owners
    exact .finish (by assumption)
  | allocate shape _ ih =>
    cases run <;> simp_all
    cases checked with | allocate checked => exact .allocate (ih checked (by simp_all) (by assumption))
  | call shape _ ih =>
    cases run <;> simp_all
    cases checked with | call bound a checked =>
      apply Runs.call (by assumption) (by assumption)
      apply ih checked _ (by assumption)
      have hlen := Select.length (by assumption : Select _ _ _ _)
      omega

namespace Target
inductive Program where
  | finish (result : Result)
  | allocate (value : Nat) (body : Program)
  | call (slot : Nat) (code : LeaseErasure.Code) (next : Continuation) (body : Program)

inductive Runs : Program → List Nat → List Nat → LeaseErasure.Heap → Nat → List LeaseErasure.Event → LeaseErasure.Heap → Prop where
  | finish : result.eval values = some v → Runs (.finish result) [] values h v [] h
  | allocate : Runs body (h.nextObject :: owners) values (LeaseErasure.allocate h v) result es t →
      Runs (.allocate v body) owners values h result (.alloc h.nextObject v :: es) t
  | call : Select owners slot x rest → LeaseErasure.Calls h x code k v first middle →
      Runs body rest (v :: values) middle result second t →
      Runs (.call slot code k body) owners values h result (first ++ second) t

theorem Runs.deterministic (a : Runs p owners values h v es t) (b : Runs p owners values h w fs u) :
    v = w ∧ es = fs ∧ t = u := by
  induction a generalizing w fs u with
  | finish ha => cases b with
    | finish hb => have eq := Option.some.inj (ha.symm.trans hb); subst w; exact ⟨rfl, rfl, rfl⟩
  | allocate _ ih => cases b with
    | allocate run => obtain ⟨rfl, rfl, rfl⟩ := ih run; exact ⟨rfl, rfl, rfl⟩
  | call selected first _ ih => cases b with
    | call other second tail =>
      obtain ⟨rfl, rfl⟩ := LeaseErasure.select_deterministic selected other
      obtain ⟨rfl, rfl, rfl⟩ := first.deterministic second
      obtain ⟨rfl, rfl, rfl⟩ := ih tail
      exact ⟨rfl, rfl, rfl⟩

theorem Runs.steps (run : Runs p owners values h v es t) : LeaseErasure.Steps h es t := by
  induction run with
  | finish => exact .nil
  | allocate _ ih => exact .cons .alloc ih
  | call _ first _ ih => exact LeaseErasure.steps_append first.steps ih
end Target

inductive Lowers : Program → Target.Program → Prop where
  | finish : Lowers (.finish result) (.finish result)
  | allocate : Lowers p q → Lowers (.allocate v p) (.allocate v q)
  | call (a : Graph.Accepted g root type) : Lowers p q →
      Lowers (.call slot g root type p) (.call slot (LeaseErasure.lowerReader a.reader) a.next q)

def lower : Program → Option Target.Program
  | .finish result => some (.finish result)
  | .allocate v p => (lower p).map (.allocate v)
  | .call slot g root type p => do
    let a ← Graph.admit g root type
    let q ← lower p
    pure (.call slot (LeaseErasure.lowerReader a.reader) a.next q)

theorem lower_sound (h : lower p = some q) : Lowers p q := by
  induction p generalizing q with
  | finish result => simp [lower] at h; subst q; exact .finish
  | allocate v p ih =>
    cases hp : lower p <;> simp [lower, hp] at h
    obtain ⟨rfl⟩ := h
    exact .allocate (ih hp)
  | call slot g root type p ih =>
    cases ha : Graph.admit g root type with
    | none => simp [lower, ha] at h
    | some a => cases hp : lower p with
      | none => simp [lower, ha, hp] at h
      | some q => simp [lower, ha, hp] at h; subst_vars; exact .call a (ih hp)

theorem lower_total (h : check n m p = true) : ∃ q, lower p = some q := by
  induction p generalizing n m with
  | finish result => exact ⟨.finish result, rfl⟩
  | allocate v p ih => obtain ⟨q, hq⟩ := ih h; exact ⟨.allocate v q, by simp [lower, hq]⟩
  | call slot g root type p ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨_, admitted⟩, tail⟩ := h
    obtain ⟨q, hq⟩ := ih tail
    cases ha : Graph.admit g root type with
    | none => simp [ha] at admitted
    | some a => exact ⟨.call slot (LeaseErasure.lowerReader a.reader) a.next q, by simp [lower, ha, hq]⟩

theorem program_forward (compiled : Lowers p q) (checked : Checked n m p)
    (length : owners.length = n) (valid : Valid s) (owned : Owns s owners)
    (run : Runs p owners values s v es t) :
    ∃ fs, Target.Runs q owners values (LeaseErasure.erase s) v fs (LeaseErasure.erase t) ∧
      LeaseErasure.targetTrace fs = LeaseErasure.sourceTrace es := by
  induction compiled generalizing n m owners values s v es t with
  | finish => cases run with | finish result => exact ⟨[], .finish result, rfl⟩
  | allocate compiled ih =>
    cases checked with | allocate checked =>
      cases run with | allocate run =>
        obtain ⟨fs, target, trace⟩ := ih checked (by simp [length]) (step_valid valid .alloc) (allocate_owns valid owned) run
        exact ⟨_, .allocate target, congrArg (LeaseErasure.Observation.alloc s.nextObject _ :: ·) trace⟩
  | @call g root type slot p q a compiled ih =>
    cases checked with | call bound admitted checked =>
      cases run with | call selected first second =>
        obtain ⟨_, middleValid, middleOwns⟩ := call_owns valid owned selected a first
        obtain ⟨xs, hx, tx⟩ := LeaseErasure.call_forward_effects (Graph.accepted_reflect a first) (owned.live _ selected.member)
        have len := selected.length
        obtain ⟨ys, hy, ty⟩ := ih checked (by omega) middleValid middleOwns second
        exact ⟨_, .call selected hx hy, by simpa [LeaseErasure.targetTrace, LeaseErasure.sourceTrace,
          List.map_append, List.filterMap_append] using LeaseErasure.append_eq tx ty⟩

theorem admitted_check (h : admit g root type = some a) : check 0 0 a.program = true := by
  unfold admit at h
  repeat' first | split at h | contradiction
  all_goals simp_all
  cases h
  assumption

theorem admitted_execution (h : admit g root type = some a) :
    ∃ q v fs heap, lower a.program = some q ∧ Target.Runs q [] [] (LeaseErasure.erase empty) v fs heap := by
  obtain ⟨q, compiled⟩ := lower_total (admitted_check h)
  obtain ⟨v, es, s, source⟩ := total (owners := []) (values := []) a.checked rfl rfl empty_valid empty_owns
  obtain ⟨fs, target, _⟩ := program_forward (lower_sound compiled) a.checked rfl empty_valid empty_owns source
  exact ⟨q, v, fs, LeaseErasure.erase s, compiled, target⟩

theorem accepted_source_total (a : Accepted g root type) :
    ∃ v es s, CoreRuns g [] root [] [] empty v es s := by
  obtain ⟨v, es, s, run⟩ := total (owners := []) (values := []) a.checked rfl rfl empty_valid empty_owns
  exact ⟨v, es, s, a.source.execution run⟩

/-- Every original constructor run, not only the totality witness, preserves
its final scalar through compilation. -/
theorem accepted_forward (a : Accepted g root type) (compiled : lower a.program = some q)
    (run : CoreRuns g [] root [] [] empty v es s) :
    ∃ fs, Target.Runs q [] [] (LeaseErasure.erase empty) v fs (LeaseErasure.erase s) ∧
      LeaseErasure.targetTrace fs = LeaseErasure.sourceTrace es :=
  program_forward (lower_sound compiled) a.checked rfl empty_valid empty_owns
    (a.source.reflect a.checked rfl run)

theorem accepted_source_result_unique (a : Accepted g root type) (compiled : lower a.program = some q)
    (first : CoreRuns g [] root [] [] empty v es s) (second : CoreRuns g [] root [] [] empty w fs t) : v = w := by
  obtain ⟨xs, hx, _⟩ := accepted_forward a compiled first
  obtain ⟨ys, hy, _⟩ := accepted_forward a compiled second
  exact (hx.deterministic hy).1

/-- Every target run has an original constructor execution with the same final
scalar, exact common effects and erased heap, not merely a chosen forward run. -/
theorem accepted_target_reflect (a : Accepted g root type) (compiled : lower a.program = some q)
    (target : Target.Runs q [] [] (LeaseErasure.erase empty) v fs heap) :
    ∃ es s, CoreRuns g [] root [] [] empty v es s ∧ LeaseErasure.erase s = heap ∧
      LeaseErasure.sourceTrace es = LeaseErasure.targetTrace fs := by
  obtain ⟨w, es, s, source⟩ := total (owners := []) (values := []) a.checked rfl rfl empty_valid empty_owns
  obtain ⟨xs, erased, trace⟩ := program_forward (lower_sound compiled) a.checked rfl empty_valid empty_owns source
  obtain ⟨rfl, rfl, eq⟩ := erased.deterministic target
  exact ⟨es, s, a.source.execution source, eq, trace.symm⟩

theorem accepted_target_safe (a : Accepted g root type) (compiled : lower a.program = some q)
    (target : Target.Runs q [] [] (LeaseErasure.erase empty) v fs heap) :
    LeaseErasure.Steps (LeaseErasure.erase empty) fs heap ∧ (∀ x, heap.live x = false) ∧
    ∀ x ∈ LeaseErasure.observedAllocations (LeaseErasure.targetTrace fs),
      (LeaseErasure.observedReleases (LeaseErasure.targetTrace fs)).count x = 1 := by
  obtain ⟨es, s, source, rfl, trace⟩ := accepted_target_reflect a compiled target
  have run := (a.source.reflect a.checked rfl source).forget
  refine ⟨target.steps, closed_heap_empty a.checked.forget run, ?_⟩
  rw [← trace, LeaseErasure.source_allocations, LeaseErasure.source_releases]
  intro x member
  exact ((closed_safety a.checked.forget run).2.2.2 x member).1

end Jihoo.ScalarCoreCallers
