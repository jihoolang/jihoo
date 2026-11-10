import Jihoo.LinearHeapPrograms

/-! Literal finite callers over original Core constructor IDs. Lexical names
retain tombstones after consumption; the live capability list compacts separately.
The exporter remains trusted. This is a specified restricted constructor semantics,
not a proof of the native evaluator or general caller elaboration. -/
namespace Jihoo.LinearCoreCallers
open HeapLeases ScopedLend LinearHeapPrograms
abbrev Context := List (Option Nat)

def fresh (ctx : Context) : Context := some 0 :: ctx.map (Option.map (· + 1))
def consumed (slot : Nat) (ctx : Context) : Context := ctx.map fun entry => do
  let k ← entry
  if k = slot then none else some (if slot < k then k - 1 else k)

def ownerSlot (g : Graph.Graph) (ctx : Context) (root : Nat) : Option Nat := do
  let .var k := Graph.nodeAt g root | none
  (ctx[k]?).join

/-- Concrete lexical binding interpretation, distinct from compact ownership slots. -/
def bindings (ctx : Context) (owners : List Nat) : List (Option Nat) :=
  ctx.map fun slot => slot.bind fun k => owners[k]?

theorem fresh_bindings : bindings (fresh ctx) (x :: owners) = some x :: bindings ctx owners := by
  simp only [bindings, fresh, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro entry _
  cases entry <;> rfl

theorem Select.lookup_selected (h : Select owners slot x rest) : owners[slot]? = some x := by
  induction h with
  | here => rfl
  | there _ ih => exact ih

theorem Select.lookup_other (h : Select owners slot x rest) (different : k ≠ slot) :
    rest[if slot < k then k - 1 else k]? = owners[k]? := by
  induction h generalizing k with
  | here => cases k with
    | zero => contradiction
    | succ k => simp
  | @there xs slot x rest y h ih =>
    cases k with
    | zero => simp
    | succ k =>
      have ne : k ≠ slot := by omega
      have old := ih ne
      by_cases lt : slot < k
      · have pos : 0 < k := by omega
        simp only [show slot + 1 < k + 1 from by omega, ↓reduceIte,
          Nat.add_sub_cancel]
        cases k with
        | zero => omega
        | succ k => simpa [lt] using old
      · simpa [lt, show ¬slot + 1 < k + 1 from by omega] using old

/-- Consumption clears precisely those lexical entries naming the selected
slot. Every other lexical entry keeps the same concrete allocation identity. -/
theorem consumed_bindings (h : Select owners slot x rest) :
    bindings (consumed slot ctx) rest =
      ctx.map (fun entry => if entry = some slot then none else entry.bind (fun k => owners[k]?)) := by
  simp only [bindings, consumed, List.map_map]
  apply List.map_congr_left
  intro entry _
  cases entry with
  | none => rfl
  | some k =>
    by_cases eq : k = slot
    · subst k; simp
    · simp [eq, Select.lookup_other h eq]

/-- A resolved lexical variable names exactly the allocation selected for
consumption, rather than merely a numerically equal compact slot. -/
theorem ownerSlot_identity (shape : Graph.nodeAt g root = .var k)
    (resolved : ownerSlot g ctx root = some slot)
    (selected : Select owners slot x rest) :
    (bindings ctx owners)[k]? = some (some x) := by
  simp only [ownerSlot, shape] at resolved
  cases hc : ctx[k]? with
  | none => simp [hc] at resolved
  | some entry =>
    cases entry with
    | none => simp [hc] at resolved
    | some value =>
      simp [hc] at resolved
      subst value
      simp [bindings, List.getElem?_map, hc, Select.lookup_selected selected]

/-- Candidate types are rechecked against the original callee graph, never
accepted from an unvalidated function-type association. -/
def calleeType (g : Graph.Graph) (root : Nat) : Option Nat := do
  let type ← (List.range g.size).find? fun ty => match Graph.nodeAt g ty with
    | .pi false domain result => Graph.bufferOne g domain && Graph.nodeAt g result == .i64
    | _ => false
  if (Graph.admit g root type).isSome then some type else none

inductive Action where
  | finish (value : Nat)
  | allocate (value body : Nat)
  | call (slot callee type body : Nat)
  deriving DecidableEq, Repr

def inspect (g : Graph.Graph) (ctx : Context) (root : Nat) : Option Action := do
  match Graph.nodeAt g root with
  | .integer v => return .finish v
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
      let type ← calleeType g callee
      return .call slot callee type body
    else none
  | _ => none

inductive Represents (g : Graph.Graph) : Context → Nat → Program → Prop where
  | finish : inspect g ctx root = some (.finish v) → Represents g ctx root .done
  | allocate : inspect g ctx root = some (.allocate v body) →
      Represents g (fresh ctx) body p → Represents g ctx root (.allocate v p)
  | call : inspect g ctx root = some (.call slot callee type body) →
      Represents g (none :: consumed slot ctx) body p →
      Represents g ctx root (.call slot g callee type p)

/-- A single-path caller still has an explicit shared budget, independent of
node IDs and DAG sharing. No partial program survives failed recognition. -/
def project : Nat → Nat → Graph.Graph → Context → Nat → Option (Program × Nat)
  | 0, _, _, _, _ | _, 0, _, _, _ => none
  | fuel + 1, budget + 1, g, ctx, root => do
    match ← inspect g ctx root with
    | .finish _ => return (.done, budget)
    | .allocate v body =>
      let (p, rest) ← project fuel budget g (fresh ctx) body
      return (.allocate v p, rest)
    | .call slot callee type body =>
      let (p, rest) ← project fuel budget g (none :: consumed slot ctx) body
      return (.call slot g callee type p, rest)

theorem project_sound (h : project fuel budget g ctx root = some (p, rest)) :
    Represents g ctx root p := by
  induction fuel generalizing budget ctx root p rest with
  | zero => simp [project] at h
  | succ fuel ih =>
    cases budget with
    | zero => simp [project] at h
    | succ budget =>
      simp only [project] at h
      cases hs : inspect g ctx root with
      | none => simp [hs] at h
      | some action =>
        cases action with
        | finish v => simp [hs] at h; obtain ⟨rfl, rfl⟩ := h; exact .finish hs
        | allocate v body =>
          cases hp : project fuel budget g (fresh ctx) body with
          | none => simp [hs, hp] at h
          | some pair =>
            obtain ⟨q, remaining⟩ := pair
            simp [hs, hp] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .allocate hs (ih hp)
        | call slot callee type body =>
          cases hp : project fuel budget g (none :: consumed slot ctx) body with
          | none => simp [hs, hp] at h
          | some pair =>
            obtain ⟨q, remaining⟩ := pair
            simp [hs, hp] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .call hs (ih hp)

structure Accepted (g : Graph.Graph) (root type : Nat) where
  graph_valid : Graph.valid g = true
  root_bound : root < g.size
  type_bound : type < g.size
  result_type : Graph.nodeAt g type = .i64
  program : Program
  source : Represents g [] root program
  checked : Checked 0 program

def admit (g : Graph.Graph) (root type : Nat) : Option (Accepted g root type) :=
  if hv : Graph.valid g = true then
  if hr : root < g.size then
  if ht : type < g.size then
  if hi : Graph.nodeAt g type = .i64 then
    match hp : project 32 512 g [] root with
    | none => none
    | some (p, _) => if hc : check 0 p = true then
        some ⟨hv, hr, ht, hi, p, project_sound hp, check_sound hc⟩ else none
  else none else none else none else none

/-- Constructor execution uses the original lexical lookup and literal
allocation. Finish does not assume an empty resource list; checked recognition
must prove it, rather than baking no-leak into the runtime rule. -/
inductive CoreRuns (g : Graph.Graph) : Context → Nat → List Nat → State → List Event → State → Prop where
  | finish : inspect g ctx root = some (.finish v) → CoreRuns g ctx root owners s [] s
  | allocate : inspect g ctx root = some (.allocate v body) →
      CoreRuns g (fresh ctx) body (s.nextObject :: owners) (allocatedState s v) es t →
      CoreRuns g ctx root owners s (.alloc s.nextObject v :: es) t
  | call : inspect g ctx root = some (.call slot callee type body) →
      Select owners slot x rest → Graph.CoreRuns g callee type s x v first middle →
      CoreRuns g (none :: consumed slot ctx) body rest middle second t →
      CoreRuns g ctx root owners s (first ++ second) t

theorem Represents.execution (h : Represents g ctx root p)
    (run : Runs p owners s es t) : CoreRuns g ctx root owners s es t := by
  induction h generalizing owners s es t with
  | finish shape => cases run; exact .finish shape
  | allocate shape _ ih => cases run with
    | allocate run => exact .allocate shape (ih run)
  | call shape _ ih => cases run with
    | call selected first second => exact .call shape selected first (ih second)

theorem Represents.reflect (h : Represents g ctx root p) (checked : Checked n p)
    (length : owners.length = n) (run : CoreRuns g ctx root owners s es t) :
    Runs p owners s es t := by
  induction h generalizing n owners s es t with
  | finish shape =>
    cases run <;> simp_all
    cases checked
    have : owners = [] := List.length_eq_zero_iff.mp length
    subst owners
    exact .done
  | allocate shape _ ih =>
    cases run <;> simp_all
    cases checked with
    | allocate check => exact .allocate (ih check (by simp_all) (by assumption))
  | call shape _ ih =>
    cases run <;> simp_all
    cases checked with
    | call bound admitted check =>
      apply Runs.call (by assumption) (by assumption)
      apply ih check _ (by assumption)
      have hlen := Select.length (by assumption : Select _ _ _ _)
      omega

theorem accepted_total (a : Accepted g root type) :
    ∃ es t, CoreRuns g [] root [] empty es t := by
  obtain ⟨es, t, run⟩ := closed_total a.checked
  exact ⟨es, t, a.source.execution run⟩

theorem accepted_all_runs (a : Accepted g root type)
    (run : CoreRuns g [] root [] empty es t) :
    Steps empty es t ∧ Valid t ∧ t.lease = empty.lease ∧
    (∀ x ∈ allocations es, (released es).count x = 1 ∧ t.live x = false) ∧
    (∀ x, t.live x = false) := by
  have projected := a.source.reflect a.checked rfl run
  have safe := closed_safety a.checked projected
  exact ⟨safe.1, safe.2.1, safe.2.2.1, safe.2.2.2, closed_heap_empty a.checked projected⟩

end Jihoo.LinearCoreCallers
