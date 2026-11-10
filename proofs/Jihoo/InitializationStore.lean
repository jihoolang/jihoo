import Jihoo.Initialization
import Jihoo.CallEntry

/-! Concrete partial local stores for checked initialization graphs.
Operations may trap or return a malformed result vector. Neither is silently
converted into success; only the uninitialized-local fault is excluded here.
Heap state, typed values and native instruction refinement are not modeled. -/
namespace Jihoo.Initialization.Store
open Jihoo.Initialization

abbrev Memory (α : Type) := Nat → Option α

def Covers (facts : Facts) (memory : Memory α) : Prop :=
  ∀ x, x ∈ facts → ∃ value, memory x = some value

def write (memory : Memory α) (slot : Nat) (value : α) : Memory α :=
  fun i => if i = slot then some value else memory i

def readMany (memory : Memory α) : Facts → Option (List α)
  | [] => some []
  | i :: rest => do
      let value ← memory i
      let values ← readMany memory rest
      pure (value :: values)

def writeMany : Facts → List α → Memory α → Option (Memory α)
  | [], [], memory => some memory
  | i :: rest, value :: values, memory => writeMany rest values (write memory i value)
  | _, _, _ => none

inductive Outcome (α : Type) where
  | normal (memory : Memory α)
  | uninitialized
  | trap
  | badResult

/-- Operation choices are indexed within a block. Different block executions
may choose different operations, so heap effects/nondeterminism are not assumed
pure merely because two instructions have the same read/write footprint. -/
abbrev Operation (α : Type) := Nat → Action → List α → Option (List α)

def execute (operation : Operation α) : List Action → Memory α → Outcome α
  | [], memory => .normal memory
  | action :: rest, memory =>
      match readMany memory action.reads with
      | none => .uninitialized
      | some inputs => match operation 0 action inputs with
        | none => .trap
        | some outputs => match writeMany action.writes outputs memory with
          | none => .badResult
          | some next => execute (fun i => operation (i + 1)) rest next

def ResultCovers (facts : Facts) : Outcome α → Prop
  | .normal memory => Covers facts memory
  | .uninitialized => False
  | .trap | .badResult => True

 theorem covers_sub (sub : Sub a b) (covered : Covers b memory) : Covers a memory :=
  fun x hx => covered x (sub x hx)

 theorem covers_write (covered : Covers facts memory) :
    Covers (slot :: facts) (write memory slot value) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨value, by simp [write]⟩
  · by_cases same : x = slot
    · exact ⟨value, by simp [write, same]⟩
    · obtain ⟨v, hv⟩ := covered x hx
      exact ⟨v, by simp [write, same, hv]⟩

 theorem readMany_exists (covered : Covers facts memory) :
    ∃ values, readMany memory facts = some values := by
  induction facts with
  | nil => exact ⟨[], rfl⟩
  | cons x rest ih =>
      obtain ⟨v, hv⟩ := covered x (by simp)
      obtain ⟨vs, hvs⟩ := ih (fun i hi => covered i (by simp [hi]))
      exact ⟨v :: vs, by simp [readMany, hv, hvs]⟩

/-- A normal result writes every destination. Existing initialized locals remain
initialized even when a destination is repeated or overwrites an old value. -/
theorem writeMany_covers (h : writeMany writes values memory = some next)
    (covered : Covers facts memory) : Covers (writes ++ facts) next := by
  induction writes generalizing values memory facts with
  | nil =>
      cases values with
      | nil =>
          simp only [writeMany, Option.some.injEq] at h
          subst next
          exact covered
      | cons => simp [writeMany] at h
  | cons slot rest ih =>
      cases values with
      | nil => simp [writeMany] at h
      | cons value values =>
          have tail := ih (facts := slot :: facts) h (covers_write covered)
          intro x hx
          apply tail x
          simp only [List.mem_append, List.mem_cons] at hx ⊢
          rcases hx with (hs | hr) | hf
          · exact Or.inr (Or.inl hs)
          · exact Or.inl hr
          · exact Or.inr (Or.inr hf)

/-- Abstract success entails no uninitialized-local fault for arbitrary concrete
values and arbitrary operation results. Trap/bad-result outcomes remain possible. -/
theorem execution_sound (h : run actions facts = some out)
    (covered : Covers facts memory) : ResultCovers out (execute operation actions memory) := by
  induction actions generalizing facts out memory operation with
  | nil =>
      simp [run] at h
      subst out
      exact covered
  | cons action rest ih =>
      simp only [run] at h
      split at h
      next hr =>
        obtain ⟨inputs, hi⟩ := readMany_exists (covers_sub (subset_sound hr) covered)
        simp only [execute, hi]
        cases ho : operation 0 action inputs with
        | none => trivial
        | some outputs =>
            change ResultCovers out (match writeMany action.writes outputs memory with
              | none => .badResult | some next => execute (fun i => operation (i + 1)) rest next)
            cases hw : writeMany action.writes outputs memory with
            | none => trivial
            | some next => exact ih h (writeMany_covers hw covered)
      next => contradiction

theorem normal_result_covered (h : run actions facts = some out)
    (covered : Covers facts memory)
    (executed : execute operation actions memory = .normal result) : Covers out result := by
  have hs := execution_sound (operation := operation) h covered
  rwa [executed] at hs

/-- Concrete CFG execution includes only normally completed block transitions.
It does not require initialization-checker acceptance or assume safe reads. -/
inductive ValueReach (g : Graph) (entry : Memory α) :
    Nat → Memory α → Prop where
  | entry : ValueReach g entry 0 entry
  | step : ValueReach g entry pc memory → (pc, b) ∈ g → next ∈ b.successors →
      execute operation b.actions memory = .normal result →
      ValueReach g entry next result

 theorem reachable_store_covered (checked : check g initial cert = true)
    (entry : Covers initial memory₀) (reach : ValueReach g memory₀ pc memory) :
    ∃ facts, cert pc = some facts ∧ Covers facts memory := by
  induction reach with
  | entry =>
      obtain ⟨facts, hc, hs⟩ := check_entry checked
      exact ⟨facts, hc, covers_sub hs entry⟩
  | step prior member successor executed ih =>
      obtain ⟨facts, hc, cover⟩ := ih
      obtain ⟨out, hr, edges⟩ := check_block checked member hc
      have result := normal_result_covered hr cover executed
      obtain ⟨incoming, hn, hs⟩ := edges _ successor
      exact ⟨incoming, hn, covers_sub hs result⟩

/-- Main concrete endpoint. Reachability does not preclude a failing next block;
checker acceptance proves that its failure cannot be an uninitialized read. -/
theorem accepted_no_uninitialized (checked : check g initial cert = true)
    (entry : Covers initial memory₀) (reach : ValueReach g memory₀ pc memory)
    (member : (pc, b) ∈ g) : execute operation b.actions memory ≠ .uninitialized := by
  obtain ⟨facts, hc, cover⟩ := reachable_store_covered checked entry reach
  obtain ⟨out, hr, _⟩ := check_block checked member hc
  have result := execution_sound (operation := operation) hr cover
  intro failed
  rw [failed] at result
  exact result

/-- Initialize exactly the designated entry locals with arbitrary values. -/
def seed (initial : Facts) (values : Nat → α) : Memory α :=
  fun i => if i ∈ initial then some (values i) else none

theorem seed_covers : Covers initial (seed initial values) := by
  intro i hi
  exact ⟨values i, by simp [seed, hi]⟩

/-- Concrete by-value call entry: return at zero, positional parameters at 1..n,
and absent locals elsewhere. This models separate local cells, not disjoint heap
objects: copied pointer values can still alias heap storage. -/
def enter (result : Option α) (arguments : List α) : Memory α
  | 0 => result
  | i + 1 => arguments[i]?

def entryFacts (result : Option α) (arguments : List α) : Facts :=
  (if result.isSome then [0] else []) ++ List.range' 1 arguments.length

theorem enter_parameter : enter result arguments (i + 1) = arguments[i]? := rfl

theorem enter_covers : Covers (entryFacts result arguments) (enter result arguments) := by
  intro i hi
  simp only [entryFacts, List.mem_append] at hi
  rcases hi with hr | ha
  · cases result with
    | none => simp at hr
    | some value =>
        simp at hr
        subst i
        exact ⟨value, rfl⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp ha
    refine ⟨arguments[k], ?_⟩
    simp [enter, Nat.add_comm, hk]

/-- The prior capture-numbering model and this concrete store agree on every
positive local, including the recursion node and its packed captures. -/
theorem call_entry_lookup :
    enter result (node :: LoweringEnvironment.pack caller) (i + 1) =
      (CallEntry.entry [reserved] node caller)[i + 1]? := by
  simp [enter, CallEntry.entry]

theorem accepted_frame_no_uninitialized
    (checked : check g (entryFacts result arguments) cert = true)
    (reach : ValueReach g (enter result arguments) pc memory)
    (member : (pc, b) ∈ g) : execute operation b.actions memory ≠ .uninitialized :=
  accepted_no_uninitialized checked enter_covers reach member

end Jihoo.Initialization.Store
