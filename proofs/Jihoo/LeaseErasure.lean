import Jihoo.LinearCoreCallers

/-! Erasure into an independent lease-free abstract pointer heap. This stage
models Lend/Borrow's pointer behavior, not native MIR blocks or raw addresses.
Successful fresh allocation and mathematical scalar payloads remain explicit. -/
namespace Jihoo.LeaseErasure
open HeapLeases ScopedLend LinearHeapPrograms

structure Heap where
  nextObject : Nat
  live : Nat → Bool
  payload : Nat → Nat

def erase (s : State) : Heap := ⟨s.nextObject, s.live, s.payload⟩
def allocate (h : Heap) (v : Nat) : Heap :=
  ⟨h.nextObject + 1, put h.live h.nextObject true, put h.payload h.nextObject v⟩
def finish (h : Heap) (x v : Nat) : Continuation → Heap
  | .free | .freeOriginal => { h with live := put h.live x false }
  | .storeResult => { h with live := put h.live x false, payload := put h.payload x v }

theorem erase_allocate : erase (allocatedState s v) = allocate (erase s) v := rfl
theorem erase_finish : erase (finalState s x v k) = finish (erase s) x v k := by cases k <;> rfl
theorem erase_open : erase (opened s x) = erase s := rfl

inductive Event where
  | alloc (object value : Nat)
  | read (object value : Nat)
  | write (object value : Nat)
  | free (object : Nat)
  deriving DecidableEq, Repr

inductive Step : Heap → Event → Heap → Prop where
  | alloc : Step h (.alloc h.nextObject v) (allocate h v)
  | read : h.live x = true → Step h (.read x (h.payload x)) h
  | write : h.live x = true → Step h (.write x v) { h with payload := put h.payload x v }
  | free : h.live x = true → Step h (.free x) { h with live := put h.live x false }

inductive Steps : Heap → List Event → Heap → Prop where
  | nil : Steps h [] h
  | cons : Step h e m → Steps m es t → Steps h (e :: es) t

theorem steps_append (a : Steps h xs m) (b : Steps m ys t) : Steps h (xs ++ ys) t := by
  induction a with
  | nil => exact b
  | cons first _ ih => exact .cons first (ih b)

inductive Code where
  | scalar (value : Nat)
  | load
  | seq (first second : Code)
  | branch (condition : Bool) (yes no : Code)
  deriving DecidableEq, Repr

def lowerReader : Reader → Code
  | .scalar v => .scalar v
  | .read _ => .load
  | .seq a b => .seq (lowerReader a) (lowerReader b)
  | .branch c a b => .branch c (lowerReader a) (lowerReader b)

/-- The target reads its direct allocation identity and checks liveness, not
source leases or any evidence of a source execution. -/
inductive Reads (h : Heap) (owner : Nat) : Code → Nat → List Event → Prop where
  | scalar : Reads h owner (.scalar v) v []
  | load : h.live owner = true → Reads h owner .load (h.payload owner) [.read owner (h.payload owner)]
  | seq : Reads h owner a v xs → Reads h owner b w ys → Reads h owner (.seq a b) w (xs ++ ys)
  | yes : Reads h owner a v es → Reads h owner (.branch true a b) v es
  | no : Reads h owner b v es → Reads h owner (.branch false a b) v es

theorem Reads.deterministic (a : Reads h x code v es) (b : Reads h x code w fs) : v = w ∧ es = fs := by
  induction a generalizing w fs with
  | scalar => cases b; exact ⟨rfl, rfl⟩
  | load => cases b; exact ⟨rfl, rfl⟩
  | seq _ _ ia ib => cases b with
    | seq first second => obtain ⟨rfl, rfl⟩ := ia first; obtain ⟨rfl, rfl⟩ := ib second; exact ⟨rfl, rfl⟩
  | yes _ ih => cases b with | yes run => exact ih run
  | no _ ih => cases b with | no run => exact ih run

theorem Reads.steps (run : Reads h x code v es) : Steps h es h := by
  induction run with
  | scalar => exact .nil
  | load live => exact .cons (.read live) .nil
  | seq _ _ ia ib => exact steps_append ia ib
  | yes _ ih | no _ ih => exact ih

/-- A scoped reader's read events have a known owner. Erasure drops token IDs,
but retains the actual owner and observed value in every target event. -/
def readerEvents (owner : Nat) (events : List HeapLeases.Event) : List Event :=
  events.filterMap fun e => match e with | .read _ v => some (.read owner v) | _ => none

theorem reader_forward (run : ScopedLend.Reads (opened s x) [s.nextLease] r v es)
    (live : s.live x = true) : Reads (erase s) x (lowerReader r) v (readerEvents x es) := by
  induction run with
  | scalar => exact .scalar
  | @read k token object slot lease =>
    have token_eq : token = s.nextLease := by
      cases k with
      | zero => simpa using slot.symm
      | succ k => simp at slot
    subst token
    have eq : object = x := by simpa [opened, put] using lease.symm
    subst object
    exact .load live
  | seq _ _ ia ib => simpa [lowerReader, readerEvents, List.filterMap_append] using Reads.seq ia ib
  | yes _ ih => exact .yes ih
  | no _ ih => exact .no ih

def continuationEvents (x v : Nat) : Continuation → List Event
  | .free | .freeOriginal => [.free x]
  | .storeResult => [.write x v, .free x]

theorem finish_steps (live : h.live x = true) :
    Steps h (continuationEvents x v k) (finish h x v k) := by
  cases k with
  | free | freeOriginal => exact .cons (.free live) .nil
  | storeResult => exact .cons (.write live) (.cons (.free live) .nil)

inductive Calls (h : Heap) (x : Nat) (code : Code) (k : Continuation) : Nat → List Event → Heap → Prop where
  | run : h.live x = true → Reads h x code v es →
      Calls h x code k v (es ++ continuationEvents x v k) (finish h x v k)

theorem Calls.steps (run : Calls h x code k v es t) : Steps h es t := by
  cases run with | run live reads => exact steps_append reads.steps (finish_steps live)

theorem Calls.deterministic (a : Calls h x code k v es t) (b : Calls h x code k w fs u) :
    v = w ∧ es = fs ∧ t = u := by
  cases a with
  | run live ar => cases b with
    | run _ br => obtain ⟨rfl, rfl⟩ := ar.deterministic br; exact ⟨rfl, rfl, rfl⟩

theorem call_forward (run : ScopedLend.Executes s x r k v es t) (live : s.live x = true) :
    ∃ targetEvents, Calls (erase s) x (lowerReader r) k v targetEvents (erase t) := by
  cases run with
  | @lend events reads =>
    refine ⟨readerEvents x events ++ continuationEvents x v k, ?_⟩
    rw [erase_finish]
    exact .run live (reader_forward reads live)

/-- Common observations retain allocation/write/free identities and scalar
read values/order. The direct read identity is separately fixed by target Reads. -/
inductive Observation where
  | alloc (object value : Nat)
  | read (value : Nat)
  | write (object value : Nat)
  | free (object : Nat)
  deriving DecidableEq, Repr

def sourceTrace (events : List HeapLeases.Event) : List Observation :=
  events.filterMap fun e => match e with
  | .alloc x v => some (.alloc x v)
  | .read _ v => some (.read v)
  | .write x v => some (.write x v)
  | .free x => some (.free x)
  | .beginLease _ _ | .close _ => none

def targetTrace (events : List Event) : List Observation :=
  events.map fun e => match e with
  | .alloc x v => .alloc x v
  | .read _ v => .read v
  | .write x v => .write x v
  | .free x => .free x

theorem append_eq {xs ys us vs : List α} (a : xs = ys) (b : us = vs) : xs ++ us = ys ++ vs := by rw [a, b]

theorem reader_trace (read : ScopedLend.Reads s env r v es) :
    targetTrace (readerEvents x es) = sourceTrace es := by
  induction read with
  | scalar | read => rfl
  | seq _ _ ia ib => simpa [readerEvents, targetTrace, sourceTrace, List.filterMap_append, List.map_append] using append_eq ia ib
  | yes _ ih | no _ ih => exact ih

theorem continuation_trace : targetTrace (continuationEvents x v k) =
    sourceTrace (ScopedLend.continuationEvents x v k) := by cases k <;> rfl

theorem call_forward_effects (run : ScopedLend.Executes s x r k v es t) (live : s.live x = true) :
    ∃ fs, Calls (erase s) x (lowerReader r) k v fs (erase t) ∧ targetTrace fs = sourceTrace es := by
  cases run with
  | @lend events reads =>
    refine ⟨readerEvents x events ++ continuationEvents x v k, ?_, ?_⟩
    · rw [erase_finish]; exact .run live (reader_forward reads live)
    · simp only [targetTrace, sourceTrace, List.map_append, List.filterMap_append,
        List.filterMap_cons, List.filterMap_nil, List.nil_append, List.append_nil]
      exact append_eq (reader_trace reads) continuation_trace

inductive Program where
  | done
  | allocate (value : Nat) (body : Program)
  | call (slot : Nat) (code : Code) (next : Continuation) (body : Program)

inductive Lowers : LinearHeapPrograms.Program → Program → Prop where
  | done : Lowers .done .done
  | allocate : Lowers p q → Lowers (.allocate v p) (.allocate v q)
  | call (a : Graph.Accepted graph root type) : Lowers p q →
      Lowers (.call slot graph root type p) (.call slot (lowerReader a.reader) a.next q)

def lower : LinearHeapPrograms.Program → Option Program
  | .done => some .done
  | .allocate v p => (lower p).map (.allocate v)
  | .call slot graph root type p => do
    let a ← Graph.admit graph root type
    let q ← lower p
    pure (.call slot (lowerReader a.reader) a.next q)

theorem lower_sound (h : lower p = some q) : Lowers p q := by
  induction p generalizing q with
  | done => simp [lower] at h; subst q; exact .done
  | allocate v p ih =>
    cases hp : lower p <;> simp [lower, hp] at h
    obtain ⟨rfl⟩ := h
    exact .allocate (ih hp)
  | call slot graph root type p ih =>
    cases ha : Graph.admit graph root type with
    | none => simp [lower, ha] at h
    | some a => cases hp : lower p with
      | none => simp [lower, ha, hp] at h
      | some q => simp [lower, ha, hp] at h; subst_vars; exact .call a (ih hp)

theorem lower_total (h : check n p = true) : ∃ q, lower p = some q := by
  induction p generalizing n with
  | done => exact ⟨.done, rfl⟩
  | allocate v p ih =>
    obtain ⟨q, hq⟩ := ih h
    exact ⟨.allocate v q, by simp [lower, hq]⟩
  | call slot graph root type p ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨_, admitted⟩, tail⟩ := h
    obtain ⟨q, hq⟩ := ih tail
    cases ha : Graph.admit graph root type with
    | none => simp [ha] at admitted
    | some a => exact ⟨.call slot (lowerReader a.reader) a.next q, by simp [lower, ha, hq]⟩

theorem admitted_check (h : LinearCoreCallers.admit g root type = some a) : check 0 a.program = true := by
  unfold LinearCoreCallers.admit at h
  repeat' first | split at h | contradiction
  all_goals simp_all
  cases h
  assumption

theorem admitted_lower_total (h : LinearCoreCallers.admit g root type = some a) :
    ∃ q, lower a.program = some q := lower_total (admitted_check h)

inductive Runs : Program → List Nat → Heap → List Event → Heap → Prop where
  | done : Runs .done [] h [] h
  | allocate : Runs body (h.nextObject :: owners) (allocate h v) es t →
      Runs (.allocate v body) owners h (.alloc h.nextObject v :: es) t
  | call : Select owners slot x rest → Calls h x code k v first middle →
      Runs body rest middle second t → Runs (.call slot code k body) owners h (first ++ second) t

theorem select_deterministic (a : Select owners slot x rest) (b : Select owners slot y other) :
    x = y ∧ rest = other := by
  induction a generalizing y other with
  | here => cases b; exact ⟨rfl, rfl⟩
  | there _ ih => cases b with
    | there h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩

theorem Runs.deterministic (a : Runs p owners h es t) (b : Runs p owners h fs u) : es = fs ∧ t = u := by
  induction a generalizing fs u with
  | done => cases b; exact ⟨rfl, rfl⟩
  | allocate _ ih => cases b with
    | allocate run => obtain ⟨rfl, rfl⟩ := ih run; exact ⟨rfl, rfl⟩
  | call selected first _ ih => cases b with
    | call other second tail =>
      obtain ⟨rfl, rfl⟩ := select_deterministic selected other
      obtain ⟨rfl, rfl, rfl⟩ := first.deterministic second
      obtain ⟨rfl, rfl⟩ := ih tail
      exact ⟨rfl, rfl⟩

theorem Runs.steps (run : Runs p owners h es t) : Steps h es t := by
  induction run with
  | done => exact .nil
  | allocate _ ih => exact .cons .alloc ih
  | call _ first _ ih => exact steps_append first.steps ih

/-- Forward erasure is value preserving at each callee and preserves all final
heap payloads/identities. The target has no lease state or token instructions. -/
theorem program_forward (compiled : Lowers p q) (checked : Checked n p)
    (length : owners.length = n) (valid : Valid s) (owned : Owns s owners)
    (run : LinearHeapPrograms.Runs p owners s es t) :
    ∃ fs, Runs q owners (erase s) fs (erase t) ∧ targetTrace fs = sourceTrace es := by
  induction compiled generalizing n owners s es t with
  | done => cases run; exact ⟨[], .done, rfl⟩
  | allocate compiled ih =>
    cases checked with | allocate checked =>
      cases run with | allocate run =>
        obtain ⟨fs, h, trace⟩ := ih checked (by simp [length]) (step_valid valid .alloc) (allocate_owns valid owned) run
        exact ⟨_, .allocate h, congrArg (Observation.alloc s.nextObject _ :: ·) trace⟩
  | @call graph root type slot p q a compiled ih =>
    cases checked with | call bound admitted checked =>
      cases run with | call selected first second =>
        obtain ⟨steps, middleValid, middleOwns⟩ := call_owns valid owned selected a first
        obtain ⟨xs, hx, tx⟩ := call_forward_effects (Graph.accepted_reflect a first) (owned.live _ selected.member)
        have len : _ := selected.length
        obtain ⟨ys, hy, ty⟩ := ih checked (by omega) middleValid middleOwns second
        exact ⟨_, .call selected hx hy, by simpa [targetTrace, sourceTrace, List.map_append, List.filterMap_append] using append_eq tx ty⟩

theorem closed_target_total (compiled : Lowers p q) (checked : Checked 0 p) :
    ∃ fs h, Runs q [] (erase empty) fs h := by
  obtain ⟨es, s, source⟩ := closed_total checked
  obtain ⟨fs, target, _⟩ := program_forward compiled checked rfl empty_valid empty_owns source
  exact ⟨fs, erase s, target⟩

/-- Source totality plus independently proved target determinism gives coverage
of every target run, not only a forward-selected execution. -/
theorem closed_reflect (compiled : Lowers p q) (checked : Checked 0 p)
    (target : Runs q [] (erase empty) fs h) :
    ∃ es s, LinearHeapPrograms.Runs p [] empty es s ∧ erase s = h ∧ sourceTrace es = targetTrace fs := by
  obtain ⟨es, s, source⟩ := closed_total checked
  obtain ⟨xs, erased, trace⟩ := program_forward compiled checked rfl empty_valid empty_owns source
  obtain ⟨rfl, eq⟩ := erased.deterministic target
  exact ⟨es, s, source, eq, trace.symm⟩

theorem closed_target_safe (compiled : Lowers p q) (checked : Checked 0 p)
    (target : Runs q [] (erase empty) fs h) :
    Steps (erase empty) fs h ∧ ∀ x, h.live x = false := by
  obtain ⟨es, s, source, rfl, _⟩ := closed_reflect compiled checked target
  exact ⟨target.steps, closed_heap_empty checked source⟩

/-- Direct endpoint for the original constructor graph admitted in #136. -/
theorem accepted_target_safe (a : LinearCoreCallers.Accepted g root type)
    (compiled : lower a.program = some q) (target : Runs q [] (erase empty) fs h) :
    Steps (erase empty) fs h ∧ ∀ x, h.live x = false :=
  closed_target_safe (lower_sound compiled) a.checked target

/-- Successful original-graph admission cannot get stuck in this erasure pass. -/
theorem admitted_execution (h : LinearCoreCallers.admit g root type = some a) :
    ∃ q fs heap, lower a.program = some q ∧ Runs q [] (erase empty) fs heap := by
  obtain ⟨q, compiled⟩ := admitted_lower_total h
  obtain ⟨fs, heap, run⟩ := closed_target_total (lower_sound compiled) a.checked
  exact ⟨q, fs, heap, compiled, run⟩

/-- Every target execution corresponds to an original admitted constructor
execution with identical observable effects and erased final heap. -/
theorem accepted_target_reflect (a : LinearCoreCallers.Accepted g root type)
    (compiled : lower a.program = some q) (target : Runs q [] (erase empty) fs h) :
    ∃ es s, LinearCoreCallers.CoreRuns g [] root [] empty es s ∧
      erase s = h ∧ sourceTrace es = targetTrace fs := by
  obtain ⟨es, s, source, eq, trace⟩ := closed_reflect (lower_sound compiled) a.checked target
  exact ⟨es, s, a.source.execution source, eq, trace⟩

def observedAllocations (es : List Observation) : List Nat := es.filterMap fun e =>
  match e with | .alloc x _ => some x | _ => none

def observedReleases (es : List Observation) : List Nat := es.filterMap fun e =>
  match e with | .free x => some x | _ => none

theorem source_allocations : observedAllocations (sourceTrace es) = allocations es := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp_all [observedAllocations, sourceTrace, allocations]

theorem source_releases : observedReleases (sourceTrace es) = released es := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp_all [observedReleases, sourceTrace, released]

/-- Trace reflection transfers exact release conservation, not just final
emptiness: every concrete target allocation is freed exactly once. -/
theorem target_exact_release (compiled : Lowers p q) (checked : Checked 0 p)
    (target : Runs q [] (erase empty) fs h) :
    ∀ x ∈ observedAllocations (targetTrace fs),
      (observedReleases (targetTrace fs)).count x = 1 ∧ h.live x = false := by
  obtain ⟨es, s, source, rfl, trace⟩ := closed_reflect compiled checked target
  rw [← trace, source_allocations, source_releases]
  exact (closed_safety checked source).2.2.2

end Jihoo.LeaseErasure
