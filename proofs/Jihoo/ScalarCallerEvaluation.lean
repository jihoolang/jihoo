import Jihoo.ScalarCoreCallers
import Jihoo.HeapLifecycle

/-! Executable evaluation of the independently specified scalar caller target.
This evaluator does not inspect MIR. Its successful result is related to the
existing operational semantics before a translation validator compares outputs. -/
namespace Jihoo.ScalarCallerEvaluation
open HeapLeases ScopedLend LinearHeapPrograms
open ScalarCoreCallers

abbrev Life := HeapLifecycle.Event

def lifecycle (events : List LeaseErasure.Event) : List Life := events.filterMap fun e =>
  match e with | .alloc x _ => some (.alloc x 16) | .free x => some (.free x) | _ => none

def select : List Nat → Nat → Option (Nat × List Nat)
  | [], _ => none
  | x :: xs, 0 => some (x, xs)
  | y :: ys, k + 1 => do
    let (x, rest) ← select ys k
    pure (x, y :: rest)

theorem select_sound (h : select owners slot = some (x, rest)) : Select owners slot x rest := by
  induction owners generalizing slot rest with
  | nil => simp [select] at h
  | cons y ys ih =>
    cases slot with
    | zero => simp [select] at h; obtain ⟨rfl, rfl⟩ := h; exact .here
    | succ k =>
      cases hs : select ys k with
      | none => simp [select, hs] at h
      | some pair =>
        obtain ⟨z, tail⟩ := pair
        simp [select, hs] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .there (ih hs)

theorem select_complete (h : Select owners slot x rest) : select owners slot = some (x, rest) := by
  induction h with
  | here => rfl
  | there _ ih => simp [select, ih]

def evalReader (heap : LeaseErasure.Heap) (owner : Nat) : LeaseErasure.Code → Option (Nat × List LeaseErasure.Event)
  | .scalar v => some (v, [])
  | .load => if heap.live owner then some (heap.payload owner, [.read owner (heap.payload owner)]) else none
  | .seq a b => do
    let (_, xs) ← evalReader heap owner a
    let (v, ys) ← evalReader heap owner b
    pure (v, xs ++ ys)
  | .branch c a b => if c then evalReader heap owner a else evalReader heap owner b

theorem reader_sound (h : evalReader heap owner code = some (v, es)) :
    LeaseErasure.Reads heap owner code v es := by
  induction code generalizing v es with
  | scalar value => simp [evalReader] at h; obtain ⟨rfl, rfl⟩ := h; exact .scalar
  | load =>
    simp only [evalReader] at h
    split at h
    · simp at h; obtain ⟨rfl, rfl⟩ := h; exact .load (by assumption)
    · contradiction
  | seq a b ia ib =>
    cases ha : evalReader heap owner a with
    | none => simp [evalReader, ha] at h
    | some pair =>
      obtain ⟨w, xs⟩ := pair
      cases hb : evalReader heap owner b with
      | none => simp [evalReader, ha, hb] at h
      | some pair =>
        obtain ⟨z, ys⟩ := pair
        simp [evalReader, ha, hb] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .seq (ia ha) (ib hb)
  | branch c a b ia ib =>
    cases c with
    | true => exact .yes (ia h)
    | false => exact .no (ib h)

theorem reader_complete (h : LeaseErasure.Reads heap owner code v es) :
    evalReader heap owner code = some (v, es) := by
  induction h with
  | scalar => rfl
  | load live => simp [evalReader, live]
  | seq _ _ ia ib => simp [evalReader, ia, ib]
  | yes _ ih | no _ ih => exact ih

abbrev Output := Nat × List LeaseErasure.Event × LeaseErasure.Heap

def evalCall (heap : LeaseErasure.Heap) (owner : Nat) (code : LeaseErasure.Code)
    (next : Continuation) : Option Output := do
  if !heap.live owner then none else do
  let (v, es) ← evalReader heap owner code
  pure (v, es ++ LeaseErasure.continuationEvents owner v next, LeaseErasure.finish heap owner v next)

theorem call_sound (h : evalCall heap owner code next = some (v, es, final)) :
    LeaseErasure.Calls heap owner code next v es final := by
  simp only [evalCall] at h
  split at h
  · contradiction
  · next live =>
    have live' : heap.live owner = true := by simpa using live
    cases hr : evalReader heap owner code with
    | none => simp [hr] at h
    | some pair =>
      obtain ⟨w, reads⟩ := pair
      simp [hr] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .run live' (reader_sound hr)

theorem call_complete (h : LeaseErasure.Calls heap owner code next v es final) :
    evalCall heap owner code next = some (v, es, final) := by
  cases h with
  | run live reads => simp [evalCall, live, reader_complete reads]

def evalProgram : Target.Program → List Nat → List Nat → LeaseErasure.Heap → Option Output
  | .finish result, owners, values, heap => do
    if !owners.isEmpty then none else do
    let v ← result.eval values
    pure (v, [], heap)
  | .allocate v body, owners, values, heap => do
    let (result, events, final) ← evalProgram body (heap.nextObject :: owners) values (LeaseErasure.allocate heap v)
    pure (result, .alloc heap.nextObject v :: events, final)
  | .call slot code next body, owners, values, heap => do
    let (owner, rest) ← select owners slot
    let (v, first, middle) ← evalCall heap owner code next
    let (result, second, final) ← evalProgram body rest (v :: values) middle
    pure (result, first ++ second, final)

theorem program_sound (h : evalProgram p owners values heap = some (v, es, final)) :
    Target.Runs p owners values heap v es final := by
  induction p generalizing owners values heap v es final with
  | finish result =>
    simp only [evalProgram] at h
    split at h
    · contradiction
    · next empty =>
      have empty' : owners = [] := by simpa using empty
      subst owners
      cases hr : result.eval values with
      | none => simp [hr] at h
      | some w => simp [hr] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact .finish hr
  | allocate value body ih =>
    cases hb : evalProgram body (heap.nextObject :: owners) values (LeaseErasure.allocate heap value) with
    | none => simp [evalProgram, hb] at h
    | some output =>
      obtain ⟨w, events, finish⟩ := output
      simp [evalProgram, hb] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .allocate (ih hb)
  | call slot code next body ih =>
    cases hs : select owners slot with
    | none => simp [evalProgram, hs] at h
    | some pair =>
      obtain ⟨owner, rest⟩ := pair
      cases hc : evalCall heap owner code next with
      | none => simp [evalProgram, hs, hc] at h
      | some output =>
        obtain ⟨w, first, middle⟩ := output
        cases hb : evalProgram body rest (w :: values) middle with
        | none => simp [evalProgram, hs, hc, hb] at h
        | some output =>
          obtain ⟨result, second, finish⟩ := output
          simp [evalProgram, hs, hc, hb] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact .call (select_sound hs) (call_sound hc) (ih hb)

theorem program_complete (h : Target.Runs p owners values heap v es final) :
    evalProgram p owners values heap = some (v, es, final) := by
  induction h with
  | finish result => simp [evalProgram, result]
  | allocate _ ih => simp [evalProgram, ih]
  | call selected called _ ih => simp [evalProgram, select_complete selected, call_complete called, ih]

structure Accepted (g : Graph.Graph) (root type : Nat) where
  source : ScalarCoreCallers.Accepted g root type
  target : Target.Program
  compiled : lower source.program = some target
  value : Nat
  events : List LeaseErasure.Event
  heap : LeaseErasure.Heap
  evaluated : evalProgram target [] [] (LeaseErasure.erase empty) = some (value, events, heap)

def admit (g : Graph.Graph) (root type : Nat) : Option (Accepted g root type) := do
  let some source := ScalarCoreCallers.admit g root type | none
  match hc : lower source.program with
  | none => none
  | some target => match he : evalProgram target [] [] (LeaseErasure.erase empty) with
    | none => none
    | some (value, events, heap) => some ⟨source, target, hc, value, events, heap, he⟩

theorem accepted_original (a : Accepted g root type) :
    ∃ es s, CoreRuns g [] root [] [] empty a.value es s ∧ LeaseErasure.erase s = a.heap ∧
      LeaseErasure.sourceTrace es = LeaseErasure.targetTrace a.events :=
  accepted_target_reflect a.source a.compiled (program_sound a.evaluated)

theorem accepted_heap_empty (a : Accepted g root type) : ∀ x, a.heap.live x = false :=
  (accepted_target_safe a.source a.compiled (program_sound a.evaluated)).2.1

theorem admitted_evaluation_total (h : ScalarCoreCallers.admit g root type = some source) :
    ∃ a, admit g root type = some a := by
  obtain ⟨target, v, es, heap, compiled, run⟩ := admitted_execution h
  have evaluated := program_complete run
  unfold admit
  simp only [h]
  split
  · next hc => simp [hc] at compiled
  · next q hc =>
    have eq : q = target := Option.some.inj (hc.symm.trans compiled)
    subst q
    split
    · next he => simp [he] at evaluated
    · exact ⟨_, rfl⟩

def sourceLifecycle (events : List HeapLeases.Event) : List Life := events.filterMap fun e =>
  match e with | .alloc x _ => some (.alloc x 16) | .free x => some (.free x) | _ => none

def observedLifecycle (events : List LeaseErasure.Observation) : List Life := events.filterMap fun e =>
  match e with | .alloc x _ => some (.alloc x 16) | .free x => some (.free x) | _ => none

theorem lifecycle_target : observedLifecycle (LeaseErasure.targetTrace es) = lifecycle es := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp_all [observedLifecycle, LeaseErasure.targetTrace, lifecycle]

theorem lifecycle_source : observedLifecycle (LeaseErasure.sourceTrace es) = sourceLifecycle es := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp_all [observedLifecycle, LeaseErasure.sourceTrace, sourceLifecycle]

theorem accepted_original_lifecycle (a : Accepted g root type) :
    ∃ es s, CoreRuns g [] root [] [] empty a.value es s ∧ LeaseErasure.erase s = a.heap ∧
      sourceLifecycle es = lifecycle a.events := by
  obtain ⟨es, s, run, heap, trace⟩ := accepted_original a
  refine ⟨es, s, run, heap, ?_⟩
  simpa [lifecycle_target, lifecycle_source] using congrArg observedLifecycle trace

/-- Every operational source run agrees with the independently computed source
reference, including its observable allocator lifecycle. -/
theorem accepted_all_source (a : Accepted g root type)
    (run : CoreRuns g [] root [] [] empty v es s) :
    v = a.value ∧ sourceLifecycle es = lifecycle a.events := by
  obtain ⟨fs, target, trace⟩ := accepted_forward a.source a.compiled run
  obtain ⟨value, events, _⟩ := target.deterministic (program_sound a.evaluated)
  refine ⟨value, ?_⟩
  have life := congrArg observedLifecycle trace.symm
  simpa [lifecycle_source, lifecycle_target, events] using life

end Jihoo.ScalarCallerEvaluation
