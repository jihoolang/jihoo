import Jihoo.SizedMirEntryAdequacy
import Jihoo.SizedMirBranchCoreExamples

/-! Actual checked entry frames start at block zero. These examples do not set
control state or prefill scratch locals after admission. -/
namespace Jihoo.SizedMirEntryExamples
open BoundedMir SizedMir
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def fragment (types : Array Ty) (entry : BoundedMir.Entry) (term : SizedErasure.Term) : Linear.Fragment :=
  (Entry.lowerProgram types entry term).getD (Linear.pureFragment (.constant (.i64 0)))
def code (types : Array Ty) (entry : BoundedMir.Entry) (term : SizedErasure.Term) : Code :=
  Entry.program types term (fragment types entry term)
def observe (fuel : Nat) (types : Array Ty) (entry : BoundedMir.Entry)
    (term : SizedErasure.Term) (values : List Value) : Option (Nat × Array Object × List Event) := do
  let frame ← entryFrame (code types entry term) entry values
  let out ← runFor fuel (code types entry term) (.running frame)
  let .returned value final := out.machine | none
  return (value, final.heap, out.events)

def types : Array Ty := #[.i64,.u64,.u64,.i64]
def entry : BoundedMir.Entry := ⟨#[2,1,3]⟩
def term : SizedErasure.Term := .ifLt (.var 0) (.var 1)
  (.app (.allocate (.var 0) (.var 2)) (.free 0 (.var 3))) (.var 2)

theorem lowered : Entry.lowerProgram types entry term = some (fragment types entry term) := by decide +kernel

theorem ordered_input_contents :
    (entryFrame (code types entry term) entry [.u64 2,.u64 4,.i64 17]).map
      (fun f => f.locals.toList.take 4) =
    some [none,some (.u64 4),some (.u64 2),some (.i64 17)] := by
  decide +kernel

theorem executes_true_from_entry : observe 100 types entry term [.u64 2,.u64 4,.i64 17] =
    some (17,#[⟨false,#[some 17,some 17,none]⟩],[.alloc 0 24,.free 0]) := by decide +kernel

theorem executes_equal_from_entry : observe 100 types entry term [.u64 2,.u64 2,.i64 17] =
    some (17,#[],[]) := by decide +kernel

theorem executes_greater_from_entry : observe 100 types entry term [.u64 4,.u64 2,.i64 17] =
    some (17,#[],[]) := by decide +kernel

theorem zero_allocation_from_entry : observe 100 types entry term [.u64 0,.u64 2,.i64 17] =
    some (17,#[⟨false,#[none]⟩],[.alloc 0 8,.free 0]) := by decide +kernel

theorem empty_input_lowered : Entry.lowerProgram #[.i64] ⟨#[]⟩ (.scalar 41) =
    some (fragment #[.i64] ⟨#[]⟩ (.scalar 41)) := by decide +kernel

theorem empty_input_executes : observe 4 #[.i64] ⟨#[]⟩ (.scalar 41) [] =
    some (41,#[],[]) := by decide +kernel

theorem short_fuel_is_partial :
    (do let f ← entryFrame (code #[.i64] ⟨#[]⟩ (.scalar 41)) ⟨#[]⟩ []
        let out ← runFor 1 (code #[.i64] ⟨#[]⟩ (.scalar 41)) (.running f)
        pure (match out.machine with | .running f => some (f.block,f.index) | _ => none)) =
      some (some (1,0)) := by decide +kernel

theorem wrong_arity_rejected : entryFrame (code types entry term) entry [.u64 2,.u64 4] = none := by decide +kernel
theorem wrong_type_rejected : entryFrame (code types entry term) entry [.i64 2,.u64 4,.i64 17] = none := by decide +kernel
theorem natural_overflow_rejected : entryFrame (code types entry term) entry
    [.u64 wordBound,.u64 4,.i64 17] = none := by decide +kernel
theorem scalar_overflow_rejected : entryFrame (code types entry term) entry
    [.u64 2,.u64 4,.i64 scalarBound] = none := by decide +kernel
theorem duplicate_slots_rejected : Entry.lowerProgram types ⟨#[1,1,3]⟩ term = none := by decide +kernel
theorem return_slot_rejected : Entry.lowerProgram types ⟨#[0]⟩ (.var 0) = none := by decide +kernel
theorem missing_slot_rejected : Entry.lowerProgram types ⟨#[4]⟩ (.var 0) = none := by decide +kernel
theorem pointer_input_rejected : Entry.lowerProgram #[.i64,.ptr] ⟨#[1]⟩
    (.free 0 (.scalar 41)) = none := by decide +kernel

def sourceEnv : SizedBufferContext.Env := [.ghost,.nat 2,.ghost,.scalar 17]
def ghostTerm : SizedErasure.Term := .var 1

theorem ghost_slots_compacted : SizedErasure.compactEnv sourceEnv =
    ([false,true,false,true],[.nat 2,.scalar 17]) := rfl

theorem ghost_variable_compiled : SizedErasure.compileTarget #[.var 3] 2
    (SizedErasure.compactEnv sourceEnv).1 0 = some ghostTerm := by decide +kernel

theorem compacted_inputs_lowered : Entry.lowerProgram #[.i64,.u64,.i64] ⟨#[1,2]⟩ ghostTerm =
    some (fragment #[.i64,.u64,.i64] ⟨#[1,2]⟩ ghostTerm) := by decide +kernel

theorem compacted_inputs_execute : observe 4 #[.i64,.u64,.i64] ⟨#[1,2]⟩ ghostTerm
    ((SizedErasure.compactEnv sourceEnv).2.map toMir) = some (17,#[],[]) := by decide +kernel

def coreTypes : Array Ty := #[.i64,.u64,.u64,.u64,.i64]
def coreEntry : BoundedMir.Entry := ⟨#[4,3,2,1]⟩
abbrev coreTerm := SizedErasureExamples.target

theorem core_lowered : Entry.lowerProgram coreTypes coreEntry coreTerm =
    some (fragment coreTypes coreEntry coreTerm) := by decide +kernel

theorem core_empty_original : observe 200 coreTypes coreEntry coreTerm [.i64 42,.u64 0,.u64 3,.u64 0] =
    some (99,materialize (SizedMirBranchCoreExamples.finalState 0 3 0 42),[.alloc 0 8,.free 0]) := by decide +kernel

theorem core_outside : observe 200 coreTypes coreEntry coreTerm [.i64 42,.u64 7,.u64 2,.u64 7] =
    some (99,materialize (SizedMirBranchCoreExamples.finalState 7 2 7 42),[.alloc 0 64,.free 0]) := by decide +kernel

theorem core_zero_copy : observe 200 coreTypes coreEntry coreTerm [.i64 42,.u64 6,.u64 0,.u64 7] =
    some (42,materialize (SizedMirBranchCoreExamples.finalState 7 0 6 42),
      [.alloc 0 64,.alloc 1 8,.free 0,.free 1]) := by decide +kernel

theorem core_positive_copy : observe 200 coreTypes coreEntry coreTerm [.i64 42,.u64 6,.u64 2,.u64 7] =
    some (42,materialize (SizedMirBranchCoreExamples.finalState 7 2 6 42),
      [.alloc 0 64,.alloc 1 24,.free 0,.free 1]) := by decide +kernel

/-- A single generated entry admits every bounded four-argument instance. -/
theorem core_admission (capacity : n + m + 2 ≤ 4096) (index : i < wordBound)
    (payload : value < scalarBound) :
    ∃ f, entryFrame (code coreTypes coreEntry coreTerm) coreEntry
      [.i64 value,.u64 i,.u64 m,.u64 n] = some f := by
  have hn : n < wordBound := by unfold wordBound; omega
  have hm : m < wordBound := by unfold wordBound; omega
  have signature : entryValid (code coreTypes coreEntry coreTerm) coreEntry = true := by decide +kernel
  have size : (code coreTypes coreEntry coreTerm).locals.size = 38 := by decide +kernel
  have t1 : (code coreTypes coreEntry coreTerm).locals[1]? = some .u64 := by decide +kernel
  have t2 : (code coreTypes coreEntry coreTerm).locals[2]? = some .u64 := by decide +kernel
  have t3 : (code coreTypes coreEntry coreTerm).locals[3]? = some .u64 := by decide +kernel
  have t4 : (code coreTypes coreEntry coreTerm).locals[4]? = some .i64 := by decide +kernel
  unfold entryFrame
  rw [signature]
  change ∃ f, bindArguments (code coreTypes coreEntry coreTerm) [4,3,2,1]
    [.i64 value,.u64 i,.u64 m,.u64 n] (initial (code coreTypes coreEntry coreTerm)) = some f
  simp [bindArguments, argumentValueValid, valueType, initial, size, t1, t2, t3, t4,
    hn, hm, index, payload, Array.set!, Array.setIfInBounds]
  obtain ⟨_, e4⟩ := Array.getElem_of_getElem? t4
  obtain ⟨_, e3⟩ := Array.getElem_of_getElem? t3
  obtain ⟨_, e2⟩ := Array.getElem_of_getElem? t2
  obtain ⟨_, e1⟩ := Array.getElem_of_getElem? t1
  exact ⟨e4,e3,e2,e1⟩

/-- Source typing, erasure, lowering and actual ABI admission construct the run.
No target frame contents, control reset or successful target run are supplied. -/
theorem core_total (capacity : n + m + 2 ≤ 4096) (index : i < wordBound)
    (payload : value < scalarBound) :
    ∃ f final,
      entryFrame (code coreTypes coreEntry coreTerm) coreEntry
        [.i64 value,.u64 i,.u64 m,.u64 n] = some f ∧
      Steps (code coreTypes coreEntry coreTerm) (.running f)
        (lifecycle (SizedMirBranchCoreExamples.events n m i value))
        (.returned (if i < n then value else 99) final) ∧
      HeapRel (SizedMirBranchCoreExamples.finalState n m i value) final.heap ∧
      SizedCoreTyping.Account [] (.scalar (if i < n then value else 99))
        (SizedMirBranchCoreExamples.events n m i value) := by
  obtain ⟨f, admitted⟩ := core_admission capacity index payload
  have compacted : SizedErasure.compileTarget SizedCompositionGraph.graph 128
      (SizedErasure.compactEnv (SizedCompositionExamples.inputEnv n m i value)).1 81 = some coreTerm :=
    SizedErasureExamples.compiled
  obtain ⟨result, events, state, final, source, target, heap, account, _⟩ :=
    Entry.typed_source_total compacted core_lowered (SizedCompositionExamples.body_typed n m i)
      (SizedCompositionExamples.input_agrees n m i value) ⟨rfl, by simp⟩ LinearHeapPrograms.empty_owns
      (by simpa [code, SizedCompositionExamples.inputEnv, SizedErasure.compactEnv, toMir] using admitted)
      (fun _ _ _ run => SizedMirBranchCoreExamples.every_run_bounded capacity payload run)
  obtain ⟨same, ev, st⟩ := source.deterministic (SizedMirBranchCoreExamples.source_run n m i value)
  cases same
  subst events state
  exact ⟨f, final, admitted, target, heap, account⟩

end Jihoo.SizedMirEntryExamples
