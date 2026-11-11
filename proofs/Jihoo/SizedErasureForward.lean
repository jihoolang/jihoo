import Jihoo.SizedCoreErasure

/-! Source-to-runtime execution correspondence for lexical proof erasure.
Structural coverage includes both branches, while environment correspondence
ensures every retained source slot has an observable runtime value. -/
namespace Jihoo.SizedErasure
open ScopedLend

/-- Retention excludes ghost results even for otherwise untyped source runs. -/
private theorem retained_value (related : EnvRel mask env runtime)
    (retained : mask[k]? = some true) (lookup : env[k]? = some value) :
    ∃ result, value = result.embed ∧ runtime[rank mask k]? = some result := by
  induction related generalizing k value with
  | nil => simp at retained
  | consKeep v tail ih =>
      cases k with
      | zero => exact ⟨v, (Option.some.inj lookup).symm, rfl⟩
      | succ k => simpa using ih retained lookup
  | consGhost tail ih =>
      cases k with
      | zero => simp at retained
      | succ k => simpa using ih retained lookup

/-- Every source execution covered by erasure has a compact execution with
exactly the same value, events, and final heap. No target run is assumed. -/
theorem Erases.forward (erased : Erases g mask root term)
    (related : EnvRel mask env runtime)
    (run : SizedCoreExecution.Eval g env root s value events t) :
    ∃ result, value = result.embed ∧ Eval runtime term s result events t := by
  induction erased generalizing env runtime s value events t with
  | scalar shape =>
      cases run with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; cases eq
          exact ⟨_, rfl, .scalar⟩
      | natural shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' lam' firstRun lastRun =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' lengthRun initRun =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' variableShape' lookup suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' leftRun rightRun bound suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' leftRun rightRun bound suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' variableShape' lookup indexRun suffix =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
      | ownedLend shape' variableShape' lookup indexRun lengthRun suffix =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
  | natural shape =>
      cases run with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := shape.symm.trans shape'; cases eq
          exact ⟨_, rfl, .natural⟩
      | var shape' lookup =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' lam' firstRun lastRun =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' lengthRun initRun =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' variableShape' lookup suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' leftRun rightRun bound suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' leftRun rightRun bound suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' variableShape' lookup indexRun suffix =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
      | ownedLend shape' variableShape' lookup indexRun lengthRun suffix =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
  | var shape retained =>
      cases run with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup =>
          have eq := shape.symm.trans shape'; cases eq
          obtain ⟨result, same, compact⟩ := retained_value related retained lookup
          exact ⟨result, same, .var compact⟩
      | app shape' lam' firstRun lastRun =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' lengthRun initRun =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' variableShape' lookup suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' leftRun rightRun bound suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' leftRun rightRun bound suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' variableShape' lookup indexRun suffix =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
      | ownedLend shape' variableShape' lookup indexRun lengthRun suffix =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
  | app shape lam first last ihf ihl =>
      cases run with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' lam' firstRun lastRun =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := lam.symm.trans lam'; cases eq
          obtain ⟨argument, rfl, firstCompact⟩ := ihf related firstRun
          obtain ⟨result, same, lastCompact⟩ := ihl (related.consKeep argument) lastRun
          exact ⟨result, same, .app firstCompact lastCompact⟩
      | allocate shape' lengthRun initRun =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' variableShape' lookup suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' leftRun rightRun bound suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' leftRun rightRun bound suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' variableShape' lookup indexRun suffix =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
      | ownedLend shape' variableShape' lookup indexRun lengthRun suffix =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
  | allocate shape length init =>
      cases run with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' lam' firstRun lastRun =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' lengthRun initRun =>
          have eq := shape.symm.trans shape'; cases eq
          exact ⟨_, rfl, .allocate (length.forward related lengthRun) (init.forward related initRun)⟩
      | free shape' variableShape' lookup suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' leftRun rightRun bound suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' leftRun rightRun bound suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' variableShape' lookup indexRun suffix =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
      | ownedLend shape' variableShape' lookup indexRun lengthRun suffix =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
  | free shape variableShape retained body ih =>
      cases run with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' lam' firstRun lastRun =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' lengthRun initRun =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' variableShape' lookup suffix =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := variableShape.symm.trans variableShape'; cases eq
          obtain ⟨result, same, compact⟩ := ih related suffix
          exact ⟨result, same, .free ((related.retained_lookup_iff retained).mp lookup) compact⟩
      | yes shape' leftRun rightRun bound suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' leftRun rightRun bound suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' variableShape' lookup indexRun suffix =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
      | ownedLend shape' variableShape' lookup indexRun lengthRun suffix =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
  | branch shape left right yes no iy ino =>
      cases run with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' lam' firstRun lastRun =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' lengthRun initRun =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' variableShape' lookup suffix =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' leftRun rightRun bound suffix =>
          have eq := shape.symm.trans shape'; cases eq
          obtain ⟨result, same, compact⟩ := iy related.consGhost suffix
          exact ⟨result, same, .yes (left.forward related leftRun)
            (right.forward related rightRun) bound compact⟩
      | no shape' leftRun rightRun bound suffix =>
          have eq := shape.symm.trans shape'; cases eq
          obtain ⟨result, same, compact⟩ := ino related suffix
          exact ⟨result, same, .no (left.forward related leftRun)
            (right.forward related rightRun) bound compact⟩
      | lend shape' variableShape' lookup indexRun suffix =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
      | ownedLend shape' variableShape' lookup indexRun lengthRun suffix =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
  | lend shape variableShape retained index body ih =>
      obtain ⟨_, _, head⟩ := shape.head
      cases run with
      | scalar shape' =>
          have eq := head.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := head.symm.trans shape'; contradiction
      | var shape' lookup =>
          have eq := head.symm.trans shape'; contradiction
      | app shape' lam' firstRun lastRun =>
          have eq := head.symm.trans shape'; contradiction
      | allocate shape' lengthRun initRun =>
          have eq := head.symm.trans shape'; contradiction
      | free shape' variableShape' lookup suffix =>
          have eq := head.symm.trans shape'; contradiction
      | yes shape' leftRun rightRun bound suffix =>
          have eq := head.symm.trans shape'; contradiction
      | no shape' leftRun rightRun bound suffix =>
          have eq := head.symm.trans shape'; contradiction
      | lend shape' variableShape' lookup indexRun suffix =>
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := variableShape.symm.trans variableShape'; cases eq
          obtain ⟨result, same, compact⟩ := ih ((related.consKeep (.scalar _)).consKeep (.owner _)) suffix
          exact ⟨result, same, .lend ((related.retained_lookup_iff retained).mp lookup)
            (index.forward (related.consKeep (.borrow _)) indexRun) compact⟩
      | ownedLend shape' variableShape' lookup indexRun lengthRun suffix =>
          exact False.elim (shape'.not_read shape)
  | ownedLend shape variableShape retained length index body ih =>
      obtain ⟨_, _, head⟩ := shape.head
      cases run with
      | scalar shape' =>
          have eq := head.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := head.symm.trans shape'; contradiction
      | var shape' lookup =>
          have eq := head.symm.trans shape'; contradiction
      | app shape' lam' firstRun lastRun =>
          have eq := head.symm.trans shape'; contradiction
      | allocate shape' lengthRun initRun =>
          have eq := head.symm.trans shape'; contradiction
      | free shape' variableShape' lookup suffix =>
          have eq := head.symm.trans shape'; contradiction
      | yes shape' leftRun rightRun bound suffix =>
          have eq := head.symm.trans shape'; contradiction
      | no shape' leftRun rightRun bound suffix =>
          have eq := head.symm.trans shape'; contradiction
      | lend shape' variableShape' lookup indexRun suffix =>
          exact False.elim (shape.not_read shape')
      | ownedLend shape' variableShape' lookup indexRun lengthRun suffix =>
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := variableShape.symm.trans variableShape'; cases eq
          obtain ⟨result, same, compact⟩ := ih ((related.consKeep (.owner _)).consKeep (.owner _)) suffix
          exact ⟨result, same, .ownedLend ((related.retained_lookup_iff retained).mp lookup)
            (index.forward (related.consKeep (.borrow _)) indexRun)
            (length.forward (related.consKeep (.borrow _)) lengthRun) compact⟩

/-- Erasure is an exact correspondence of terminating executions, including
source runs whose result was not assumed in advance to be non-ghost. -/
theorem Erases.execution_iff (erased : Erases g mask root term)
    (related : EnvRel mask env runtime) :
    SizedCoreExecution.Eval g env root s value events t ↔
      ∃ result, value = result.embed ∧ Eval runtime term s result events t := by
  constructor
  · exact erased.forward related
  · rintro ⟨result, rfl, run⟩
    exact erased.backward related run

/-- Observable values agree without an existential wrapper. -/
theorem Erases.eval_iff (erased : Erases g mask root term)
    (related : EnvRel mask env runtime) :
    SizedCoreExecution.Eval g env root s value.embed events t ↔
      Eval runtime term s value events t := by
  constructor
  · intro run
    obtain ⟨result, same, compact⟩ := erased.forward related run
    obtain rfl := Value.embed_inj.mp same
    exact compact
  · exact erased.backward related

open SizedBufferContext SizedCoreTyping LinearHeapPrograms

/-- A well-typed closing instance whose whole syntax is covered by erasure
has a compact execution. Safety and accounting are conclusions, not runtime
premises. -/
theorem Erases.total_accounted (erased : Erases g mask root term)
    (related : EnvRel mask env runtime) (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners) :
    ∃ value events t, Eval runtime term s value events t ∧
      SizedBufferHeap.Steps s events t ∧ SizedBufferHeap.Valid t ∧
      Post kind t value.embed ∧ Account owners value.embed events := by
  obtain ⟨source, events, t, run, steps, finalValid, post, accounted⟩ :=
    typed.total_accounted agree layout valid owned
  obtain ⟨value, rfl, compact⟩ := erased.forward related run
  exact ⟨value, events, t, compact, steps, finalValid, post, accounted⟩

/-- Every execution of the independent runtime inherits the source safety
result. Neither a source execution nor safe target trace is assumed. -/
theorem Erases.every_run_safe (erased : Erases g mask root term)
    (related : EnvRel mask env runtime) (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners)
    (run : Eval runtime term s value events t) :
    SizedBufferHeap.Steps s events t ∧ SizedBufferHeap.Valid t ∧ Post kind t value.embed :=
  typed.every_run_safe agree layout valid owned (erased.backward related run)

/-- Exact per-identity allocation/release accounting survives compaction. -/
theorem Erases.every_run_accounted (erased : Erases g mask root term)
    (related : EnvRel mask env runtime) (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners)
    (run : Eval runtime term s value events t) : Account owners value.embed events :=
  typed.every_run_accounted agree layout valid owned (erased.backward related run)

/-- Compact producer execution preserves disjoint captured owners, deriving
result/frame disjointness from execution rather than assuming it. -/
theorem Erases.framed_safe (erased : Erases g mask root term)
    (related : EnvRel mask env runtime) (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap (owners ++ frame))
    (run : Eval runtime term s value events t) :
    SizedBufferHeap.Steps s events t ∧ SizedBufferHeap.Valid t ∧
      Post kind t value.embed ∧ Owns t.heap (resultOwners value.embed ++ frame) :=
  typed.framed_safe agree layout valid owned (erased.backward related run)

/-- Retained captures preserve their exact lengths and payloads across a
compact runtime execution, not just their ownership. -/
theorem Erases.frame_contents (erased : Erases g mask root term)
    (related : EnvRel mask env runtime) (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap (owners ++ frame))
    (run : Eval runtime term s value events t) (member : x ∈ frame) :
    t.length x = s.length x ∧ t.heap.payload x = s.heap.payload x :=
  typed.frame_contents agree layout valid owned (erased.backward related run) member

end Jihoo.SizedErasure
