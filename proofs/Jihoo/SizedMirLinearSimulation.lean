import Jihoo.SizedMirAllocationEmbedded
import Jihoo.SizedMirRead
import Jihoo.SizedMirTraceBounds
import Jihoo.SizedMirTranslation

/-! Compositional forward execution of generated structured MIR. Source safe
traces justify release and indexed reads; final cumulative bounds justify every
allocation. Source lease metadata is erased by the physical heap relation. -/
namespace Jihoo.SizedMir.Linear
open BoundedMir
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def start (f : Frame) (block : Nat) : Frame := { f with block := block, index := 0 }

@[simp] theorem operand_start : operand (start f block) op = operand f op := by
  cases op <;> rfl

theorem start_eq (block : f.block = target) (index : f.index = 0) : start f target = f := by
  cases f
  simp_all [start]

theorem Compiles.covered (compiled : Compiles inputs kinds l b exit term fragment) : Trace.StructuredTerm term := by
  induction compiled with
  | scalar => exact .scalar
  | natural => exact .natural
  | var => exact .var
  | allocate => exact .allocate
  | app _ _ _ first last => exact .app first last
  | free _ _ ih => exact .free ih
  | lend _ _ _ ih => exact .lend ih
  | ownedLend _ _ _ _ ih => exact .ownedLend ih
  | ifLt _ _ _ _ _ _ yes no => exact .ifLt yes no

theorem Embedded.allocation
    (placed : Embedded c l b (allocationFragment l b exit length fill))
    (out : exit < c.blocks.size) : Allocation.Embedded c l b exit length fill := by
  constructor
  · constructor
    · intro r
      have h := placed.locals r.val (by simp [allocationFragment, Allocation.roleTypes])
      simpa [allocationFragment, Allocation.roleTypes, Allocation.layout] using h
    · simpa [allocationFragment, Allocation.fragmentBlocks, Allocation.labels] using placed.blocks 1 (by simp [allocationFragment, Allocation.fragmentBlocks])
    · simpa [allocationFragment, Allocation.fragmentBlocks, Allocation.labels] using placed.blocks 2 (by simp [allocationFragment, Allocation.fragmentBlocks])
    · simpa [allocationFragment, Allocation.fragmentBlocks, Allocation.labels] using placed.blocks 3 (by simp [allocationFragment, Allocation.fragmentBlocks])
    · simpa [allocationFragment, Allocation.fragmentBlocks, Allocation.labels] using placed.blocks 4 (by simp [allocationFragment, Allocation.fragmentBlocks])
    · simpa [allocationFragment, Allocation.fragmentBlocks, Allocation.labels] using placed.blocks 5 (by simp [allocationFragment, Allocation.fragmentBlocks])
    · exact out
  · simpa [allocationFragment, Allocation.fragmentBlocks] using placed.blocks 0 (by simp [allocationFragment, Allocation.fragmentBlocks])

theorem lifecycle_append (first last : List SizedBufferHeap.Event) :
    lifecycle (first ++ last) = lifecycle first ++ lifecycle last := by
  induction first with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [lifecycle, ih]

/-- Every covered compact execution constructs an instruction execution in the
completed code, retaining the lexical environment and exact heap representation.
No successful MIR run is a premise. -/
theorem Compiles.simulate
    (compiled : Compiles inputs kinds l b exit term fragment)
    (placed : Embedded c l b fragment) (out : exit < c.blocks.size)
    (size : c.locals.size = f.locals.size) (before : InputsBefore l inputs)
    (related : EnvRel env inputs f) (kindsRelated : EnvKinds env kinds) (heaps : HeapRel s f.heap)
    (valid : SizedBufferHeap.Valid s)
    (run : SizedErasure.Eval env term s value events t)
    (safe : SizedBufferHeap.Steps s events t) (bounded : Trace.Bounds t) :
    ∃ final, Steps c (.running (start f (entry b exit term))) (lifecycle events) (.running final) ∧
      final.block = exit ∧ final.index = 0 ∧ HeapRel t final.heap ∧
      operand final fragment.result = some (toMir value) ∧
      final.locals.size = f.locals.size ∧
      (∀ i, i < l → final.locals[i]? = f.locals[i]?) := by
  induction compiled generalizing env f s value events t c with
  | @scalar v inputs kinds l b exit bound =>
    cases run
    refine ⟨start f exit, ?_, rfl, rfl, heaps, ?_, rfl, ?_⟩
    · simpa [entry, blockCost, lifecycle] using (Steps.nil (c := c) (m := .running (start f exit)))
    · simp [pureFragment, operand, constant, toMir, bound]
    · intro i hi; rfl
  | @natural n inputs kinds l b exit bound =>
    cases run
    refine ⟨start f exit, ?_, rfl, rfl, heaps, ?_, rfl, ?_⟩
    · simpa [entry, blockCost, lifecycle] using (Steps.nil (c := c) (m := .running (start f exit)))
    · simp [pureFragment, operand, constant, toMir, bound]
    · intro i hi; rfl
  | @var inputs k op kinds l b exit lookup =>
    cases run with
    | var source =>
      refine ⟨start f exit, ?_, rfl, rfl, heaps, ?_, rfl, ?_⟩
      · simpa [entry, blockCost, lifecycle] using (Steps.nil (c := c) (m := .running (start f exit)))
      · simpa [pureFragment] using related.lookup source lookup
      · intro i hi; rfl
  | @allocate inputs length lengthOp fill fillOp kinds l b exit hn hf =>
    cases run with
    | allocate lengthRun fillRun =>
      rename_i n value
      obtain ⟨objects, cells, payload⟩ := bounded.allocation
      have locals : l + 10 ≤ f.locals.size := by simpa [allocationFragment, Allocation.roleTypes, size] using placed.localBound
      have hobjects : f.heap.size < 512 := by rw [← heaps.nextObject]; exact objects
      have hcells : (f.heap.toList.map (fun obj => obj.cells.size)).sum + n + 1 ≤ 4096 := by
        rw [heaps.cell_count]; exact cells
      obtain ⟨final, target, control, index, heap, result, length, frame⟩ :=
        Allocation.embedded_run (placed.allocation out) locals
          (lowerNat_before before hn) (lowerScalar_before before hf)
          (lowerNat_correct lengthRun related hn) (lowerScalar_correct fillRun related hf)
          hobjects hcells payload
      refine ⟨final, ?_, control, index, ?_, ?_, length, fun i hi => frame i (Or.inl hi)⟩
      · simpa [start, lifecycle, heaps.nextObject] using target
      · rw [heap]; exact heaps.allocate
      · simpa [allocationFragment, toMir, heaps.nextObject] using result
  | @app kinds argument argumentKind inputs l b exit body first last argumentKindRun firstCompiled lastCompiled firstIH lastIH =>
    cases run with
    | app firstRun lastRun =>
      rename_i computed beforeEvents middleState afterEvents
      obtain ⟨firstSafe, lastSafe⟩ := Trace.trace_suffix firstCompiled.covered valid firstRun safe
      have firstPlaced := placed.append_left
      have lastPlaced : Embedded c (l + localCost argument) (b + blockCost argument) last := by
        simpa only [firstCompiled.sizes.1, firstCompiled.sizes.2] using placed.append_right
      have middleExit := lastPlaced.entry_bound lastCompiled out
      obtain ⟨middle, firstSteps, middleBlock, middleIndex, middleHeap, middleValue, middleSize, middleFrame⟩ :=
        firstIH firstPlaced middleExit size before related kindsRelated heaps valid firstRun firstSafe (bounded.backward lastSafe)
      have kept : EnvRel env inputs middle := related.frame before (fun i hi => (middleFrame i hi).symm)
      have newBefore : InputsBefore (l + localCost argument) (first.result :: inputs) := by
        intro op member
        rcases List.mem_cons.mp member with rfl | old
        · exact firstCompiled.result_before before
        · exact (before op old).mono (by omega)
      obtain ⟨final, lastSteps, control, index, heap, result, length, frame⟩ :=
        lastIH lastPlaced out (size.trans middleSize.symm) newBefore (kept.cons middleValue)
          (by simpa [inferKind_correct argumentKindRun kindsRelated firstRun] using kindsRelated.cons (value := computed))
          middleHeap (SizedBufferHeap.steps_valid valid firstSafe) lastRun lastSafe bounded
      rw [start_eq middleBlock middleIndex] at lastSteps
      refine ⟨final, ?_, control, index, heap, result, length.trans middleSize, ?_⟩
      · simpa only [entry_app, lifecycle_append] using steps_trans firstSteps lastSteps
      · intro i hi
        exact (frame i (by omega)).trans (middleFrame i hi)
  | @free inputs k owner kinds l b exit body last lookup bodyCompiled ih =>
    cases run with
    | free source bodyRun =>
      cases safe with
      | cons released rest =>
        cases released with
        | free live unborrowed =>
          rename_i objectId suffix
          have old : objectId < f.heap.size := by rw [← heaps.nextObject]; exact valid.allocated _ live
          have tailPlaced := placed.free_tail
          have tailExit := tailPlaced.entry_bound bodyCompiled out
          have localBound : l < f.locals.size := by
            have h := placed.localBound
            simp only [freeFragment, Array.size_append, Array.size_singleton] at h
            omega
          let initial := start f b
          have firstSteps := free_run (f := initial) placed.free_block rfl placed.free_type localBound tailExit
            (by simpa [initial, toMir] using related.lookup source lookup) heaps old live
          let middle := freedFrame initial l (entry (b + 1) exit body)
            (f.heap.set! objectId { SizedMir.object s objectId with alive := false })
          have middleHeap : HeapRel (SizedBufferHeap.release s objectId) middle.heap := heaps.release old
          have middleSize : middle.locals.size = f.locals.size := by simp [middle, initial, start]
          have middleFrame : ∀ i, i < l → middle.locals[i]? = f.locals[i]? := by
            intro i hi
            exact freedFrame_other (by omega)
          have kept : EnvRel env inputs middle := related.frame before (fun i hi => (middleFrame i hi).symm)
          obtain ⟨final, lastSteps, control, index, heap, result, length, frame⟩ :=
            ih tailPlaced out (size.trans middleSize.symm) (before.mono (by omega)) kept kindsRelated middleHeap
              (SizedBufferHeap.step_valid valid (.free live unborrowed)) bodyRun rest bounded
          have middleStart : start middle (entry (b + 1) exit body) = middle := rfl
          rw [middleStart] at lastSteps
          refine ⟨final, ?_, control, index, heap, result, length.trans middleSize, ?_⟩
          · simpa [initial, middle, lifecycle] using steps_trans firstSteps lastSteps
          · intro i hi
            exact (frame i (by omega)).trans (middleFrame i hi)

  | @lend inputs k owner index indexOp l kinds b exit body last lookup lowered bodyCompiled ih =>
    cases run with
    | lend source indexRun bodyRun =>
      rename_i objectId i suffix
      obtain ⟨live, inside, rest⟩ := Trace.lend_prefix valid safe
      have old : objectId < f.heap.size := by rw [← heaps.nextObject]; exact valid.allocated _ live
      have ownerValue := related.lookup source lookup
      have borrowEnv : EnvRel (.borrow objectId :: env) (owner :: inputs) f := related.cons ownerValue
      have tailPlaced := placed.lend_tail
      have readPlaced := placed.lend_read
      have targetBound := tailPlaced.entry_bound bodyCompiled out
      have localBound : l + 2 ≤ f.locals.size := by
        simpa [readFragment, size] using readPlaced.localBound
      let initial := start f b
      let middle := readFrame initial l (entry (b + 1) exit body) objectId i (s.heap.payload objectId)
      have firstSteps := read_run (f := initial) readPlaced.read_block rfl
        readPlaced.read_ptr_type readPlaced.read_scalar_type localBound targetBound
        (by simpa [initial, toMir] using ownerValue)
        (by simpa [initial] using lowerNat_correct indexRun borrowEnv lowered)
        heaps old live inside
      have middleFrame : ∀ j, j < l → middle.locals[j]? = f.locals[j]? := by
        intro j hj
        exact readFrame_other (Or.inl hj)
      have kept : EnvRel env inputs middle := related.frame before (fun j hj => (middleFrame j hj).symm)
      have ownerAfter := kept.lookup source lookup
      have scalarAfter : operand middle (.copy ⟨l + 1, false⟩) = some (.i64 (s.heap.payload objectId)) :=
        readFrame_result localBound
      have bodyEnv : EnvRel (.owner objectId :: .scalar (s.heap.payload objectId) :: env)
          (owner :: .copy ⟨l + 1, false⟩ :: inputs) middle := .keep ownerAfter (.keep scalarAfter kept)
      have bodyBefore : InputsBefore (l + 2) (owner :: .copy ⟨l + 1, false⟩ :: inputs) := by
        intro op member
        rcases List.mem_cons.mp member with rfl | member
        · exact (before _ (List.mem_of_getElem? lookup)).mono (by omega)
        rcases List.mem_cons.mp member with rfl | member
        · simp [Before]
        · exact (before _ member).mono (by omega)
      have middleSize : middle.locals.size = f.locals.size := by simp [middle, initial, start]
      obtain ⟨final, lastSteps, control, statement, heap, result, length, frame⟩ :=
        ih tailPlaced out (size.trans middleSize.symm) bodyBefore bodyEnv
          (by simpa [kindOf] using (kindsRelated.cons (value := .scalar _)).cons (value := .owner _)) heaps.restore
          (SizedBufferHeap.steps_valid valid (SizedBufferHeap.read_cycle valid live inside)) bodyRun rest bounded
      have middleStart : start middle (entry (b + 1) exit body) = middle := rfl
      rw [middleStart] at lastSteps
      refine ⟨final, ?_, control, statement, heap, result, length.trans middleSize, ?_⟩
      · simpa [initial, middle, lifecycle_append, lifecycle] using steps_trans firstSteps lastSteps
      · intro j hj
        exact (frame j (by omega)).trans (middleFrame j hj)
  | @ownedLend inputs k owner length lengthOp index indexOp l kinds b exit body last
      lookup loweredLength loweredIndex bodyCompiled ih =>
    cases run with
    | ownedLend source indexRun lengthRun bodyRun =>
      rename_i objectId i m suffix
      obtain ⟨live, inside, rest⟩ := Trace.owned_lend_prefix valid safe
      have old : objectId < f.heap.size := by rw [← heaps.nextObject]; exact valid.allocated _ live
      have ownerValue := related.lookup source lookup
      have borrowEnv : EnvRel (.borrow objectId :: env) (owner :: inputs) f := related.cons ownerValue
      have borrowBefore : InputsBefore l (owner :: inputs) := by
        intro op member
        rcases List.mem_cons.mp member with rfl | member
        · exact before _ (List.mem_of_getElem? lookup)
        · exact before _ member
      have lengthBefore := lowerNat_before borrowBefore loweredLength
      have tailPlaced := placed.ownedLend_tail
      have allocationPlaced := placed.ownedLend_allocation
      have readPlaced := placed.ownedLend_read
      have targetBound := tailPlaced.entry_bound bodyCompiled out
      have allocationEntry : b + 1 < c.blocks.size := by
        have h := allocationPlaced.blockBound
        simp [allocationFragment, Allocation.fragmentBlocks] at h
        omega
      have readBound : l + 2 ≤ f.locals.size := by simpa [readFragment, size] using readPlaced.localBound
      let initial := start f b
      let readEnd := readFrame initial l (b + 1) objectId i (s.heap.payload objectId)
      have readSteps := read_run (f := initial) readPlaced.read_block rfl
        readPlaced.read_ptr_type readPlaced.read_scalar_type readBound allocationEntry
        (by simpa [initial, toMir] using ownerValue)
        (by simpa [initial] using lowerNat_correct indexRun borrowEnv loweredIndex)
        heaps old live inside
      have readSize : readEnd.locals.size = f.locals.size := by simp [readEnd, initial, start]
      have readFrameEq : ∀ j, j < l → readEnd.locals[j]? = f.locals[j]? := by
        intro j hj
        exact readFrame_other (Or.inl hj)
      have readHeap : HeapRel (SizedBufferHeap.restore s) readEnd.heap := heaps.restore
      have lengthValue : operand readEnd lengthOp = some (.u64 m) :=
        (operand_frame lengthBefore readFrameEq).trans (lowerNat_correct lengthRun borrowEnv loweredLength)
      have fillValue : operand readEnd (.copy ⟨l + 1, false⟩) = some (.i64 (s.heap.payload objectId)) :=
        readFrame_result readBound
      obtain ⟨objects, cells, payload⟩ := (bounded.backward rest).allocation
      have allocationBound : (l + 2) + 10 ≤ readEnd.locals.size := by
        simpa [allocationFragment, Allocation.roleTypes, readSize, size] using allocationPlaced.localBound
      have hobjects : readEnd.heap.size < 512 := by rw [← readHeap.nextObject]; exact objects
      have hcells : (readEnd.heap.toList.map (fun obj => obj.cells.size)).sum + m + 1 ≤ 4096 := by
        rw [readHeap.cell_count]; exact cells
      obtain ⟨middle, allocationSteps, middleBlock, middleIndex, allocatedHeap, freshOwner, middleSize, allocationFrame⟩ :=
        Allocation.embedded_run (allocationPlaced.allocation targetBound) allocationBound
          (lengthBefore.mono (by omega)) (by simp [Before]) lengthValue fillValue hobjects hcells payload
      change Steps c (.running readEnd) [.alloc readEnd.heap.size (m * 8 + 8)] (.running middle) at allocationSteps
      have middleHeap : HeapRel (SizedOwnedLend.final s m (s.heap.payload objectId)) middle.heap := by
        rw [allocatedHeap]
        exact readHeap.allocate
      have middleFrame : ∀ j, j < l → middle.locals[j]? = f.locals[j]? := by
        intro j hj
        exact (allocationFrame j (Or.inl (by omega))).trans (readFrameEq j hj)
      have kept : EnvRel env inputs middle := related.frame before (fun j hj => (middleFrame j hj).symm)
      have ownerAfter := kept.lookup source lookup
      have newOwner : operand middle (.copy ⟨l + 6, false⟩) = some (.pointer s.heap.nextObject 0) := by
        simpa [Nat.add_assoc, initial, start, ← heaps.nextObject] using freshOwner
      have bodyEnv : EnvRel (.owner objectId :: .owner s.heap.nextObject :: env)
          (owner :: .copy ⟨l + 6, false⟩ :: inputs) middle := .keep ownerAfter (.keep newOwner kept)
      have bodyBefore : InputsBefore (l + 12) (owner :: .copy ⟨l + 6, false⟩ :: inputs) := by
        intro op member
        rcases List.mem_cons.mp member with rfl | member
        · exact (before _ (List.mem_of_getElem? lookup)).mono (by omega)
        rcases List.mem_cons.mp member with rfl | member
        · simp [Before]
        · exact (before _ member).mono (by omega)
      have totalSize := middleSize.trans readSize
      obtain ⟨final, lastSteps, control, statement, heap, result, finalSize, frame⟩ :=
        ih tailPlaced out (size.trans totalSize.symm) bodyBefore bodyEnv
          (by simpa [kindOf] using (kindsRelated.cons (value := .owner _)).cons (value := .owner _)) middleHeap
          (SizedOwnedLend.prefix_valid valid live inside) bodyRun rest bounded
      rw [start_eq middleBlock middleIndex] at lastSteps
      refine ⟨final, ?_, control, statement, heap, result, finalSize.trans totalSize, ?_⟩
      · have joined := steps_trans readSteps (steps_trans allocationSteps lastSteps)
        simpa [initial, lifecycle_append, lifecycle, SizedOwnedLend.events, ← readHeap.nextObject,
          SizedBufferHeap.restore, ScopedLend.restored] using joined
      · intro j hj
        exact (frame j (by omega)).trans (middleFrame j hj)
  | @ifLt inputs left leftOp right rightOp kinds yes kind no l b yesCode noCode exit
      loweredLeft loweredRight yesKind noKind yesCompiled noCompiled yesIH noIH =>
    have yesPlaced := placed.branch_yes
    have noPlaced : Embedded c (l + 2 + localCost yes) (b + 3 + blockCost yes) noCode := by
      simpa only [yesCompiled.sizes.1, yesCompiled.sizes.2] using placed.branch_no
    have adminBound : b + 3 ≤ c.blocks.size := by
      have h := placed.blockBound
      simp [branchFragment] at h
      omega
    have localBound : l + 2 ≤ f.locals.size := by
      have h := placed.localBound
      simp [branchFragment] at h
      omega
    have yesExit : b + 1 < c.blocks.size := by omega
    have noExit : b + 2 < c.blocks.size := by omega
    have yesEntry := yesPlaced.entry_bound yesCompiled yesExit
    have noEntry := noPlaced.entry_bound noCompiled noExit
    cases run with
    | yes leftRun rightRun lt bodyRun =>
      rename_i a n
      let initial := start f b
      let middle := Branch.decisionFrame initial l (entry (b + 3) (b + 1) yes)
        (entry (b + 3 + blockCost yes) (b + 2) no) a n
      have decision := Branch.decision_run (f := initial) placed.branch_decision rfl
        placed.branch_type.1 (by change l < f.locals.size; omega) yesEntry noEntry
        (by simpa [initial] using lowerNat_correct leftRun related loweredLeft)
        (by simpa [initial] using lowerNat_correct rightRun related loweredRight)
      have middleFrame : ∀ i, i < l → middle.locals[i]? = f.locals[i]? := by
        intro i hi
        exact Branch.decisionFrame_other (by omega)
      have kept := related.frame before (fun i hi => (middleFrame i hi).symm)
      have middleSize : middle.locals.size = f.locals.size := by simp [middle, initial, start]
      obtain ⟨bodyEnd, bodySteps, control, index, heap, result, length, frame⟩ :=
        yesIH yesPlaced yesExit (size.trans middleSize.symm) (before.mono (by omega))
          kept kindsRelated heaps valid bodyRun safe bounded
      have middleStart : start middle (entry (b + 3) (b + 1) yes) = middle := by
        apply start_eq <;> simp [middle, lt]
      rw [middleStart] at bodySteps
      have bodyType : c.locals[l + 1]? = some (valueType (toMir value)) := by
        rw [toMir_valueType, inferKind_correct yesKind kindsRelated bodyRun]
        exact placed.branch_type.2
      have bodyBound : l + 1 < bodyEnd.locals.size := by rw [length, middleSize]; omega
      have joined := Branch.join_run (f := bodyEnd) (by rw [control]; exact placed.branch_yes_join)
        index bodyType bodyBound out result
      refine ⟨Branch.joinFrame bodyEnd (l + 1) exit (toMir value), ?_, rfl, rfl, heap,
        Branch.joinFrame_result bodyBound, ?_, ?_⟩
      · simpa [initial, middle, entry, blockCost, lt] using
          steps_trans decision (steps_trans bodySteps joined)
      · simpa using length.trans middleSize
      · intro i hi
        exact (Branch.joinFrame_other (by omega)).trans ((frame i (by omega)).trans (middleFrame i hi))
    | no leftRun rightRun lt bodyRun =>
      rename_i a n
      let initial := start f b
      let middle := Branch.decisionFrame initial l (entry (b + 3) (b + 1) yes)
        (entry (b + 3 + blockCost yes) (b + 2) no) a n
      have decision := Branch.decision_run (f := initial) placed.branch_decision rfl
        placed.branch_type.1 (by change l < f.locals.size; omega) yesEntry noEntry
        (by simpa [initial] using lowerNat_correct leftRun related loweredLeft)
        (by simpa [initial] using lowerNat_correct rightRun related loweredRight)
      have middleFrame : ∀ i, i < l → middle.locals[i]? = f.locals[i]? := by
        intro i hi
        exact Branch.decisionFrame_other (by omega)
      have kept := related.frame before (fun i hi => (middleFrame i hi).symm)
      have middleSize : middle.locals.size = f.locals.size := by simp [middle, initial, start]
      obtain ⟨bodyEnd, bodySteps, control, index, heap, result, length, frame⟩ :=
        noIH noPlaced noExit (size.trans middleSize.symm) (before.mono (by omega))
          kept kindsRelated heaps valid bodyRun safe bounded
      have middleStart : start middle (entry (b + 3 + blockCost yes) (b + 2) no) = middle := by
        apply start_eq <;> simp [middle, lt]
      rw [middleStart] at bodySteps
      have bodyType : c.locals[l + 1]? = some (valueType (toMir value)) := by
        rw [toMir_valueType, inferKind_correct noKind kindsRelated bodyRun]
        exact placed.branch_type.2
      have bodyBound : l + 1 < bodyEnd.locals.size := by rw [length, middleSize]; omega
      have joined := Branch.join_run (f := bodyEnd) (by rw [control]; exact placed.branch_no_join)
        index bodyType bodyBound out result
      refine ⟨Branch.joinFrame bodyEnd (l + 1) exit (toMir value), ?_, rfl, rfl, heap,
        Branch.joinFrame_result bodyBound, ?_, ?_⟩
      · simpa [initial, middle, entry, blockCost, lt] using
          steps_trans decision (steps_trans bodySteps joined)
      · simpa using length.trans middleSize
      · intro i hi
        exact (Branch.joinFrame_other (by omega)).trans ((frame i (by omega)).trans (middleFrame i hi))

end Jihoo.SizedMir.Linear
