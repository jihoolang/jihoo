import Jihoo.SizedMirAllocation

/-! The generated allocation template inside a completed enclosing MIR program.
Scratch slots may already contain arbitrary values. Only the selected ten local
roles and the newly allocated object change. -/
namespace Jihoo.SizedMir.Allocation
open BoundedMir
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

structure Embedded (c : Code) (localBase blockBase exit : Nat)
    (length fill : Operand) : Prop where
  buffer : MirBuffer.Embedded c (layout localBase) (labels blockBase exit)
  input : c.blocks[blockBase]? = some (inputBlock localBase blockBase exit length fill)

theorem overlay_other_opt (slots : Fin size → Nat)
    (original : Array (Option Value)) (vals : Fin size → Option Value)
    (hother : ∀ r, slots r ≠ i) :
    (MirLocal.overlay slots original vals)[i]? = original[i]? := by
  by_cases hi : i < original.size
  · have hb : i < (MirLocal.overlay slots original vals).size := by simpa using hi
    rw [getElem?_pos (MirLocal.overlay slots original vals) i hb, getElem?_pos original i hi]
    congr 1
    rw [← getElem!_pos (MirLocal.overlay slots original vals) i hb,
      ← getElem!_pos original i hi]
    exact MirLocal.overlay_other slots original vals i hother
  · simp [getElem?_neg, hi]

@[simp] private theorem embedded_values_update0 :
    MirLocal.updateValues (MirBuffer.values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 0 x =
      MirBuffer.values x a1 a2 a3 a4 a5 a6 a7 a8 a9 := by
  funext ⟨r, hr⟩
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp] private theorem embedded_values_update1 :
    MirLocal.updateValues (MirBuffer.values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 1 x =
      MirBuffer.values a0 x a2 a3 a4 a5 a6 a7 a8 a9 := by
  funext ⟨r, hr⟩
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl


def savedValues (localBase : Nat) (original : Array (Option Value)) : MirBuffer.Role → Option Value :=
  MirBuffer.values original[localBase]! original[localBase + 1]!
    original[localBase + 2]! original[localBase + 3]! original[localBase + 4]!
    original[localBase + 5]! original[localBase + 6]! original[localBase + 7]!
    original[localBase + 8]! original[localBase + 9]!

theorem saved_overlay : MirLocal.overlay (layout localBase).slot original
    (savedValues localBase original) = original := by
  apply MirLocal.overlay_same
  intro ⟨r, hr⟩
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem embedded_role_bounds {original : Array (Option Value)} (bound : localBase + 10 ≤ original.size) (r : MirBuffer.Role) :
    (layout localBase).slot r < original.size := by
  have hr := r.isLt
  simp only [layout]
  omega

theorem embedded_local_frame (outside : i < localBase ∨ localBase + 10 ≤ i) :
    (MirBuffer.frame (layout localBase) original H vals block index).locals[i]? = original[i]? := by
  apply overlay_other_opt
  intro r
  have hr := r.isLt
  simp only [layout]
  omega

theorem embedded_operand_frame (old : Before localBase op) :
    operand (MirBuffer.frame (layout localBase) original H vals block index) op =
      operand ⟨sourceBlock, sourceIndex, original, H⟩ op :=
  SizedMir.operand_frame old (fun _ bound => embedded_local_frame (Or.inl bound))

/-- The two copies execute inside the completed program, without extending or
requiring empty contents in the ten reserved local slots. -/
theorem embedded_input_prefix
    (emb : Embedded c localBase blockBase exit length fill)
    (bound : localBase + 10 ≤ original.size)
    (lengthOld : Before localBase length) (fillOld : Before localBase fill)
    (lengthValue : operand ⟨sourceBlock, sourceIndex, original, H⟩ length = some (.u64 n))
    (fillValue : operand ⟨sourceBlock, sourceIndex, original, H⟩ fill = some (.i64 value)) :
    runFor 3 c (.running ⟨blockBase, 0, original, H⟩) =
      some ⟨.running (MirBuffer.frame (layout localBase) original H
        (MirBuffer.values (some (.u64 n)) (some (.i64 value))
          original[localBase + 2]! original[localBase + 3]! original[localBase + 4]!
          original[localBase + 5]! original[localBase + 6]! original[localBase + 7]!
          original[localBase + 8]! original[localBase + 9]!)
        (blockBase + 1) 0), []⟩ := by
  have input' (hb : blockBase < c.blocks.size) :
      c.blocks[blockBase]'hb = inputBlock localBase blockBase exit length fill := by
    simpa only [getElem?_pos c.blocks blockBase hb, Option.some.injEq] using emb.input
  have jumpBound : blockBase + 1 < c.blocks.size := by
    have h := emb.buffer.entry
    exact (Array.getElem?_eq_some_iff.mp h).1
  have hn (vals : MirBuffer.Role → Option Value) (block index : Nat) :
      operand (MirBuffer.frame (layout localBase) original H vals block index) length = some (.u64 n) :=
    (embedded_operand_frame lengthOld).trans lengthValue
  have hv (vals : MirBuffer.Role → Option Value) (block index : Nat) :
      operand (MirBuffer.frame (layout localBase) original H vals block index) fill = some (.i64 value) :=
    (embedded_operand_frame fillOld).trans fillValue
  simp only [MirBuffer.frame] at hn hv
  have bounds (r : MirBuffer.Role) : (layout localBase).slot r < original.size :=
    embedded_role_bounds bound r
  have set (vals : MirBuffer.Role → Option Value) (r : MirBuffer.Role) (x : Option Value) :
      (MirLocal.overlay (layout localBase).slot original vals).setIfInBounds
        ((layout localBase).slot r) x =
      MirLocal.overlay (layout localBase).slot original (MirLocal.updateValues vals r x) :=
    MirLocal.overlay_set! _ _ _ (layout localBase).distinct r (bounds r) x
  have prefixRun : runFor 3 c
      (.running (MirBuffer.frame (layout localBase) original H
        (savedValues localBase original) blockBase 0)) =
      some ⟨.running (MirBuffer.frame (layout localBase) original H
        (MirBuffer.values (some (.u64 n)) (some (.i64 value))
          original[localBase + 2]! original[localBase + 3]! original[localBase + 4]!
          original[localBase + 5]! original[localBase + 6]! original[localBase + 7]!
          original[localBase + 8]! original[localBase + 9]!)
        (blockBase + 1) 0), []⟩ := by
    simp [runFor, rawTick, fetch, emb.input, input', inputBlock, MirBuffer.slotPlace,
      rvalue, hn, hv, write, emb.buffer.types, valueType, MirBuffer.frame, advance, jump,
      set, bounds, jumpBound, savedValues]
  simpa only [MirBuffer.frame, saved_overlay] using prefixRun

/-- A structurally embedded generated allocation constructs its own execution;
all surrounding locals, including later fragments' scratch slots, are framed. -/
theorem embedded_run
    (emb : Embedded c localBase blockBase exit length fill)
    (bound : localBase + 10 ≤ original.size)
    (lengthOld : Before localBase length) (fillOld : Before localBase fill)
    (lengthValue : operand ⟨sourceBlock, sourceIndex, original, H⟩ length = some (.u64 n))
    (fillValue : operand ⟨sourceBlock, sourceIndex, original, H⟩ fill = some (.i64 value))
    (hobjects : H.size < 512)
    (hcells : (H.toList.map (fun obj => obj.cells.size)).sum + n + 1 ≤ 4096)
    (hv : value < scalarBound) :
    ∃ final, Steps c (.running ⟨blockBase, 0, original, H⟩)
      [.alloc H.size (n * 8 + 8)] (.running final) ∧
      final.block = exit ∧ final.index = 0 ∧
      final.heap = H.push ⟨true, MirBuffer.cells n value n⟩ ∧
      operand final (.copy ⟨localBase + 4, false⟩) = some (.pointer H.size 0) ∧
      final.locals.size = original.size ∧
      (∀ i, i < localBase ∨ localBase + 10 ≤ i → final.locals[i]? = original[i]?) := by
  have bounds := embedded_role_bounds bound
  have first := runFor_sound (embedded_input_prefix emb bound lengthOld fillOld lengthValue fillValue)
  obtain ⟨dest, rest⟩ := MirBuffer.terminates (original := original) (H := H)
    (n := n) (value := value)
    (a2 := original[localBase + 2]!) (a3 := original[localBase + 3]!)
    (a4 := original[localBase + 4]!) (a5 := original[localBase + 5]!)
    (a6 := original[localBase + 6]!) (a7 := original[localBase + 7]!)
    (a8 := original[localBase + 8]!) (a9 := original[localBase + 9]!)
    emb.buffer bounds hobjects hcells hv
  refine ⟨MirBuffer.outputFrame (layout localBase) (labels blockBase exit) original H n value dest,
    ?_, rfl, rfl, rfl, ?_, MirBuffer.output_local_size, ?_⟩
  · simpa only [labels, List.nil_append] using steps_trans first rest
  · have lookup : (MirLocal.overlay (layout localBase).slot original
        (MirBuffer.loopValues n value H.size n (some (.boolean false)) dest))[localBase + 4]? =
        some (some (.pointer H.size 0)) :=
      MirLocal.overlay_lookup_opt (layout localBase).slot original
        (MirBuffer.loopValues n value H.size n (some (.boolean false)) dest)
        (layout localBase).distinct 4 (bounds 4)
    simp [operand, MirBuffer.outputFrame, MirBuffer.frame, lookup]
  · intro i outside
    exact embedded_local_frame outside

end Jihoo.SizedMir.Allocation
