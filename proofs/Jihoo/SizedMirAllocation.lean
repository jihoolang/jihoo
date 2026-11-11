import Jihoo.MirBufferFragment
import Jihoo.SizedMirOperands

/-! A constructive allocation/fill MIR builder. It appends fresh locals and
blocks to an enclosing code, retaining an existing continuation. The builder
is separate from the executable jihoo compiler's lowering implementation. -/
namespace Jihoo.SizedMir.Allocation
open BoundedMir
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def layout (base : Nat) : MirBuffer.Layout where
  slot := fun r => base + r.val
  distinct := by intro a b h; apply Fin.ext; omega

def labels (base exit : Nat) : MirBuffer.Labels :=
  ⟨base + 1, base + 2, base + 3, base + 4, base + 5, exit⟩

def roleTypes : Array Ty := Array.ofFn MirBuffer.roleType

def inputBlock (localBase blockBase _exit : Nat) (length fill : Operand) : Block :=
  ⟨#[⟨MirBuffer.slotPlace (layout localBase) 0, .use length⟩,
      ⟨MirBuffer.slotPlace (layout localBase) 1, .use fill⟩], .goto (blockBase + 1)⟩

def fragmentBlocks (localBase blockBase exit : Nat) (length fill : Operand) : Array Block :=
  let l := layout localBase
  let b := labels blockBase exit
  #[inputBlock localBase blockBase exit length fill,
    MirBuffer.entryBlock l b, MirBuffer.guardBlock l b,
    MirBuffer.initBlock l b, MirBuffer.testBlock l b, MirBuffer.bodyBlock l b]

def build (before : Code) (exit : Nat) (length fill : Operand) : Code :=
  ⟨before.locals ++ roleTypes,
    before.blocks ++ fragmentBlocks before.locals.size before.blocks.size exit length fill⟩

@[simp] theorem local_count : (build before exit length fill).locals.size = before.locals.size + 10 := by
  simp [build, roleTypes]

@[simp] theorem block_count : (build before exit length fill).blocks.size = before.blocks.size + 6 := by
  simp [build, fragmentBlocks]

theorem local_prefix (h : i < before.locals.size) :
    (build before exit length fill).locals[i]? = before.locals[i]? := by
  exact Array.getElem?_append_left h

theorem block_prefix (h : i < before.blocks.size) :
    (build before exit length fill).blocks[i]? = before.blocks[i]? := by
  exact Array.getElem?_append_left h

theorem input_block :
    (build before exit length fill).blocks[before.blocks.size]? =
      some (inputBlock before.locals.size before.blocks.size exit length fill) := by
  simp [build, fragmentBlocks]

/-- The five executable blocks and all role declarations are generated together;
no external structural-embedding certificate is assumed by the simulation. -/
theorem embedded (hexit : exit < before.blocks.size) :
    MirBuffer.Embedded (build before exit length fill) (layout before.locals.size)
      (labels before.blocks.size exit) := by
  constructor
  · intro r
    simp [build, layout, roleTypes]
  · simp [build, labels, fragmentBlocks]
  · simp [build, labels, fragmentBlocks]
  · simp [build, labels, fragmentBlocks]
  · simp [build, labels, fragmentBlocks]
  · simp [build, labels, fragmentBlocks]
  · simp [labels]
    omega

def extendLocals (original : Array (Option Value)) : Array (Option Value) :=
  original ++ Array.replicate 10 none

@[simp] theorem extended_size : (extendLocals original).size = original.size + 10 := by
  simp [extendLocals]

theorem fresh_bounds (r : MirBuffer.Role) :
    (layout original.size).slot r < (extendLocals original).size := by
  have hr := r.isLt
  simp [layout]

theorem fresh_none (r : MirBuffer.Role) :
    (extendLocals original)[(layout original.size).slot r]! = none := by
  have hr := r.isLt
  rw [getElem!_pos (extendLocals original) _ (fresh_bounds r)]
  simp [extendLocals, layout, Array.getElem_append_right]

private theorem overlay_other_opt (slots : Fin size → Nat)
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

theorem frame_local_prefix (hi : i < original.size) :
    (MirBuffer.frame (layout original.size) (extendLocals original) H vals block index).locals[i]? =
      original[i]? := by
  unfold MirBuffer.frame
  rw [overlay_other_opt]
  · exact Array.getElem?_append_left hi
  · intro r
    simp [layout]
    omega

theorem initial_overlay :
    MirLocal.overlay (layout original.size).slot (extendLocals original)
      (MirBuffer.values none none none none none none none none none none) =
      extendLocals original := by
  apply MirLocal.overlay_same
  intro r
  rw [fresh_none]
  unfold MirBuffer.values
  split <;> rfl

theorem operand_in_frame (old : Before original.size op) :
    operand (MirBuffer.frame (layout original.size) (extendLocals original) H vals block index) op =
      operand ⟨sourceBlock, sourceIndex, original, H⟩ op :=
  SizedMir.operand_frame old (fun _ bound => frame_local_prefix bound)

@[simp] private theorem values_update0 :
    MirLocal.updateValues (MirBuffer.values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 0 x =
      MirBuffer.values x a1 a2 a3 a4 a5 a6 a7 a8 a9 := by
  funext ⟨r, hr⟩
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp] private theorem values_update1 :
    MirLocal.updateValues (MirBuffer.values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 1 x =
      MirBuffer.values a0 x a2 a3 a4 a5 a6 a7 a8 a9 := by
  funext ⟨r, hr⟩
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Copy both lowered operands before allocation. Fresh destinations cannot
clobber a local read by the second operand, even when the inputs alias. -/
theorem input_prefix
    (hsize : before.locals.size = original.size) (hexit : exit < before.blocks.size)
    (lengthOld : Before original.size length) (fillOld : Before original.size fill)
    (lengthValue : operand ⟨sourceBlock, sourceIndex, original, H⟩ length = some (.u64 n))
    (fillValue : operand ⟨sourceBlock, sourceIndex, original, H⟩ fill = some (.i64 value)) :
    runFor 3 (build before exit length fill)
      (.running ⟨before.blocks.size, 0, extendLocals original, H⟩) =
      some ⟨.running (MirBuffer.frame (layout original.size) (extendLocals original) H
        (MirBuffer.values (some (.u64 n)) (some (.i64 value)) none none none none none none none none)
        (before.blocks.size + 1) 0), []⟩ := by
  have emb : MirBuffer.Embedded (build before exit length fill)
      (layout original.size) (labels before.blocks.size exit) := by
    simpa only [hsize] using embedded (length := length) (fill := fill) hexit
  have input : (build before exit length fill).blocks[before.blocks.size]? =
      some (inputBlock original.size before.blocks.size exit length fill) := by
    simpa only [hsize] using (input_block (before := before) (exit := exit) (length := length) (fill := fill))
  have input' (hb : before.blocks.size < (build before exit length fill).blocks.size) :
      (build before exit length fill).blocks[before.blocks.size]'hb =
      inputBlock original.size before.blocks.size exit length fill := by
    simpa only [getElem?_pos (build before exit length fill).blocks before.blocks.size hb,
      Option.some.injEq] using input
  have jumpBound : before.blocks.size + 1 < (build before exit length fill).blocks.size := by simp
  have hn (vals : MirBuffer.Role → Option Value) (block index : Nat) :
      operand (MirBuffer.frame (layout original.size) (extendLocals original) H vals block index) length = some (.u64 n) :=
    (operand_in_frame lengthOld).trans lengthValue
  have hv (vals : MirBuffer.Role → Option Value) (block index : Nat) :
      operand (MirBuffer.frame (layout original.size) (extendLocals original) H vals block index) fill = some (.i64 value) :=
    (operand_in_frame fillOld).trans fillValue
  simp only [MirBuffer.frame] at hn hv
  have bound (r : MirBuffer.Role) : (layout original.size).slot r < original.size + 10 := by
    simpa only [extended_size] using (fresh_bounds (original := original) r)
  have set (vals : MirBuffer.Role → Option Value) (r : MirBuffer.Role) (x : Option Value) :
      (MirLocal.overlay (layout original.size).slot (extendLocals original) vals).setIfInBounds
        ((layout original.size).slot r) x =
      MirLocal.overlay (layout original.size).slot (extendLocals original) (MirLocal.updateValues vals r x) :=
    MirLocal.overlay_set! _ _ _ (layout original.size).distinct r (fresh_bounds r) x
  have prefixRun : runFor 3 (build before exit length fill)
      (.running (MirBuffer.frame (layout original.size) (extendLocals original) H
        (MirBuffer.values none none none none none none none none none none) before.blocks.size 0)) =
      some ⟨.running (MirBuffer.frame (layout original.size) (extendLocals original) H
        (MirBuffer.values (some (.u64 n)) (some (.i64 value)) none none none none none none none none)
        (before.blocks.size + 1) 0), []⟩ := by
    simp [runFor, rawTick, fetch, input, input', inputBlock, MirBuffer.slotPlace,
      rvalue, hn, hv, write, emb.types, valueType, MirBuffer.frame, advance, jump,
      set, bound, jumpBound]
  simpa only [MirBuffer.frame, initial_overlay] using prefixRun

def startFrame (before : Code) (original : Array (Option Value)) (H : Array Object) : Frame :=
  ⟨before.blocks.size, 0, extendLocals original, H⟩

noncomputable def outputFrame (before : Code) (exit : Nat) (original : Array (Option Value))
    (H : Array Object) (n value : Nat) (dest : Option Value) : Frame :=
  MirBuffer.outputFrame (layout original.size) (labels before.blocks.size exit)
    (extendLocals original) H n value dest

/-- A generated allocation, including its input-copy block, reaches the chosen
continuation. Only the actual operand values and allocator bounds are premises. -/
theorem run (hsize : before.locals.size = original.size) (hexit : exit < before.blocks.size)
    (lengthOld : Before original.size length) (fillOld : Before original.size fill)
    (lengthValue : operand ⟨sourceBlock, sourceIndex, original, H⟩ length = some (.u64 n))
    (fillValue : operand ⟨sourceBlock, sourceIndex, original, H⟩ fill = some (.i64 value))
    (hobjects : H.size < 512)
    (hcells : (H.toList.map (fun obj => obj.cells.size)).sum + n + 1 ≤ 4096)
    (hv : value < scalarBound) :
    ∃ dest, Steps (build before exit length fill) (.running (startFrame before original H))
      [.alloc H.size (n * 8 + 8)] (.running (outputFrame before exit original H n value dest)) := by
  have emb : MirBuffer.Embedded (build before exit length fill)
      (layout original.size) (labels before.blocks.size exit) := by
    simpa only [hsize] using embedded (length := length) (fill := fill) hexit
  have first := runFor_sound (input_prefix hsize hexit lengthOld fillOld lengthValue fillValue)
  obtain ⟨dest, rest⟩ := MirBuffer.terminates (original := extendLocals original) (H := H)
    (n := n) (value := value) (a2 := none) (a3 := none) (a4 := none) (a5 := none)
    (a6 := none) (a7 := none) (a8 := none) (a9 := none)
    emb fresh_bounds hobjects hcells hv
  exact ⟨dest, by simpa only [startFrame, outputFrame, labels, List.nil_append] using steps_trans first rest⟩

theorem output_local_prefix (old : i < original.size) :
    (outputFrame before exit original H n value dest).locals[i]? = original[i]? :=
  frame_local_prefix old

theorem output_owner :
    (outputFrame before exit original H n value dest).locals[original.size + 4]! =
      some (.pointer H.size 0) :=
  (MirBuffer.output_roles (l := layout original.size) (b := labels before.blocks.size exit)
    (original := extendLocals original) (H := H) (n := n) (value := value) (dest := dest)
    fresh_bounds).2.2.1

theorem output_owner_operand :
    operand (outputFrame before exit original H n value dest)
      (.copy ⟨original.size + 4, false⟩) = some (.pointer H.size 0) := by
  have lookup : (outputFrame before exit original H n value dest).locals[original.size + 4]? =
      some (some (.pointer H.size 0)) :=
    MirLocal.overlay_lookup_opt (layout original.size).slot (extendLocals original) _
      (layout original.size).distinct 4 (fresh_bounds 4)
  simp [operand, lookup]

theorem output_heap :
    (outputFrame before exit original H n value dest).heap =
      H.push ⟨true, MirBuffer.cells n value n⟩ := rfl

theorem output_control :
    (outputFrame before exit original H n value dest).block = exit ∧
      (outputFrame before exit original H n value dest).index = 0 := ⟨rfl, rfl⟩

end Jihoo.SizedMir.Allocation
