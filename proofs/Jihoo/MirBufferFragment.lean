import Jihoo.BoundedMirRun
import Jihoo.MirLocalOverlay
import Jihoo.MirBufferHeap

/-! A relocatable allocation-and-fill CFG fragment. The code template uses actual
BoundedMir instructions. Its continuation block belongs to the enclosing program.
Only the eight designated scratch locals and one fresh heap object are changed. -/
namespace Jihoo.MirBuffer
open BoundedMir
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev Role := Fin 10

/-- Roles 0/1 are length/payload inputs; 2..9 are disposable scratch locals. -/
structure Layout where
  slot : Role → Nat
  distinct : ∀ a b, slot a = slot b → a = b

structure Labels where
  entry : Nat
  guard : Nat
  init : Nat
  test : Nat
  body : Nat
  exit : Nat
  deriving DecidableEq, Repr

def roleType (r : Role) : Ty :=
  match r.val with
  | 1 => .i64 | 4 | 9 => .ptr | 6 | 8 => .bool | _ => .u64

def slotPlace (l : Layout) (r : Role) : Place := ⟨l.slot r, false⟩
def copy (l : Layout) (r : Role) : Operand := .copy (slotPlace l r)

def entryBlock (l : Layout) (b : Labels) : Block :=
  ⟨#[⟨slotPlace l 2, .bin .mul (copy l 0) (.constant (.u64 8))⟩,
      ⟨slotPlace l 3, .bin .add (copy l 2) (.constant (.u64 8))⟩],
    .malloc (copy l 3) (slotPlace l 4) b.guard⟩
def guardBlock (l : Layout) (b : Labels) : Block :=
  ⟨#[⟨slotPlace l 5, .ptrCast (copy l 4)⟩,
      ⟨slotPlace l 6, .bin .ne (copy l 5) (.constant (.u64 0))⟩],
    .assert (copy l 6) b.init⟩
def initBlock (l : Layout) (b : Labels) : Block :=
  ⟨#[⟨slotPlace l 7, .use (.constant (.u64 0))⟩], .goto b.test⟩
def testBlock (l : Layout) (b : Labels) : Block :=
  ⟨#[⟨slotPlace l 8, .bin .lt (copy l 7) (copy l 0)⟩],
    .switch (copy l 8) [(0, b.exit)] b.body⟩
def bodyBlock (l : Layout) (b : Labels) : Block :=
  ⟨#[⟨slotPlace l 9, .offset (copy l 4) (copy l 7)⟩,
      ⟨⟨l.slot 9, true⟩, .use (copy l 1)⟩,
      ⟨slotPlace l 7, .bin .add (copy l 7) (.constant (.u64 1))⟩], .goto b.test⟩

/-- Structural embedding, not a successful-execution or safety certificate.
Other blocks and all non-role slotPlace declarations are unconstrained. -/
structure Embedded (c : Code) (l : Layout) (b : Labels) : Prop where
  types : ∀ r, c.locals[l.slot r]? = some (roleType r)
  entry : c.blocks[b.entry]? = some (entryBlock l b)
  guard : c.blocks[b.guard]? = some (guardBlock l b)
  init : c.blocks[b.init]? = some (initBlock l b)
  test : c.blocks[b.test]? = some (testBlock l b)
  body : c.blocks[b.body]? = some (bodyBlock l b)
  exit : b.exit < c.blocks.size

def values (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Option Value) : Role → Option Value :=
  fun r => match r.val with
  | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3 | 4 => a4
  | 5 => a5 | 6 => a6 | 7 => a7 | 8 => a8 | _ => a9

@[simp] theorem values_update2 :
    MirLocal.updateValues (values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 2 x = values a0 a1 x a3 a4 a5 a6 a7 a8 a9 := by
  funext ⟨r, hr⟩
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp] theorem values_update3 :
    MirLocal.updateValues (values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 3 x = values a0 a1 a2 x a4 a5 a6 a7 a8 a9 := by
  funext ⟨r, hr⟩
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp] theorem values_update4 :
    MirLocal.updateValues (values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 4 x = values a0 a1 a2 a3 x a5 a6 a7 a8 a9 := by
  funext ⟨r, hr⟩
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp] theorem values_update5 :
    MirLocal.updateValues (values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 5 x = values a0 a1 a2 a3 a4 x a6 a7 a8 a9 := by
  funext ⟨r, hr⟩
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp] theorem values_update6 :
    MirLocal.updateValues (values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 6 x = values a0 a1 a2 a3 a4 a5 x a7 a8 a9 := by
  funext ⟨r, hr⟩
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp] theorem values_update7 :
    MirLocal.updateValues (values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 7 x = values a0 a1 a2 a3 a4 a5 a6 x a8 a9 := by
  funext ⟨r, hr⟩
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp] theorem values_update8 :
    MirLocal.updateValues (values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 8 x = values a0 a1 a2 a3 a4 a5 a6 a7 x a9 := by
  funext ⟨r, hr⟩
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp] theorem values_update9 :
    MirLocal.updateValues (values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 9 x = values a0 a1 a2 a3 a4 a5 a6 a7 a8 x := by
  funext ⟨r, hr⟩
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def loopValues (n value object k : Nat) (test dest : Option Value) : Role → Option Value :=
  values (some (.u64 n)) (some (.i64 value)) (some (.u64 (n*8)))
    (some (.u64 (n*8+8))) (some (.pointer object 0)) (some (.address object))
    (some (.boolean true)) (some (.u64 k)) test dest

noncomputable def frame (l : Layout) (original : Array (Option Value))
    (heap : Array Object) (vals : Role → Option Value) (block index : Nat) : Frame :=
  ⟨block, index, MirLocal.overlay l.slot original vals, heap⟩

noncomputable def loopFrame (l : Layout) (b : Labels) (original : Array (Option Value))
    (H : Array Object) (n value k : Nat) (test dest : Option Value) : Frame :=
  frame l original (H.push ⟨true, cells n value k⟩)
    (loopValues n value H.size k test dest) b.test 0

@[simp] theorem roleType0 : roleType 0 = .u64 := rfl
@[simp] theorem roleType1 : roleType 1 = .i64 := rfl
@[simp] theorem roleType2 : roleType 2 = .u64 := rfl
@[simp] theorem roleType3 : roleType 3 = .u64 := rfl
@[simp] theorem roleType4 : roleType 4 = .ptr := rfl
@[simp] theorem roleType5 : roleType 5 = .u64 := rfl
@[simp] theorem roleType6 : roleType 6 = .bool := rfl
@[simp] theorem roleType7 : roleType 7 = .u64 := rfl
@[simp] theorem roleType8 : roleType 8 = .bool := rfl
@[simp] theorem roleType9 : roleType 9 = .ptr := rfl

@[simp] theorem values0 : values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 0 = a0 := rfl
@[simp] theorem values1 : values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 1 = a1 := rfl
@[simp] theorem values2 : values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 2 = a2 := rfl
@[simp] theorem values3 : values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 3 = a3 := rfl
@[simp] theorem values4 : values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 4 = a4 := rfl
@[simp] theorem values5 : values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 5 = a5 := rfl
@[simp] theorem values6 : values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 6 = a6 := rfl
@[simp] theorem values7 : values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 7 = a7 := rfl
@[simp] theorem values8 : values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 8 = a8 := rfl
@[simp] theorem values9 : values a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 9 = a9 := rfl

private theorem elem_of_some {xs : Array α} (h : xs[i]? = some x) (hb : i < xs.size) :
    xs[i] = x := by simpa only [getElem?_pos xs i hb, Option.some.injEq] using h

private theorem block_bound {c : Code} (h : c.blocks[b]? = some block) : b < c.blocks.size :=
  (Array.getElem?_eq_some_iff.mp h).choose


/-- Eight actual instructions allocate raw cells and establish the loop invariant. -/
theorem initialization_prefix (h : Embedded c l b)
    (hl : ∀ r, l.slot r < original.size)
    (hobjects : H.size < 512)
    (hcells : (H.toList.map (fun obj => obj.cells.size)).sum + n + 1 ≤ 4096) :
    runFor 8 c (.running (frame l original H
      (values (some (.u64 n)) (some (.i64 value)) a2 a3 a4 a5 a6 a7 a8 a9) b.entry 0)) =
      some ⟨.running (loopFrame l b original H n value 0 a8 a9),
        [.alloc H.size (n * 8 + 8)]⟩ := by
  have mulBound : n * 8 < wordBound := by unfold wordBound; omega
  have byteBound : n * 8 + 8 < wordBound := by unfold wordBound; omega
  have hg := block_bound h.guard
  have hi := block_bound h.init
  have ht := block_bound h.test
  have look (vals : Role → Option Value) (r : Role) :
      (MirLocal.overlay l.slot original vals)[l.slot r]? = some (vals r) :=
    MirLocal.overlay_lookup_opt l.slot original vals l.distinct r (hl r)
  have set (vals : Role → Option Value) (r : Role) (x : Option Value) :
      (MirLocal.overlay l.slot original vals).set! (l.slot r) x =
        MirLocal.overlay l.slot original (MirLocal.updateValues vals r x) :=
    MirLocal.overlay_set! l.slot original vals l.distinct r (hl r) x
  have look' (vals : Role → Option Value) (r : Role) (hb) :
      (MirLocal.overlay l.slot original vals)[l.slot r]'hb = vals r := by
    rw [← getElem!_pos (MirLocal.overlay l.slot original vals) (l.slot r) hb]
    exact MirLocal.overlay_lookup l.slot original vals l.distinct r (hl r)
  have set' (vals : Role → Option Value) (r : Role) (x : Option Value) :
      (MirLocal.overlay l.slot original vals).setIfInBounds (l.slot r) x =
        MirLocal.overlay l.slot original (MirLocal.updateValues vals r x) := set vals r x
  change n * 8 < 18446744073709551616 at mulBound
  change n * 8 + 8 < 18446744073709551616 at byteBound
  simp! [runFor, rawTick, fetch, h.entry, h.guard, h.init, elem_of_some h.guard, elem_of_some h.init, entryBlock, guardBlock,
    initBlock, frame, loopFrame, loopValues, slotPlace, copy, rvalue, operand,
    constant, binary, write, valueType, advance, jump, h.types,
    look, set, look', set', hl, mulBound, byteBound, hg, hi, ht, wordBound,
    malloc_heap (value := value) H hobjects hcells]

/-- Six transitions test, store one initialized cell, increment and return to the
loop header. The heap prefix and every non-role local are arbitrary. -/
theorem fill_iteration (h : Embedded c l b)
    (hl : ∀ r, l.slot r < original.size)
    (hn : n ≤ 4095) (hk : k < n) (hv : value < scalarBound) :
    runFor 6 c (.running (loopFrame l b original H n value k test dest)) =
      some ⟨.running (loopFrame l b original H n value (k + 1)
        (some (.boolean true)) (some (.pointer H.size k))), []⟩ := by
  have bound : k + 1 < 18446744073709551616 := by omega
  have offset : k ≤ n + 1 := by omega
  have store : k < n + 1 := by omega
  have ht := block_bound h.test
  have hb := block_bound h.body
  have look (vals : Role → Option Value) (r : Role) :
      (MirLocal.overlay l.slot original vals)[l.slot r]? = some (vals r) :=
    MirLocal.overlay_lookup_opt l.slot original vals l.distinct r (hl r)
  have set (vals : Role → Option Value) (r : Role) (x : Option Value) :
      (MirLocal.overlay l.slot original vals).set! (l.slot r) x =
        MirLocal.overlay l.slot original (MirLocal.updateValues vals r x) :=
    MirLocal.overlay_set! l.slot original vals l.distinct r (hl r) x
  have look' (vals : Role → Option Value) (r : Role) (hb) :
      (MirLocal.overlay l.slot original vals)[l.slot r]'hb = vals r := by
    rw [← getElem!_pos (MirLocal.overlay l.slot original vals) (l.slot r) hb]
    exact MirLocal.overlay_lookup l.slot original vals l.distinct r (hl r)
  have set' (vals : Role → Option Value) (r : Role) (x : Option Value) :
      (MirLocal.overlay l.slot original vals).setIfInBounds (l.slot r) x =
        MirLocal.overlay l.slot original (MirLocal.updateValues vals r x) := set vals r x
  have heapSet : (H.push ⟨true, cells n value k⟩).setIfInBounds H.size
      ⟨true, (cells n value k).setIfInBounds k (some value)⟩ =
      H.push ⟨true, cells n value (k + 1)⟩ := heap_store_prefix H hk
  simp [runFor, rawTick, fetch, h.test, h.body, elem_of_some h.test,
    elem_of_some h.body, testBlock, bodyBlock, frame, loopFrame, loopValues,
    slotPlace, copy, rvalue, operand, constant, binary, write, valueType,
    advance, jump, switchValue, select, h.types, look, set, look', set', hl,
    hk, hv, bound, offset, store, ht, hb, wordBound, heapSet]

/-- Induction on remaining logical cells proves termination of the embedded
loop without fuel or a closed initial heap. -/
theorem fill_total (h : Embedded c l b) (hl : ∀ r, l.slot r < original.size)
    (hn : n ≤ 4095) (hv : value < scalarBound) (hk : k ≤ n) :
    ∃ test' dest', Steps c (.running (loopFrame l b original H n value k test dest)) []
      (.running (loopFrame l b original H n value n test' dest')) := by
  generalize he : n - k = remaining
  induction remaining generalizing k test dest with
  | zero =>
    have eq : k = n := by omega
    subst k
    exact ⟨test, dest, .nil⟩
  | succ remaining ih =>
    have lt : k < n := by omega
    have eq : n - (k + 1) = remaining := by omega
    obtain ⟨test', dest', rest⟩ := ih (by omega) eq
      (test := some (.boolean true)) (dest := some (.pointer H.size k))
    exact ⟨test', dest', by simpa using
      (steps_trans (runFor_sound (fill_iteration h hl hn lt hv)) rest)⟩

noncomputable def outputFrame (l : Layout) (b : Labels) (original : Array (Option Value))
    (H : Array Object) (n value : Nat) (dest : Option Value) : Frame :=
  frame l original (H.push ⟨true, cells n value n⟩)
    (loopValues n value H.size n (some (.boolean false)) dest) b.exit 0

/-- The fragment stops at an arbitrary enclosing continuation, without executing
its first instruction. The final failed loop test is reflected in the locals. -/
theorem exit_prefix (h : Embedded c l b) (hl : ∀ r, l.slot r < original.size) :
    runFor 2 c (.running (loopFrame l b original H n value n test dest)) =
      some ⟨.running (outputFrame l b original H n value dest), []⟩ := by
  have ht := block_bound h.test
  have look (vals : Role → Option Value) (r : Role) :
      (MirLocal.overlay l.slot original vals)[l.slot r]? = some (vals r) :=
    MirLocal.overlay_lookup_opt l.slot original vals l.distinct r (hl r)
  have set (vals : Role → Option Value) (r : Role) (x : Option Value) :
      (MirLocal.overlay l.slot original vals).set! (l.slot r) x =
        MirLocal.overlay l.slot original (MirLocal.updateValues vals r x) :=
    MirLocal.overlay_set! l.slot original vals l.distinct r (hl r) x
  have look' (vals : Role → Option Value) (r : Role) (hb) :
      (MirLocal.overlay l.slot original vals)[l.slot r]'hb = vals r := by
    rw [← getElem!_pos (MirLocal.overlay l.slot original vals) (l.slot r) hb]
    exact MirLocal.overlay_lookup l.slot original vals l.distinct r (hl r)
  have set' (vals : Role → Option Value) (r : Role) (x : Option Value) :
      (MirLocal.overlay l.slot original vals).setIfInBounds (l.slot r) x =
        MirLocal.overlay l.slot original (MirLocal.updateValues vals r x) := set vals r x
  simp [runFor, rawTick, fetch, h.test, elem_of_some h.test, testBlock,
    frame, loopFrame, outputFrame, loopValues, slotPlace, copy, rvalue, operand,
    binary, write, valueType, advance, jump, switchValue, select, h.types,
    look, set, look', set', hl, ht, h.exit]

/-- A structural code embedding plus resource/input bounds suffices to allocate
and initialize a fresh Buffer, then reach the enclosing continuation. -/
theorem terminates (h : Embedded c l b) (hl : ∀ r, l.slot r < original.size)
    (hobjects : H.size < 512)
    (hcells : (H.toList.map (fun obj => obj.cells.size)).sum + n + 1 ≤ 4096)
    (hv : value < scalarBound) :
    ∃ dest, Steps c (.running (frame l original H
      (values (some (.u64 n)) (some (.i64 value)) a2 a3 a4 a5 a6 a7 a8 a9) b.entry 0))
      [.alloc H.size (n * 8 + 8)]
      (.running (outputFrame l b original H n value dest)) := by
  have hn : n ≤ 4095 := by omega
  obtain ⟨test, dest, filled⟩ := fill_total (H := H) (k := 0)
    (test := a8) (dest := a9) h hl hn hv (by omega)
  exact ⟨dest, by simpa using (steps_trans
    (runFor_sound (initialization_prefix h hl hobjects hcells))
    (steps_trans filled (runFor_sound (exit_prefix h hl))))⟩

/-- Ordinary input frames need only initialize the two input roles. Scratch
contents are not required to be absent or to have any particular value. -/
theorem input_overlay (l : Layout) (original : Array (Option Value))
    (hn : original[l.slot 0]! = some (.u64 n))
    (hv : original[l.slot 1]! = some (.i64 value)) :
    MirLocal.overlay l.slot original
      (values (some (.u64 n)) (some (.i64 value))
        original[l.slot 2]! original[l.slot 3]! original[l.slot 4]!
        original[l.slot 5]! original[l.slot 6]! original[l.slot 7]!
        original[l.slot 8]! original[l.slot 9]!) = original := by
  apply MirLocal.overlay_same
  intro ⟨r, hr⟩
  have cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hn | exact hv | rfl

/-- The reusable entry theorem accepts the actual initial local array, preserving
all untouched locals and all earlier heap objects in its resulting frame. -/
theorem fills_from_frame (h : Embedded c l b) (hl : ∀ r, l.slot r < original.size)
    (hin : original[l.slot 0]! = some (.u64 n))
    (hvalue : original[l.slot 1]! = some (.i64 value))
    (hobjects : H.size < 512)
    (hcells : (H.toList.map (fun obj => obj.cells.size)).sum + n + 1 ≤ 4096)
    (hv : value < scalarBound) :
    ∃ dest, Steps c (.running ⟨b.entry, 0, original, H⟩)
      [.alloc H.size (n * 8 + 8)]
      (.running (outputFrame l b original H n value dest)) := by
  obtain ⟨dest, steps⟩ := terminates
    (a2 := original[l.slot 2]!) (a3 := original[l.slot 3]!)
    (a4 := original[l.slot 4]!) (a5 := original[l.slot 5]!)
    (a6 := original[l.slot 6]!) (a7 := original[l.slot 7]!)
    (a8 := original[l.slot 8]!) (a9 := original[l.slot 9]!)
    h hl hobjects hcells hv
  exact ⟨dest, by simpa only [frame, input_overlay l original hin hvalue] using steps⟩

/-- The two input slots, fresh base pointer and finished cursor remain available
to a continuation, independently of the physical slot assignment. -/
theorem output_roles (hl : ∀ r, l.slot r < original.size) :
    (outputFrame l b original H n value dest).locals[l.slot 0]! = some (.u64 n) ∧
    (outputFrame l b original H n value dest).locals[l.slot 1]! = some (.i64 value) ∧
    (outputFrame l b original H n value dest).locals[l.slot 4]! = some (.pointer H.size 0) ∧
    (outputFrame l b original H n value dest).locals[l.slot 7]! = some (.u64 n) := by
  simp only [outputFrame, frame, loopValues,
    MirLocal.overlay_lookup l.slot original _ l.distinct _ (hl _), values0, values1, values4, values7]
  trivial

theorem output_local_frame (hother : ∀ r, l.slot r ≠ slot) :
    (outputFrame l b original H n value dest).locals[slot]! = original[slot]! :=
  MirLocal.overlay_other l.slot original _ slot hother

theorem output_local_size :
    (outputFrame l b original H n value dest).locals.size = original.size := by
  simp [outputFrame, frame]

theorem output_heap_frame (hj : j < H.size) :
    (outputFrame l b original H n value dest).heap[j]? = H[j]? :=
  heap_prefix_frame H hj

theorem output_load_frame (hj : j < H.size) :
    load (outputFrame l b original H n value dest).heap j index = load H j index :=
  heap_prefix_load_frame H hj

theorem output_read (hi : i < n) :
    load (outputFrame l b original H n value dest).heap H.size i = some value :=
  filled_read H hi

theorem output_spare :
    load (outputFrame l b original H n value dest).heap H.size n = none :=
  spare_uninitialized H (Nat.le_refl n)

/-- A continuation is independently proved in the same enclosing code. It may
read, free or pass on the fresh Buffer; this rule composes its trace exactly. -/
theorem continue_after_fill (h : Embedded c l b) (hl : ∀ r, l.slot r < original.size)
    (hin : original[l.slot 0]! = some (.u64 n))
    (hvalue : original[l.slot 1]! = some (.i64 value))
    (hobjects : H.size < 512)
    (hcells : (H.toList.map (fun obj => obj.cells.size)).sum + n + 1 ≤ 4096)
    (hv : value < scalarBound)
    (target : Option Value → Machine)
    (continuation : ∀ dest, Steps c (.running (outputFrame l b original H n value dest)) events (target dest)) :
    ∃ dest, Steps c (.running ⟨b.entry, 0, original, H⟩)
      (.alloc H.size (n * 8 + 8) :: events) (target dest) := by
  obtain ⟨dest, first⟩ := fills_from_frame h hl hin hvalue hobjects hcells hv
  exact ⟨dest, by simpa using steps_trans first (continuation dest)⟩

end Jihoo.MirBuffer
