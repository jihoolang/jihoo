import Jihoo.TreeCreateCorrectness

/-! Relocatable in-function constructor fragments. Sources are read by actual
copy instructions, not bound by a call ABI. Two fresh temporaries implement a
parallel child move even for cycles or source/destination overlap. -/
set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace Jihoo.TreeCreateRelocation
open ReferenceCfg ReferenceCalls CommonDataReference TreeCreateCfg

structure Slots where
  result : Nat
  address : Nat
  word : Nat
  left : Nat
  right : Nat
  tempLeft : Nat
  tempRight : Nat
  deriving DecidableEq, Repr

def Slots.writes (q : Slots) : List Nat :=
  [q.result, q.address, q.word, q.left, q.right, q.tempLeft, q.tempRight]

def move (dst src : Nat) : Stmt := ⟨⟨dst, false⟩, .use (arg src)⟩
def moves (q : Slots) (left right : Nat) : Array Stmt :=
  #[move q.tempLeft left, move q.tempRight right,
    move q.left q.tempLeft, move q.right q.tempRight]
def entry (q : Slots) (node : Bool) (left right build : Nat) : Block :=
  ⟨if node then moves q left right else #[],
    .malloc (.constant (.u64 (if node then 24 else 8))) ⟨q.result, false⟩ build⟩
def build (q : Slots) (node : Bool) (cont : Nat) : Block :=
  ⟨if node then #[
      ⟨⟨q.result, true⟩, .use (.constant (.i64 1))⟩,
      ⟨⟨q.address, false⟩, .offset (arg q.result) (.constant (.u64 1))⟩,
      ⟨⟨q.word, false⟩, .pointerToWord (arg q.left)⟩,
      ⟨⟨q.address, true⟩, .use (arg q.word)⟩,
      ⟨⟨q.address, false⟩, .offset (arg q.result) (.constant (.u64 2))⟩,
      ⟨⟨q.word, false⟩, .pointerToWord (arg q.right)⟩,
      ⟨⟨q.address, true⟩, .use (arg q.word)⟩]
    else #[⟨⟨q.result, true⟩, .use (.constant (.i64 0))⟩], .goto cont⟩

/-- Only the two prefix blocks are constrained. The continuation and all other
caller blocks/exits remain arbitrary. Safe placement requires distinct blocks. -/
structure Placement (f : ReferenceCalls.Function) (q : Slots) (node : Bool)
    (left right start work cont : Nat) : Prop where
  entryBlock : f.code.base.blocks[start]? = some (entry q node left right work)
  buildBlock : f.code.base.blocks[work]? = some (build q node cont)
  entryExit : (f.code.exits[start]?).join = none
  buildExit : (f.code.exits[work]?).join = none
  workBound : work < f.code.base.blocks.size
  contBound : cont < f.code.base.blocks.size
  distinct : [start, work, cont].Nodup

/-- Scratch and child destinations are pairwise distinct; both temporaries
are fresh for both sources. Sources may otherwise alias ANY destination. -/
structure Safe (f : ReferenceCalls.Function) (q : Slots) (vs : Array (Option Value))
    (left right : Nat) : Prop where
  distinct : q.writes.Nodup
  bounds : ∀ k ∈ q.writes, k < vs.size
  types : ∀ k ∈ q.writes, f.code.base.locals[k]? = some (if k = q.word then .i64 else .ptr)
  freshLL : q.tempLeft ≠ left
  freshLR : q.tempLeft ≠ right
  freshRL : q.tempRight ≠ left
  freshRR : q.tempRight ≠ right

def copied (q : Slots) (vs : Array (Option Value)) (l r : Value) :=
  (((vs.set! q.tempLeft (some l)).set! q.tempRight (some r)).set! q.left (some l)).set! q.right (some r)
def resultLocals (q : Slots) (vs : Array (Option Value)) (H : ReferenceHeap.Heap) (l r : Nat) :=
  (((copied q vs (.pointer l 0) (.pointer r 0)).set! q.result (some (.pointer H.size 0))).set!
    q.address (some (.pointer H.size 2))).set! q.word (some (.referenceWord (.object r 0)))

theorem nil_prefix (installed : p[fn]? = some f)
    (place : Placement f q false left right start work cont)
    (resultType : f.code.base.locals[q.result]? = some .ptr)
    (resultBound : q.result < vs.size) (capacity : Budget H 1) :
    walk p 3 (stateAt fn start H vs ks) =
      some (stateAt fn cont (H.push ReferenceHeap.nilObject)
        (vs.set! q.result (some (.pointer H.size 0))) ks, [.alloc H.size 8]) := by
  rcases place with ⟨he, hb, ee, eb, bw, bn, _⟩
  obtain ⟨_, hbe⟩ := Array.getElem_of_getElem? hb
  obtain ⟨_, hee⟩ := Array.getElem_of_getElem? he
  simp only [walk]
  simp +arith [ReferenceCalls.tick, installed, ReferenceCalls.extension,
    ReferenceCfg.tick_eq_rawTick, ReferenceCfg.rawTick, ReferenceCfg.fetch,
    ReferenceCfg.operand, ReferenceCfg.rvalue, ReferenceCfg.write,
    ReferenceCfg.valueType, ReferenceCfg.advance, ReferenceCfg.jump,
    ReferenceCfg.mallocHeap, ReferenceCalls.liftLegacy,
    ReferenceCfg.constant, BoundedMir.constant, ReferenceCfg.embedValue,
    ReferenceHeap.allocate, capacity.1, capacity.2,
    ReferenceHeap.store, ReferenceHeap.address, ReferenceHeap.validCell,
    ReferenceHeap.nilObject, BoundedMir.scalarBound, BoundedMir.wordBound,
    Array.replicate_succ, stateAt, entry, build, arg, he, hb, hee, hbe, ee, eb, bw, bn,
    resultType, resultBound, Array.set!, Array.setIfInBounds, Array.set_push]

attribute [local irreducible] walk resultLocals

theorem node_prefix (installed : p[fn]? = some f)
    (place : Placement f q true left right start work cont)
    (safe : Safe f q vs left right)
    (hl : (vs[left]?).join = some (.pointer l 0))
    (hr : (vs[right]?).join = some (.pointer r 0))
    (capacity : Budget H 3) :
    walk p 13 (stateAt fn start H vs ks) =
      some (stateAt fn cont (H.push (ReferenceHeap.node (.object l 0) (.object r 0)))
        (resultLocals q vs H l r) ks, [.alloc H.size 24]) := by
  rcases place with ⟨he, hb, ee, eb, bw, bn, _⟩
  obtain ⟨_, hbe⟩ := Array.getElem_of_getElem? hb
  obtain ⟨_, hee⟩ := Array.getElem_of_getElem? he
  rcases safe with ⟨hd, bounds, types, fll, flr, frl, frr⟩
  simp only [Slots.writes, List.nodup_cons, List.mem_cons, List.mem_singleton,
    not_or, List.nodup_nil, List.not_mem_nil, not_false_eq_true, and_true] at hd
  rcases hd with ⟨⟨d01,d02,d03,d04,d05,d06⟩,⟨d12,d13,d14,d15,d16⟩,
    ⟨d23,d24,d25,d26⟩,⟨d34,d35,d36⟩,⟨d45,d46⟩,d56⟩
  have br := bounds q.result (by simp [Slots.writes])
  have ba := bounds q.address (by simp [Slots.writes])
  have bwrd := bounds q.word (by simp [Slots.writes])
  have bl := bounds q.left (by simp [Slots.writes])
  have brr := bounds q.right (by simp [Slots.writes])
  have btl := bounds q.tempLeft (by simp [Slots.writes])
  have btr := bounds q.tempRight (by simp [Slots.writes])
  have tr := types q.result (by simp [Slots.writes])
  have ta := types q.address (by simp [Slots.writes])
  have tw := types q.word (by simp [Slots.writes])
  have tl := types q.left (by simp [Slots.writes])
  have tR := types q.right (by simp [Slots.writes])
  have ttl := types q.tempLeft (by simp [Slots.writes])
  have ttr := types q.tempRight (by simp [Slots.writes])
  simp [d01, d02, d03, d04, d05, d06, d12, d13, d14, d15, d16, d23, d24, d25, d26, d34, d35, d36, d45, d46, d56, Ne.symm d01, Ne.symm d02, Ne.symm d03, Ne.symm d04, Ne.symm d05, Ne.symm d06, Ne.symm d12, Ne.symm d13, Ne.symm d14, Ne.symm d15, Ne.symm d16, Ne.symm d23, Ne.symm d24, Ne.symm d25, Ne.symm d26, Ne.symm d34, Ne.symm d35, Ne.symm d36, Ne.symm d45, Ne.symm d46, Ne.symm d56] at tr ta tw tl tR ttl ttr
  repeat
    (conv => lhs; rw [walk]
     simp [ReferenceCalls.tick, installed, ReferenceCalls.extension,
    ReferenceCfg.tick_eq_rawTick, ReferenceCfg.rawTick, ReferenceCfg.fetch,
    ReferenceCfg.operand, ReferenceCfg.rvalue, ReferenceCfg.write,
    ReferenceCfg.valueType, ReferenceCfg.advance, ReferenceCfg.jump,
    ReferenceCfg.mallocHeap, ReferenceCalls.liftLegacy,
    ReferenceCfg.constant, BoundedMir.constant, ReferenceCfg.embedValue, ReferenceCfg.toRef,
    ReferenceHeap.node_allocate capacity.1 capacity.2,
    ReferenceHeap.store, ReferenceHeap.address, ReferenceHeap.validCell,
    ReferenceHeap.rawNode, ReferenceHeap.node, ReferenceHeap.pointerToWord,
    BoundedMir.scalarBound, BoundedMir.wordBound,
    Array.set_push, stateAt, entry, build, moves, move, arg, he, hb, hee, hbe, ee, eb, bw, bn,
    br, ba, bwrd, bl, brr, btl, btr, tr, ta, tw, tl, tR, ttl, ttr,
    hl, hr, fll, flr, frl, frr, Ne.symm fll, Ne.symm flr, Ne.symm frl, Ne.symm frr,
    d01, d02, d03, d04, d05, d06, d12, d13, d14, d15, d16, d23, d24, d25, d26, d34, d35, d36, d45, d46, d56, Ne.symm d01, Ne.symm d02, Ne.symm d03, Ne.symm d04, Ne.symm d05, Ne.symm d06, Ne.symm d12, Ne.symm d13, Ne.symm d14, Ne.symm d15, Ne.symm d16, Ne.symm d23, Ne.symm d24, Ne.symm d25, Ne.symm d26, Ne.symm d34, Ne.symm d35, Ne.symm d36, Ne.symm d45, Ne.symm d46, Ne.symm d56])
  simp [resultLocals, copied,
    br, ba, bwrd, bl, brr, btl, btr]
  constructor
  · rw [Array.setIfInBounds_comm _ _ (Ne.symm d12)]
    simp
  · simp [Array.setIfInBounds, Array.set_push]

end Jihoo.TreeCreateRelocation
