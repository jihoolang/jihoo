import Jihoo.ReferenceCalls
import Jihoo.CommonDataReference

/-! Constructor prefixes: pointer result 0, scratch 1/2, immutable child
operands 3/4, arbitrary caller locals thereafter. Block 2 receives the result;
this does not extend ReferenceCalls' unit-only internal return ABI. -/
set_option linter.unusedSimpArgs false
namespace Jihoo.TreeCreateCfg
open ReferenceCfg ReferenceCalls CommonDataReference

def arg (n : Nat) : Operand := .copy ⟨n, false⟩
def types (tail : Array Ty) : Array Ty := #[.ptr, .ptr, .i64, .ptr, .ptr] ++ tail
def body (node : Bool) (tail : Array Ty) (continuation : Block) (exit : Option Exit) : ReferenceCalls.Function :=
  ⟨⟨⟨types tail, #[
    ⟨#[], .malloc (.constant (.u64 (if node then 24 else 8))) ⟨0, false⟩ 1⟩,
    ⟨if node then #[
      ⟨⟨0, true⟩, .use (.constant (.i64 1))⟩,
      ⟨⟨1, false⟩, .offset (arg 0) (.constant (.u64 1))⟩,
      ⟨⟨2, false⟩, .pointerToWord (arg 3)⟩,
      ⟨⟨1, true⟩, .use (arg 2)⟩,
      ⟨⟨1, false⟩, .offset (arg 0) (.constant (.u64 2))⟩,
      ⟨⟨2, false⟩, .pointerToWord (arg 4)⟩,
      ⟨⟨1, true⟩, .use (arg 2)⟩]
     else #[⟨⟨0, true⟩, .use (.constant (.i64 0))⟩], .goto 2⟩,
    continuation]⟩, #[none, none, exit]⟩, #[]⟩
def stateAt (fn block : Nat) (H : ReferenceHeap.Heap) (vs : Array (Option Value))
    (ks : List Continuation) : State := ⟨fn, ⟨block, 0, vs, H⟩, ks⟩
def walk (p : Program) : Nat → State → Option (State × List Event)
  | 0, s => some (s, [])
  | n + 1, s => do
    let next ← ReferenceCalls.tick p s
    let .running t := next.machine | none
    let (u, es) ← walk p n t
    pure (u, next.events ++ es)
inductive Prefix (p : Program) : Nat → State → List Event → State → Prop where
  | nil : Prefix p 0 s [] s
  | cons : ReferenceCalls.Step p (.running s) es (.running t) →
      Prefix p n t fs u → Prefix p (n + 1) s (es ++ fs) u

theorem walk_sound (h : walk p n s = some (t, es)) : Prefix p n s es t := by
  induction n generalizing s es with
  | zero => simp [walk] at h; obtain ⟨rfl, rfl⟩ := h; exact .nil
  | succ n ih =>
    cases ht : ReferenceCalls.tick p s with
    | none => simp [walk, ht] at h
    | some next =>
      cases hm : next.machine with
      | returned _ _ => simp [walk, ht, hm] at h
      | running u =>
        cases hw : walk p n u with
        | none => simp [walk, ht, hm, hw] at h
        | some result =>
          obtain ⟨v, fs⟩ := result
          simp [walk, ht, hm, hw] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .cons (hm ▸ ReferenceCalls.tick_sound ht) (ih hw)

theorem Prefix.execute (h : Prefix p n s es t)
    (tail : ReferenceCalls.execute fuel p t = some out) :
    ReferenceCalls.execute (n + fuel) p s = some {out with events := es ++ out.events} := by
  induction h with
  | nil => simpa using tail
  | cons step _ ih =>
    simp [Nat.succ_add, ReferenceCalls.execute, ReferenceCalls.tick_complete step,
      ih tail, List.append_assoc]

def slots (a b c d e : Option Value) (tail : Array (Option Value)) := #[a,b,c,d,e] ++ tail
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem nil_prefix (installed : p[fn]? = some (body false tys continuation exit))
    (capacity : Budget H 1) :
    walk p 3 (stateAt fn 0 H (slots a b c d e vs) ks) =
      some (stateAt fn 2 (H.push ReferenceHeap.nilObject)
        (slots (some (.pointer H.size 0)) b c d e vs) ks, [.alloc H.size 8]) := by
  simp only [walk]
  simp +arith [Array.getElem?_append, BoundedMir.wordBound, ReferenceCalls.tick, installed, body, ReferenceCalls.extension,
    ReferenceCfg.tick_eq_rawTick, ReferenceCfg.rawTick, ReferenceCfg.fetch,
    ReferenceCfg.operand, ReferenceCfg.rvalue, ReferenceCfg.write,
    ReferenceCfg.valueType, ReferenceCfg.advance, ReferenceCfg.jump,
    ReferenceCfg.mallocHeap, ReferenceCalls.liftLegacy,
    ReferenceCfg.constant, BoundedMir.constant, ReferenceCfg.embedValue,
    ReferenceHeap.allocate, capacity.1, capacity.2,
    ReferenceHeap.store, ReferenceHeap.address, ReferenceHeap.validCell,
    ReferenceHeap.nilObject, BoundedMir.scalarBound, Array.replicate_succ,
    Array.set!, Array.setIfInBounds, Array.set_push, stateAt, slots, types, arg]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem node_prefix (installed : p[fn]? = some (body true tys continuation exit))
    (capacity : Budget H 3) :
    walk p 9 (stateAt fn 0 H (slots a b c (some (.pointer l 0)) (some (.pointer r 0)) vs) ks) =
      some (stateAt fn 2 (H.push (ReferenceHeap.node (.object l 0) (.object r 0)))
        (slots (some (.pointer H.size 0)) (some (.pointer H.size 2))
          (some (.referenceWord (.object r 0))) (some (.pointer l 0)) (some (.pointer r 0)) vs)
        ks, [.alloc H.size 24]) := by
  simp only [walk]
  simp +arith [Array.getElem?_append, BoundedMir.wordBound, ReferenceCalls.tick, installed, body, ReferenceCalls.extension,
    ReferenceCfg.tick_eq_rawTick, ReferenceCfg.rawTick, ReferenceCfg.fetch,
    ReferenceCfg.operand, ReferenceCfg.rvalue, ReferenceCfg.write,
    ReferenceCfg.valueType, ReferenceCfg.advance, ReferenceCfg.jump,
    ReferenceCfg.mallocHeap, ReferenceCalls.liftLegacy,
    ReferenceCfg.constant, BoundedMir.constant, ReferenceCfg.embedValue, ReferenceCfg.toRef,
    ReferenceHeap.node_allocate capacity.1 capacity.2,
    ReferenceHeap.store, ReferenceHeap.address, ReferenceHeap.validCell,
    ReferenceHeap.rawNode, ReferenceHeap.node, ReferenceHeap.pointerToWord,
    BoundedMir.scalarBound, Array.set!, Array.setIfInBounds, Array.set_push,
    stateAt, slots, types, arg]

/-- No complete return is possible with fuel consumed entirely by this prefix. -/
theorem Prefix.short_fuel (h : Prefix p n s es t) (bound : fuel ≤ n) :
    ReferenceCalls.execute fuel p s = none := by
  induction h generalizing fuel with
  | nil =>
    have : fuel = 0 := by omega
    subst fuel
    rfl
  | cons step rest ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      simp [ReferenceCalls.execute, ReferenceCalls.tick_complete step, ih (fuel := fuel) (by omega)]

theorem Prefix.steps (h : Prefix p n s es t) :
    ReferenceCalls.Steps p (.running s) es (.running t) := by
  induction h with
  | nil => exact .nil
  | cons step _ ih => exact .cons step ih

/-- Every shorter prefix exists and obeys the same actual transition relation. -/
theorem Prefix.take (h : Prefix p n s es t) (bound : m ≤ n) :
    ∃ u fs, Prefix p m s fs u := by
  induction h generalizing m with
  | nil =>
    have : m = 0 := by omega
    subst m
    exact ⟨_, [], .nil⟩
  | cons step rest ih =>
    cases m with
    | zero => exact ⟨_, [], .nil⟩
    | succ m =>
      obtain ⟨u, fs, hp⟩ := ih (m := m) (by omega)
      exact ⟨u, _, .cons step hp⟩

end Jihoo.TreeCreateCfg
