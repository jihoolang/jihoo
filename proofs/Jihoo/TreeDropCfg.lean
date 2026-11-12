import Jihoo.ReferenceCalls
import Jihoo.CommonDataReferenceDrop

/-! Fixed binary Tree Drop. Image is a proof witness only. Execution consumes
heap/root and independent instruction fuel. Native pointer casts, reuse and
whole-compiler correctness are outside this abstract reference-cell model. -/
namespace Jihoo.TreeDropCfg
open ReferenceCfg ReferenceCalls CommonDataReference

def arg (n : Nat) : Operand := .copy ⟨n, false⟩
def body : ReferenceCalls.Function := ⟨⟨⟨
  #[.ptr, .i64, .ptr, .i64, .ptr, .ptr, .unit], #[
  ⟨#[⟨⟨1, false⟩, .use (.copy ⟨0, true⟩)⟩],
    .switch (arg 1) [(0, 1), (1, 2)] 6⟩,
  ⟨#[], .free (arg 0) ⟨6, false⟩ 5⟩,
  ⟨#[⟨⟨2, false⟩, .offset (arg 0) (.constant (.u64 1))⟩,
      ⟨⟨3, false⟩, .use (.copy ⟨2, true⟩)⟩,
      ⟨⟨4, false⟩, .wordToPointer (arg 3)⟩,
      ⟨⟨2, false⟩, .offset (arg 0) (.constant (.u64 2))⟩,
      ⟨⟨3, false⟩, .use (.copy ⟨2, true⟩)⟩,
      ⟨⟨5, false⟩, .wordToPointer (arg 3)⟩], .free (arg 0) ⟨6, false⟩ 3⟩,
  ⟨#[], .ret⟩, ⟨#[], .ret⟩, ⟨#[], .ret⟩]⟩,
  #[none, none, none,
    some (.call ⟨0, #[arg 4], ⟨6, false⟩, 4⟩),
    some (.call ⟨0, #[arg 5], ⟨6, false⟩, 5⟩), some .retUnit]⟩, #[0]⟩
def program : Program := #[body]
def locals (j : Nat) : Array (Option Value) :=
  #[some (.pointer j 0), none, none, none, none, none, none]
def start (H : ReferenceHeap.Heap) (j : Nat) (ks : List Continuation := []) : State :=
  ⟨0, ⟨0, 0, locals j, H⟩, ks⟩
def run (fuel : Nat) (H : ReferenceHeap.Heap) (root : Nat) :=
  ReferenceCalls.execute fuel program (start H root)

/-- Running prefixes count instructions and check a separate stack limit. -/
def walk : Nat → Nat → State → Option (State × List Event)
  | 0, limit, s => if stackDepth s ≤ limit then some (s, []) else none
  | n + 1, limit, s => do
      if stackDepth s > limit then none else do
      let next ← ReferenceCalls.tick program s
      let .running t := next.machine | none
      let (u, es) ← walk n limit t
      pure (u, next.events ++ es)

theorem walk_add (a b limit s) : walk (a + b) limit s = (do
    let (t, es) ← walk a limit s
    let (u, fs) ← walk b limit t
    pure (u, es ++ fs)) := by
  induction a generalizing s with
  | zero =>
    simp only [Nat.zero_add, walk]
    split
    · cases h : walk b limit s <;> simp [h]
    · cases b <;> simp_all [walk]
  | succ a ih =>
    simp only [Nat.succ_add, walk]
    split <;> simp_all
    cases ht : ReferenceCalls.tick program s with
    | none => simp
    | some next =>
      cases hm : next.machine <;>
        simp [hm, Option.bind_assoc, List.append_assoc]

/-- Every active state in the actual prefix obeys the independent stack bound. -/
inductive BoundedPrefix (limit : Nat) : Nat → State → List Event → State → Prop where
  | nil : stackDepth s ≤ limit → BoundedPrefix limit 0 s [] s
  | cons : stackDepth s ≤ limit → ReferenceCalls.tick program s = some ⟨.running t, es⟩ →
      BoundedPrefix limit n t fs u → BoundedPrefix limit (n + 1) s (es ++ fs) u

theorem walk_sound (h : walk n limit s = some (t, es)) :
    BoundedPrefix limit n s es t := by
  induction n generalizing s es with
  | zero =>
    simp only [walk] at h
    split at h
    · cases Option.some.inj h; exact .nil (by assumption)
    · contradiction
  | succ n ih =>
    simp only [walk] at h
    split at h
    · contradiction
    · rename_i hb
      cases ht : ReferenceCalls.tick program s with
      | none => simp [ht] at h
      | some next =>
        cases hm : next.machine with
        | returned _ _ => simp [ht, hm] at h
        | running u =>
          cases hw : walk n limit u with
          | none => simp [ht, hm, hw] at h
          | some result =>
            obtain ⟨v, fs⟩ := result
            simp [ht, hm, hw] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .cons (by omega) (by simpa only [← hm] using ht) (ih hw)

theorem BoundedPrefix.steps (h : BoundedPrefix limit n s es t) :
    ReferenceCalls.Steps program (.running s) es (.running t) := by
  induction h with
  | nil _ => exact .nil
  | cons _ ht _ ih => exact .cons (ReferenceCalls.tick_sound ht) ih

theorem BoundedPrefix.execute (h : BoundedPrefix limit n s es t)
    (tail : ReferenceCalls.execute fuel program t = some out) :
    ReferenceCalls.execute (n + fuel) program s = some {out with events := es ++ out.events} := by
  induction h with
  | nil _ => simpa using tail
  | cons _ ht _ ih =>
    simp [Nat.succ_add, ReferenceCalls.execute, ht, ih tail, List.append_assoc]


def nilLocals (j : Nat) : Array (Option Value) :=
  #[some (.pointer j 0), some (.i64 0), none, none, none, none, some .unit]
def nodeLocals (j l r : Nat) : Array (Option Value) :=
  #[some (.pointer j 0), some (.i64 1), some (.pointer j 2),
    some (.referenceWord (.object r 0)), some (.pointer l 0), some (.pointer r 0), some .unit]
def stateAt (H : ReferenceHeap.Heap) (vs : Array (Option Value)) (block : Nat)
    (ks : List Continuation) : State := ⟨0, ⟨block, 0, vs, H⟩, ks⟩
def saved (vs : Array (Option Value)) (block : Nat) : Continuation :=
  ⟨0, block, vs, ⟨6, false⟩⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem nil_prefix (found : H[j]? = some ReferenceHeap.nilObject)
    (bound : ks.length ≤ limit) :
    walk 3 limit (start H j ks) =
      some (stateAt (retired H j ReferenceHeap.nilObject) (nilLocals j) 5 ks, [.free j]) := by
  simp [walk, ReferenceCalls.tick, program, body, ReferenceCalls.extension,
    ReferenceCfg.tick_eq_rawTick, ReferenceCfg.rawTick, ReferenceCfg.fetch,
    ReferenceCfg.operand, ReferenceCfg.load, ReferenceCfg.rvalue, ReferenceCfg.write,
    ReferenceCfg.valueType, ReferenceCfg.advance, ReferenceCfg.jump, ReferenceCfg.switchValue,
    ReferenceCfg.select, ReferenceCfg.freeHeap, ReferenceCalls.liftLegacy,
    ReferenceHeap.release, ReferenceHeap.load, ReferenceHeap.address, found,
    ReferenceHeap.nilObject, start, locals, nilLocals, stateAt, retired, arg, stackDepth, bound, Nat.not_lt.mpr bound]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem node_prefix (found : H[j]? = some (ReferenceHeap.node (.object l 0) (.object r 0)))
    (bound : ks.length ≤ limit) :
    walk 9 limit (start H j ks) =
      some (stateAt (retired H j (ReferenceHeap.node (.object l 0) (.object r 0)))
        (nodeLocals j l r) 3 ks, [.free j]) := by
  simp [walk, ReferenceCalls.tick, program, body, ReferenceCalls.extension,
    ReferenceCfg.tick_eq_rawTick, ReferenceCfg.rawTick, ReferenceCfg.fetch,
    ReferenceCfg.operand, ReferenceCfg.load, ReferenceCfg.rvalue, ReferenceCfg.write,
    ReferenceCfg.valueType, ReferenceCfg.advance, ReferenceCfg.jump, ReferenceCfg.switchValue,
    ReferenceCfg.select, ReferenceCfg.freeHeap, ReferenceCalls.liftLegacy,
    ReferenceCfg.constant, BoundedMir.constant, ReferenceCfg.embedValue, ReferenceCfg.ofRef,
    ReferenceHeap.release, ReferenceHeap.load, ReferenceHeap.address, found,
    ReferenceHeap.node, ReferenceHeap.pointerToWord, start, locals, nodeLocals, stateAt, retired,
    arg, stackDepth, bound, Nat.not_lt.mpr bound, BoundedMir.wordBound]

set_option maxRecDepth 10000 in
theorem call_left (bound : ks.length + 1 ≤ limit) :
    walk 1 limit (stateAt H (nodeLocals j l r) 3 ks) =
    some (start H l (saved (nodeLocals j l r) 4 :: ks), []) := by
  have hb : ks.length ≤ limit := by omega
  simp [walk, ReferenceCalls.tick, program, body, ReferenceCalls.extension,
    ReferenceCfg.fetch, ReferenceCalls.enter, ReferenceCalls.bindArguments,
    ReferenceCfg.initial, ReferenceCfg.write, ReferenceCfg.operand, ReferenceCfg.valueType,
    start, locals, nodeLocals, stateAt, saved, arg, stackDepth, bound,
    Nat.not_lt.mpr hb, Array.replicate_succ]

set_option maxRecDepth 10000 in
theorem call_right (bound : ks.length + 1 ≤ limit) :
    walk 1 limit (stateAt H (nodeLocals j l r) 4 ks) =
    some (start H r (saved (nodeLocals j l r) 5 :: ks), []) := by
  have hb : ks.length ≤ limit := by omega
  simp [walk, ReferenceCalls.tick, program, body, ReferenceCalls.extension,
    ReferenceCfg.fetch, ReferenceCalls.enter, ReferenceCalls.bindArguments,
    ReferenceCfg.initial, ReferenceCfg.write, ReferenceCfg.operand, ReferenceCfg.valueType,
    start, locals, nodeLocals, stateAt, saved, arg, stackDepth, bound,
    Nat.not_lt.mpr hb, Array.replicate_succ]

set_option maxRecDepth 10000 in
theorem return_child (bound : ks.length + 1 ≤ limit) (blockBound : b < 6) :
    walk 1 limit (stateAt H vs 5 (saved (nodeLocals j l r) b :: ks)) =
    some (stateAt H (nodeLocals j l r) b ks, []) := by
  have hb : ks.length ≤ limit := by omega
  simp [walk, ReferenceCalls.tick, program, body, ReferenceCalls.extension,
    ReferenceCfg.fetch, ReferenceCalls.leave, ReferenceCfg.write, ReferenceCfg.valueType,
    nodeLocals, stateAt, saved, stackDepth, hb, Nat.not_lt.mpr bound,
    Nat.not_le.mpr blockBound]

def finalLocals : Image → Array (Option Value)
  | .nil j => nilLocals j
  | .node _ j l r => nodeLocals j l.target r.target
/-- Excludes the last return instruction. -/
def ticks : Image → Nat
  | .nil _ => 3
  | .node _ _ l r => 13 + ticks l + ticks r

/-- The witness shapes only this induction, never the fixed executable code.
The prefix works under arbitrary suspended callers and leaves them unchanged. -/
theorem tree_prefix (layout : Layout H i) (unique : i.ids.Nodup)
    (bound : ks.length + i.depth ≤ limit) :
    ∃ K, walk (ticks i) limit (start H i.target ks) =
      some (stateAt K (finalLocals i) 5 ks, i.ids.map HeapLifecycle.Event.free) ∧ Frees H i.ids K := by
  induction i generalizing H ks with
  | nil j =>
    obtain ⟨_, freed, _⟩ := empty_case_total layout
    refine ⟨retired H j ReferenceHeap.nilObject, ?_, .cons freed .nil⟩
    exact nil_prefix (ks := ks) (limit := limit) layout (by simp [Image.depth] at bound; omega)
  | node x j l r ihl ihr =>
    have bounds : (ks.length + 1) + l.depth ≤ limit ∧
        (ks.length + 1) + r.depth ≤ limit := by
      simp only [Image.depth] at bound
      omega
    have hb : ks.length + 1 ≤ limit := by omega
    obtain ⟨rootApart, children⟩ := List.nodup_cons.mp unique
    obtain ⟨ul, ur, apart⟩ := List.nodup_append.mp children
    have release : ReferenceHeap.release H (.object j 0) =
        some (retired H j (Image.node x j l r).object) :=
      ReferenceHeap.Frame.release_success_iff.mpr ⟨_, layout.1, rfl, rfl, rfl⟩
    have ll : Layout (retired H j (Image.node x j l r).object) l :=
      layout.2.1.congr (fun k hk => ReferenceHeap.Frame.release_agree release k
        (fun eq => rootApart (List.mem_append_left _ (eq ▸ hk))))
    obtain ⟨M, leftRun, leftFrees⟩ := ihl ll ul
      (ks := saved (nodeLocals j l.target r.target) 4 :: ks) bounds.1
    have rl : Layout M r := by
      apply layout.2.2.congr
      intro k hk
      rw [leftFrees.frame (fun hl => apart k hl k hk rfl)]
      exact ReferenceHeap.Frame.release_agree release k
        (fun eq => rootApart (List.mem_append_right _ (eq ▸ hk)))
    obtain ⟨K, rightRun, rightFrees⟩ := ihr rl ur
      (ks := saved (nodeLocals j l.target r.target) 5 :: ks) bounds.2
    refine ⟨K, ?_, .cons release (leftFrees.append rightFrees)⟩
    have count : ticks (.node x j l r) =
        9 + (1 + (ticks l + (1 + (1 + (ticks r + 1))))) := by simp [ticks]; omega
    simp only [Image.target]
    simp only [Image.object] at leftRun
    rw [count, walk_add, node_prefix (ks := ks) (limit := limit) layout.1 (by omega)]
    simp only [bind, Option.bind_some]
    rw [walk_add, call_left hb]
    simp only [bind, Option.bind_some]
    rw [walk_add, leftRun]
    simp only [bind, Option.bind_some]
    rw [walk_add, return_child hb (by decide : 4 < 6)]
    simp only [bind, Option.bind_some]
    rw [walk_add, call_right hb]
    simp only [bind, Option.bind_some]
    rw [walk_add, rightRun]
    simp only [bind, Option.bind_some]
    rw [return_child hb (by decide : 5 < 6)]
    simp [finalLocals, Image.ids, List.map_append]

theorem top_return (fuel H vs) :
    ReferenceCalls.execute (fuel + 1) program (stateAt H vs 5 []) =
      some ⟨.unit, stateAt H vs 5 [], []⟩ := by
  simp [ReferenceCalls.execute, ReferenceCalls.tick, program, body,
    ReferenceCalls.extension, ReferenceCfg.fetch, ReferenceCalls.leave, stateAt]

/-- Independent instruction fuel, not a recursion-depth budget. -/
theorem total (layout : Layout H i) (unique : i.ids.Nodup)
    (depth : i.depth ≤ limit) (fuelBound : ticks i + 1 ≤ fuel) :
    ∃ K, run fuel H i.target =
      some ⟨.unit, stateAt K (finalLocals i) 5 [], i.ids.map HeapLifecycle.Event.free⟩ ∧
      Frees H i.ids K ∧
      BoundedPrefix limit (ticks i) (start H i.target)
        (i.ids.map HeapLifecycle.Event.free) (stateAt K (finalLocals i) 5 []) := by
  obtain ⟨K, pre, frees⟩ := tree_prefix (ks := []) layout unique (by simpa using depth)
  have certified := walk_sound pre
  have finish := certified.execute (top_return (fuel - (ticks i + 1)) K (finalLocals i))
  have eq : ticks i + (fuel - (ticks i + 1) + 1) = fuel := by omega
  refine ⟨K, ?_, frees, certified⟩
  simpa [eq, run] using finish

theorem frees_unique (a : Frees H ids K) (b : Frees H ids L) : K = L := by
  induction a with
  | nil => cases b; rfl
  | cons ha _ ih =>
    cases b with
    | cons hb tail =>
      have eq := Option.some.inj (ha.symm.trans hb)
      subst eq
      exact ih tail

/-- Exact connection to #192's heap interpreter, proved after CFG totality. -/
theorem heap_correspondence (layout : Layout H i) (unique : i.ids.Nodup)
    (depth : i.depth ≤ stackLimit) (dropDepth : i.depth ≤ recursionFuel)
    (steps : ticks i + 1 ≤ stepFuel) :
    ∃ K, run stepFuel H i.target =
      some ⟨.unit, stateAt K (finalLocals i) 5 [], i.ids.map HeapLifecycle.Event.free⟩ ∧
      drop H (.object i.target 0) recursionFuel = some (K, i.ids) ∧
      (∀ j, K[j]? = if j ∈ i.ids then H[j]?.map deadObject else H[j]?) := by
  obtain ⟨K, cfg, frees, _⟩ := total layout unique depth steps
  obtain ⟨L, heap, other⟩ := drop_total layout unique dropDepth
  have eq := frees_unique frees other
  subst L
  exact ⟨K, cfg, heap, frees.effect unique⟩

/-- Unit return restores arbitrary suspended locals, changing only destination 6.
No callee heap snapshot is restored. -/
theorem caller_restore (space : 6 < caller.size) (blockBound : b < 6) :
    ReferenceCalls.tick program (stateAt H vs 5 (saved caller b :: ks)) =
      some ⟨.running (stateAt H (caller.set! 6 (some .unit)) b ks), []⟩ := by
  simp [ReferenceCalls.tick, program, body, ReferenceCalls.extension, ReferenceCfg.fetch,
    ReferenceCalls.leave, ReferenceCfg.write, ReferenceCfg.valueType, stateAt, saved,
    space, Nat.not_le.mpr blockBound]

theorem caller_other_local (caller : Array (Option Value)) (different : slot ≠ 6) :
    (caller.set! 6 (some Value.unit))[slot]? = caller[slot]? := by
  unfold Array.set! Array.setIfInBounds
  split <;> simp [Ne.symm different]

theorem steps_append (a : ReferenceCalls.Steps program m es n)
    (b : ReferenceCalls.Steps program n fs t) :
    ReferenceCalls.Steps program m (es ++ fs) t := by
  induction a with
  | nil => exact b
  | cons head _ ih => simpa [List.append_assoc] using ReferenceCalls.Steps.cons head (ih b)

/-- Entire subtree execution and return to a suspended caller of function 0.
The caller may have arbitrary locals; only its unit destination is updated. -/
theorem caller_total (layout : Layout H i) (unique : i.ids.Nodup)
    (depth : ks.length + 1 + i.depth ≤ limit)
    (space : 6 < caller.size) (blockBound : b < 6) :
    ∃ K, ReferenceCalls.Steps program
      (.running (start H i.target (saved caller b :: ks)))
      (i.ids.map HeapLifecycle.Event.free)
      (.running (stateAt K (caller.set! 6 (some .unit)) b ks)) ∧ Frees H i.ids K := by
  obtain ⟨K, pre, frees⟩ := tree_prefix (ks := saved caller b :: ks) (limit := limit) layout unique depth
  refine ⟨K, ?_, frees⟩
  have tail := ReferenceCalls.Steps.cons
    (ReferenceCalls.tick_sound (caller_restore (H := K) (vs := finalLocals i)
      (ks := ks) space blockBound)) ReferenceCalls.Steps.nil
  simpa using steps_append (walk_sound pre).steps tail

open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime
/-- Source Destroy, heap Drop and actual fixed CFG share the same target effect.
Nil shells are additional target resources, not source frees or identical IDs. -/
theorem destroy_correspondence (related : Related s H i)
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (i.source.owners ++ frame))
    (depth : i.depth ≤ stackLimit) (dropDepth : i.depth ≤ recursionFuel)
    (steps : ticks i + 1 ≤ stepFuel) :
    ∃ t K, CommonData.Destroy (root i.source) s (i.source.owners.map HeapLeases.Event.free) t ∧
      HeapLeases.Steps s.buffers.heap (i.source.owners.map HeapLeases.Event.free) t.buffers.heap ∧
      Valid t.buffers.heap ∧ Owns t.buffers.heap frame ∧
      run stepFuel H i.target =
        some ⟨.unit, stateAt K (finalLocals i) 5 [], i.ids.map HeapLifecycle.Event.free⟩ ∧
      drop H (.object i.target 0) recursionFuel = some (K, i.ids) ∧
      (∀ j, K[j]? = if j ∈ i.ids then H[j]?.map deadObject else H[j]?) ∧
      i.pairs.map Prod.fst = i.source.owners ∧
      (∀ j, i.ids.count j = (i.pairs.map Prod.snd).count j + i.nils.count j) ∧
      i.nils.length = i.source.owners.length + 1 := by
  obtain ⟨t, source, sourceSteps, vt, kept⟩ := CommonData.destroy_total related.fields valid owned
  obtain ⟨K, cfg, heap, effect⟩ := heap_correspondence related.layout related.distinct depth dropDepth steps
  exact ⟨t, K, source, sourceSteps, vt, kept, cfg, heap, effect,
    source_pairs i, resource_count i, nil_count i⟩

theorem instruction_count (i : Image) : ticks i + 1 = 16 * i.source.owners.length + 4 := by
  induction i <;> simp_all [ticks, Image.source, Tree.owners] <;> omega

end Jihoo.TreeDropCfg
