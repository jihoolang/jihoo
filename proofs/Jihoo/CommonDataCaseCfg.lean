import Jihoo.ReferenceCalls
import Jihoo.CommonDataReference

/-! A fixed binary Tree Case entry prefix. The ABI reserves locals 0–6:
root, tag, field address, provenance word, left, right, unit. Body blocks
are supplied independently; Image is used only by the correspondence proof.
Integration obligations: reserve this ABI away from retained live locals;
map source's newest [right,left] bindings to slots [5,4]; relocate blocks
0–4 and their edges together; carry the pending parent and revoke its
source aliases until a separately proved finish. The supplied body blocks
are not executed here. No branch-body safety, native cast correctness or
reuse claim is made. No shared compiler/context imports are extended. -/
namespace Jihoo.CommonDataCaseCfg
open ReferenceCfg ReferenceCalls CommonDataReference

def arg (n : Nat) : Operand := .copy ⟨n, false⟩
/-- Prefix destinations are distinct from the root and from one another,
except for intentional reuse of address/word temporaries. -/
def body (nilBody nodeBody : Block) : ReferenceCalls.Function := ⟨⟨⟨
  #[.ptr, .i64, .ptr, .i64, .ptr, .ptr, .unit], #[
  ⟨#[⟨⟨1, false⟩, .use (.copy ⟨0, true⟩)⟩],
    .switch (arg 1) [(0, 1), (1, 2)] 5⟩,
  ⟨#[], .free (arg 0) ⟨6, false⟩ 3⟩,
  ⟨#[⟨⟨2, false⟩, .offset (arg 0) (.constant (.u64 1))⟩,
      ⟨⟨3, false⟩, .use (.copy ⟨2, true⟩)⟩,
      ⟨⟨4, false⟩, .wordToPointer (arg 3)⟩,
      ⟨⟨2, false⟩, .offset (arg 0) (.constant (.u64 2))⟩,
      ⟨⟨3, false⟩, .use (.copy ⟨2, true⟩)⟩,
      ⟨⟨5, false⟩, .wordToPointer (arg 3)⟩], .goto 4⟩,
  nilBody, nodeBody]⟩, #[]⟩, #[]⟩
def program (nb cb : Block) : Program := #[body nb cb]
def stateAt (H : ReferenceHeap.Heap) (vs : Array (Option Value)) (block : Nat)
    (ks : List Continuation) : State := ⟨0, ⟨block, 0, vs, H⟩, ks⟩

variable (nb cb : Block)
/-- Running prefixes count instructions and check a separate stack limit. -/
def walk (nb cb : Block) : Nat → Nat → State → Option (State × List Event)
  | 0, limit, s => if stackDepth s ≤ limit then some (s, []) else none
  | n + 1, limit, s => do
      if stackDepth s > limit then none else do
      let next ← ReferenceCalls.tick (program nb cb) s
      let .running t := next.machine | none
      let (u, es) ← walk nb cb n limit t
      pure (u, next.events ++ es)

theorem walk_add (a b limit s) : walk nb cb (a + b) limit s = (do
    let (t, es) ← walk nb cb a limit s
    let (u, fs) ← walk nb cb b limit t
    pure (u, es ++ fs)) := by
  induction a generalizing s with
  | zero =>
    simp only [Nat.zero_add, walk]
    split
    · cases h : walk nb cb b limit s <;> simp [h]
    · cases b <;> simp_all [walk]
  | succ a ih =>
    simp only [Nat.succ_add, walk]
    split <;> simp_all
    cases ht : ReferenceCalls.tick (program nb cb) s with
    | none => simp
    | some next =>
      cases hm : next.machine <;>
        simp [hm, Option.bind_assoc, List.append_assoc]

/-- Every active state in the actual prefix obeys the independent stack bound. -/
inductive BoundedPrefix (nb cb : Block) (limit : Nat) : Nat → State → List Event → State → Prop where
  | nil : stackDepth s ≤ limit → BoundedPrefix nb cb limit 0 s [] s
  | cons : stackDepth s ≤ limit → ReferenceCalls.tick (program nb cb) s = some ⟨.running t, es⟩ →
      BoundedPrefix nb cb limit n t fs u → BoundedPrefix nb cb limit (n + 1) s (es ++ fs) u

theorem walk_sound (h : walk nb cb n limit s = some (t, es)) :
    BoundedPrefix nb cb limit n s es t := by
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
      cases ht : ReferenceCalls.tick (program nb cb) s with
      | none => simp [ht] at h
      | some next =>
        cases hm : next.machine with
        | returned _ _ => simp [ht, hm] at h
        | running u =>
          cases hw : walk nb cb n limit u with
          | none => simp [ht, hm, hw] at h
          | some result =>
            obtain ⟨v, fs⟩ := result
            simp [ht, hm, hw] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .cons (by omega) (by simpa only [← hm] using ht) (ih hw)

theorem BoundedPrefix.steps (h : BoundedPrefix nb cb limit n s es t) :
    ReferenceCalls.Steps (program nb cb) (.running s) es (.running t) := by
  induction h with
  | nil _ => exact .nil
  | cons _ ht _ ih => exact .cons (ReferenceCalls.tick_sound ht) ih

theorem BoundedPrefix.execute (h : BoundedPrefix nb cb limit n s es t)
    (tail : ReferenceCalls.execute fuel (program nb cb) t = some out) :
    ReferenceCalls.execute (n + fuel) (program nb cb) s = some {out with events := es ++ out.events} := by
  induction h with
  | nil _ => simpa using tail
  | cons _ ht _ ih =>
    simp [Nat.succ_add, ReferenceCalls.execute, ht, ih tail, List.append_assoc]



def nilLocals (vs : Array (Option Value)) :=
  (vs.set! 1 (some (.i64 0))).set! 6 (some .unit)
def nodeLocals (vs : Array (Option Value)) (j l r : Nat) :=
  ((((((vs.set! 1 (some (.i64 1))).set! 2 (some (.pointer j 1))).set! 3
    (some (.referenceWord (.object l 0)))).set! 4 (some (.pointer l 0))).set! 2
    (some (.pointer j 2))).set! 3 (some (.referenceWord (.object r 0)))).set! 5
    (some (.pointer r 0))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem nil_prefix (found : H[j]? = some ReferenceHeap.nilObject)
    (root : vs[0]? = some (some (.pointer j 0))) (space : 7 ≤ vs.size)
    (bound : ks.length ≤ limit) :
    walk nb cb 3 limit (stateAt H vs 0 ks) =
      some (stateAt (retired H j ReferenceHeap.nilObject) (nilLocals vs) 3 ks, [.free j]) := by
  have h0 : 0 < vs.size := by omega
  have hroot : vs[0] = some (.pointer j 0) := by simpa [h0] using root
  have h1 : 1 < vs.size := by omega
  have h6 : 6 < vs.size := by omega
  simp [walk, ReferenceCalls.tick, program, body, ReferenceCalls.extension,
    ReferenceCfg.tick_eq_rawTick, ReferenceCfg.rawTick, ReferenceCfg.fetch,
    ReferenceCfg.operand, ReferenceCfg.load, ReferenceCfg.rvalue, ReferenceCfg.write,
    ReferenceCfg.valueType, ReferenceCfg.advance, ReferenceCfg.jump, ReferenceCfg.switchValue,
    ReferenceCfg.select, ReferenceCfg.freeHeap, ReferenceCalls.liftLegacy,
    ReferenceHeap.release, ReferenceHeap.load, ReferenceHeap.address, found,
    ReferenceHeap.nilObject, nilLocals, stateAt, retired, arg, stackDepth, bound,
    Nat.not_lt.mpr bound, Array.set!, Array.setIfInBounds, h0, h1, h6, hroot]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem node_prefix (found : H[j]? = some (ReferenceHeap.node (.object l 0) (.object r 0)))
    (root : vs[0]? = some (some (.pointer j 0))) (space : 7 ≤ vs.size)
    (bound : ks.length ≤ limit) :
    walk nb cb 9 limit (stateAt H vs 0 ks) =
      some (stateAt H (nodeLocals vs j l r) 4 ks, []) := by
  have h0 : 0 < vs.size := by omega
  have hroot : vs[0] = some (.pointer j 0) := by simpa [h0] using root
  have h1 : 1 < vs.size := by omega
  have h2 : 2 < vs.size := by omega
  have h3 : 3 < vs.size := by omega
  have h4 : 4 < vs.size := by omega
  have h5 : 5 < vs.size := by omega
  simp [walk, ReferenceCalls.tick, program, body, ReferenceCalls.extension,
    ReferenceCfg.tick_eq_rawTick, ReferenceCfg.rawTick, ReferenceCfg.fetch,
    ReferenceCfg.operand, ReferenceCfg.load, ReferenceCfg.rvalue, ReferenceCfg.write,
    ReferenceCfg.valueType, ReferenceCfg.advance, ReferenceCfg.jump, ReferenceCfg.switchValue,
    ReferenceCfg.select, ReferenceCfg.freeHeap, ReferenceCalls.liftLegacy,
    ReferenceCfg.constant, BoundedMir.constant, ReferenceCfg.embedValue, ReferenceCfg.ofRef,
    ReferenceHeap.release, ReferenceHeap.load, ReferenceHeap.address, found,
    ReferenceHeap.node, ReferenceHeap.pointerToWord, nodeLocals, stateAt,
    arg, stackDepth, bound, Nat.not_lt.mpr bound, BoundedMir.wordBound,
    Array.set!, Array.setIfInBounds, h0, h1, h2, h3, h4, h5, hroot]


/-- A fuel-limited observation of a caller-selected number of actual ticks,
not an automatic branch-entry executor. The 3/9 entry theorems below derive
that this observation ends at the chosen body, without running that body. -/
def runPrefix (fuel steps limit : Nat) (s : State) :=
  if steps ≤ fuel then walk nb cb steps limit s else none

/-- Source entry inspects the actual environment and stored fields. Empty
entry stutters; a Node entry binds children and records a pending parent. -/
def sourceEnter (s : CommonData.State) (env : List RecursiveLexicalFields.Value)
    (index ghosts : Nat) : Option (List RecursiveLexicalFields.Value × Option Nat) := do
  match ← env[index]? with
  | .data none => pure (env, none)
  | .data (some _) => do
    let (opened, parent) ← RecursiveLexicalFields.enter s.recursive env index ghosts
    pure (opened, some parent)
  | _ => none

theorem node_locals (space : 7 ≤ vs.size) :
    (nodeLocals vs j l r)[4]? = some (some (.pointer l 0)) ∧
    (nodeLocals vs j l r)[5]? = some (some (.pointer r 0)) := by
  have h4 : 4 < vs.size := by omega
  have h5 : 5 < vs.size := by omega
  simp only [nodeLocals, Array.set!, Array.getElem?_setIfInBounds,
    Array.size_setIfInBounds]
  simp [h4, h5]

theorem node_frame (outside : k ∉ [1,2,3,4,5]) :
    (nodeLocals vs j l r)[k]? = vs[k]? := by
  have h1 : 1 ≠ k := by intro h; subst k; simp at outside
  have h2 : 2 ≠ k := by intro h; subst k; simp at outside
  have h3 : 3 ≠ k := by intro h; subst k; simp at outside
  have h4 : 4 ≠ k := by intro h; subst k; simp at outside
  have h5 : 5 ≠ k := by intro h; subst k; simp at outside
  simp only [nodeLocals, Array.set!, Array.getElem?_setIfInBounds,
    h1, h2, h3, h4, h5, ↓reduceIte]

theorem nil_frame (tagApart : k ≠ 1) (unitApart : k ≠ 6) :
    (nilLocals vs)[k]? = vs[k]? := by
  simp only [nilLocals, Array.set!, Array.getElem?_setIfInBounds,
    Ne.symm tagApart, Ne.symm unitApart, ↓reduceIte]

open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime
/-- Joint entry result: success is derived from Related and the actual
source lookup / target operand connection. The parent remains a live pending
shell; neither side frees anything in this Node prefix. -/
theorem node_entry (related : Related s H (.node x j l r))
    (selected : env[index]? = some (.data (some x)))
    (connected : vs[0]? = some (some (.pointer j 0))) (space : 7 ≤ vs.size)
    (bound : ks.length ≤ limit) (fuelEnough : 9 ≤ fuel) :
    sourceEnter s env index ghosts = some
      (RecursiveLexicalFields.bindValues ghosts ⟨root l.source, root r.source⟩ env, some x) ∧
    runPrefix nb cb fuel 9 limit (stateAt H vs 0 ks) =
      some (stateAt H (nodeLocals vs j l.target r.target) 4 ks, []) ∧
    BoundedPrefix nb cb limit 9 (stateAt H vs 0 ks) []
      (stateAt H (nodeLocals vs j l.target r.target) 4 ks) ∧
    (nodeLocals vs j l.target r.target)[4]? = some (some (.pointer l.target 0)) ∧
    (nodeLocals vs j l.target r.target)[5]? = some (some (.pointer r.target 0)) ∧
    H[j]? = some (ReferenceHeap.node (.object l.target 0) (.object r.target 0)) ∧
    Related s H l ∧ Related s H r := by
  obtain ⟨entered, _, left, right⟩ := case_open_total related selected (ghosts := ghosts)
  have pre := node_prefix nb cb related.layout.1 connected space bound
  exact ⟨by simp [sourceEnter, selected, entered],
    by simpa [runPrefix, fuelEnough] using pre,
    walk_sound nb cb pre, (node_locals space).1, (node_locals space).2,
    related.layout.1, left, right⟩

/-- Nil entry has zero source frees and exactly one extra physical target
free. All other target objects, source state, and suspended frames survive. -/
theorem nil_entry (related : Related s H (.nil j))
    (selected : env[index]? = some (.data none))
    (connected : vs[0]? = some (some (.pointer j 0))) (space : 7 ≤ vs.size)
    (bound : ks.length ≤ limit) (fuelEnough : 3 ≤ fuel) :
    sourceEnter s env index ghosts = some (env, none) ∧
    runPrefix nb cb fuel 3 limit (stateAt H vs 0 ks) =
      some (stateAt (retired H j ReferenceHeap.nilObject) (nilLocals vs) 3 ks, [.free j]) ∧
    BoundedPrefix nb cb limit 3 (stateAt H vs 0 ks) [.free j]
      (stateAt (retired H j ReferenceHeap.nilObject) (nilLocals vs) 3 ks) ∧
    HeapLeases.Steps s.buffers.heap [] s.buffers.heap ∧
    (∀ k, k ≠ j → (retired H j ReferenceHeap.nilObject)[k]? = H[k]?) := by
  have pre := nil_prefix nb cb related.layout connected space bound
  exact ⟨by simp [sourceEnter, selected], by simpa [runPrefix, fuelEnough] using pre,
    walk_sound nb cb pre, .nil, (empty_case_total related.layout).2.2⟩


/-- Internal destinations do not alias the root, nor one another. External
integration additionally reserves these slots away from retained live locals. -/
theorem destination_noncollision : ([0,1,2,3,4,5,6] : List Nat).Nodup := by decide

/-- The slot connection is exactly the operand consumed by free/offset;
the tag read itself dereferences this same root in instruction zero. -/
theorem operand_connection :
    ReferenceCfg.operand (stateAt H vs 0 ks).frame (arg 0) =
      (vs[0]?).join := by simp [ReferenceCfg.operand, stateAt, arg]

theorem pending_shell (related : Related s H (.node x j l r)) :
    s.buffers.heap.live x = true ∧
    H[j]? = some (ReferenceHeap.node (.object l.target 0) (.object r.target 0)) ∧
    j ∉ l.ids ++ r.ids ∧ HeapLeases.Steps s.buffers.heap [] s.buffers.heap := by
  exact ⟨related.owned.live x (by simp [Image.source, Tree.owners]),
    related.layout.1, (List.nodup_cons.mp related.distinct).1, .nil⟩

end Jihoo.CommonDataCaseCfg
