import Jihoo.CommonDataCaseCfg

/-! Independent fixed-slot ABI relocation. No #197 context integration,
branch-body safety, native cast or reuse correctness is claimed. -/
set_option linter.unusedSimpArgs false
namespace Jihoo.CommonDataCaseRelocation
open ReferenceCfg ReferenceCalls CommonDataReference CommonDataCaseCfg

/- Relocate every CFG edge, including edges in both supplied body blocks. -/
def relocateTerm (base : Nat) : Term → Term
  | .goto b => .goto (base + b)
  | .switch v cs d => .switch v (cs.map fun (n,b) => (n,base+b)) (base+d)
  | .assert v b => .assert v (base+b)
  | .malloc v p b => .malloc v p (base+b)
  | .free v p b => .free v p (base+b)
  | .ret => .ret

def relocateBlock (base : Nat) (b : Block) : Block :=
  {b with term := relocateTerm base b.term}

/- A real failing instruction, not an out-of-bounds sentinel. -/
def failure : Block := ⟨#[], .assert (.constant (.boolean false)) 0⟩

/- The five original blocks, then failure, then an optional root-copy entry.
Body edges use fragment-relative addresses. Prefix/suffix blocks retain their
own absolute addresses. The optional entry costs one assignment plus one jump. -/
def linked (pre post : Array Block) (nb cb : Block) (src : Nat) : Program :=
  #[⟨⟨⟨(body nb cb).code.base.locals,
    pre ++ ((body nb cb).code.base.blocks.map (relocateBlock pre.size)) ++
    #[failure, ⟨#[⟨⟨0,false⟩, .use (arg src)⟩], .goto pre.size⟩] ++ post⟩, #[]⟩, #[]⟩]

def walk (p : Program) : Nat → Nat → State → Option (State × List Event)
  | 0, limit, s => if stackDepth s ≤ limit then some (s, []) else none
  | n+1, limit, s => do
      if stackDepth s > limit then none else do
      let next ← ReferenceCalls.tick p s
      let .running t := next.machine | none
      let (u, es) ← walk p n limit t
      pure (u, next.events ++ es)

def runPrefix (p : Program) (fuel steps limit : Nat) (s : State) :=
  if steps ≤ fuel then walk p steps limit s else none

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem nil_prefix (pre post : Array Block) (nb cb : Block) (src : Nat) (found : H[j]? = some ReferenceHeap.nilObject)
    (root : vs[0]? = some (some (.pointer j 0))) (space : 7 ≤ vs.size)
    (bound : ks.length ≤ limit) :
    walk (linked pre post nb cb src) 3 limit (stateAt H vs pre.size ks) =
      some (stateAt (retired H j ReferenceHeap.nilObject) (nilLocals vs) (pre.size + 3) ks, [.free j]) := by
  have h0 : 0 < vs.size := by omega
  have hroot : vs[0] = some (.pointer j 0) := by simpa [h0] using root
  have h1 : 1 < vs.size := by omega
  have h6 : 6 < vs.size := by omega
  simp [walk, linked, relocateBlock, relocateTerm, failure,
    Array.getElem?_append, Array.getElem?_map, Array.getElem?_eq_getElem,
    show ¬ pre.size < pre.size by omega,
    show ¬ pre.size + 1 < pre.size by omega,
    show ¬ pre.size + 2 < pre.size by omega,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
     ReferenceCalls.tick, program, body, ReferenceCalls.extension,
    ReferenceCfg.tick_eq_rawTick, ReferenceCfg.rawTick, ReferenceCfg.fetch,
    ReferenceCfg.operand, ReferenceCfg.load, ReferenceCfg.rvalue, ReferenceCfg.write,
    ReferenceCfg.valueType, ReferenceCfg.advance, ReferenceCfg.jump, ReferenceCfg.switchValue,
    ReferenceCfg.select, ReferenceCfg.freeHeap, ReferenceCalls.liftLegacy,
    ReferenceHeap.release, ReferenceHeap.load, ReferenceHeap.address, found,
    ReferenceHeap.nilObject, nilLocals, stateAt, retired, arg, stackDepth, bound,
    Nat.not_lt.mpr bound, Array.set!, Array.setIfInBounds, h0, h1, h6, hroot]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem node_prefix (pre post : Array Block) (nb cb : Block) (src : Nat) (found : H[j]? = some (ReferenceHeap.node (.object l 0) (.object r 0)))
    (root : vs[0]? = some (some (.pointer j 0))) (space : 7 ≤ vs.size)
    (bound : ks.length ≤ limit) :
    walk (linked pre post nb cb src) 9 limit (stateAt H vs pre.size ks) =
      some (stateAt H (nodeLocals vs j l r) (pre.size + 4) ks, []) := by
  have h0 : 0 < vs.size := by omega
  have hroot : vs[0] = some (.pointer j 0) := by simpa [h0] using root
  have h1 : 1 < vs.size := by omega
  have h2 : 2 < vs.size := by omega
  have h3 : 3 < vs.size := by omega
  have h4 : 4 < vs.size := by omega
  have h5 : 5 < vs.size := by omega
  simp [walk, linked, relocateBlock, relocateTerm, failure,
    Array.getElem?_append, Array.getElem?_map, Array.getElem?_eq_getElem,
    show ¬ pre.size < pre.size by omega,
    show ¬ pre.size + 1 < pre.size by omega,
    show ¬ pre.size + 2 < pre.size by omega,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
     ReferenceCalls.tick, program, body, ReferenceCalls.extension,
    ReferenceCfg.tick_eq_rawTick, ReferenceCfg.rawTick, ReferenceCfg.fetch,
    ReferenceCfg.operand, ReferenceCfg.load, ReferenceCfg.rvalue, ReferenceCfg.write,
    ReferenceCfg.valueType, ReferenceCfg.advance, ReferenceCfg.jump, ReferenceCfg.switchValue,
    ReferenceCfg.select, ReferenceCfg.freeHeap, ReferenceCalls.liftLegacy,
    ReferenceCfg.constant, BoundedMir.constant, ReferenceCfg.embedValue, ReferenceCfg.ofRef,
    ReferenceHeap.release, ReferenceHeap.load, ReferenceHeap.address, found,
    ReferenceHeap.node, ReferenceHeap.pointerToWord, nodeLocals, stateAt,
    arg, stackDepth, bound, Nat.not_lt.mpr bound, BoundedMir.wordBound,
    Array.set!, Array.setIfInBounds, h0, h1, h2, h3, h4, h5, hroot]

theorem walk_add (a b limit s) : walk p (a + b) limit s = (do
    let (t, es) ← walk p a limit s
    let (u, fs) ← walk p b limit t
    pure (u, es ++ fs)) := by
  induction a generalizing s with
  | zero =>
    simp only [Nat.zero_add, walk]
    split
    · cases h : walk p b limit s <;> simp [h]
    · cases b <;> simp_all [walk]
  | succ a ih =>
    simp only [Nat.succ_add, walk]
    split <;> simp_all
    cases ht : ReferenceCalls.tick p s with
    | none => simp
    | some next =>
      cases hm : next.machine <;>
        simp [hm, Option.bind_assoc, List.append_assoc]

/- Every active state in the actual prefix obeys the independent stack bound. -/
inductive BoundedPrefix (p : Program) (limit : Nat) : Nat → State → List Event → State → Prop where
  | nil : stackDepth s ≤ limit → BoundedPrefix p limit 0 s [] s
  | cons : stackDepth s ≤ limit → ReferenceCalls.tick p s = some ⟨.running t, es⟩ →
      BoundedPrefix p limit n t fs u → BoundedPrefix p limit (n + 1) s (es ++ fs) u

theorem walk_sound (h : walk p n limit s = some (t, es)) :
    BoundedPrefix p limit n s es t := by
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
      cases ht : ReferenceCalls.tick p s with
      | none => simp [ht] at h
      | some next =>
        cases hm : next.machine with
        | returned _ _ => simp [ht, hm] at h
        | running u =>
          cases hw : walk p n limit u with
          | none => simp [ht, hm, hw] at h
          | some result =>
            obtain ⟨v, fs⟩ := result
            simp [ht, hm, hw] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .cons (by omega) (by simpa only [← hm] using ht) (ih hw)

theorem BoundedPrefix.steps (h : BoundedPrefix p limit n s es t) :
    ReferenceCalls.Steps p (.running s) es (.running t) := by
  induction h with
  | nil _ => exact .nil
  | cons _ ht _ ih => exact .cons (ReferenceCalls.tick_sound ht) ih

theorem BoundedPrefix.execute (h : BoundedPrefix p limit n s es t)
    (tail : ReferenceCalls.execute fuel p t = some out) :
    ReferenceCalls.execute (n + fuel) p s = some {out with events := es ++ out.events} := by
  induction h with
  | nil _ => simpa using tail
  | cons _ ht _ ih =>
    simp [Nat.succ_add, ReferenceCalls.execute, ht, ih tail, List.append_assoc]


/- Copying the selected root to reserved slot zero costs two ticks in this
layout (one assignment and one goto), and preserves heap and suspended frames. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem copy_prefix (pre post : Array Block) (nb cb : Block) (src : Nat)
    (selected : vs[src]? = some (some (.pointer j 0))) (space : 7 ≤ vs.size)
    (bound : ks.length ≤ limit) :
    walk (linked pre post nb cb src) 2 limit
      (stateAt H vs (pre.size + 6) ks) =
    some (stateAt H (vs.set! 0 (some (.pointer j 0))) pre.size ks, []) := by
  have h0 : 0 < vs.size := by omega
  simp [walk, linked, relocateBlock, relocateTerm, failure, body,
    ReferenceCalls.tick, ReferenceCalls.extension, ReferenceCfg.tick_eq_rawTick,
    ReferenceCfg.rawTick, ReferenceCfg.fetch, ReferenceCfg.operand,
    ReferenceCfg.rvalue, ReferenceCfg.write, ReferenceCfg.valueType,
    ReferenceCfg.advance, ReferenceCfg.jump, ReferenceCalls.liftLegacy,
    stateAt, arg, stackDepth, bound, Nat.not_lt.mpr bound, selected, h0,
    Array.set!, Array.setIfInBounds, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/- The slot allocator must establish this for retained live bindings. -/
def Apart (live writes : List Nat) : Prop := ∀ k ∈ live, k ∉ writes

theorem node_live (h : Apart live [1,2,3,4,5]) (hk : k ∈ live) :
    (nodeLocals vs j l r)[k]? = vs[k]? := node_frame (h k hk)

theorem nil_live (h : Apart live [1,6]) (hk : k ∈ live) :
    (nilLocals vs)[k]? = vs[k]? := by
  apply nil_frame <;> have hh := h k hk <;> simp_all

/- When root copying is used, slot zero must also be reserved. -/
theorem copy_live {vs : Array (Option Value)} (h : Apart live [0]) (hk : k ∈ live) :
    (vs.set! 0 (some (.pointer j 0)))[k]? = vs[k]? := by
  have hn : 0 ≠ k := by
    have hh := h k hk
    simp only [List.mem_singleton] at hh
    exact Ne.symm hh
  simp [Array.set!, Array.getElem?_setIfInBounds, hn]

theorem binder_order (space : 7 ≤ vs.size) :
    (RecursiveLexicalFields.bindValues ghosts ⟨l, r⟩ env).take 2 = [.data r, .data l] ∧
    ([5,4] : List Nat).map (fun k => (nodeLocals vs j lt rt)[k]?) =
      [some (some (.pointer rt 0)), some (some (.pointer lt 0))] := by
  obtain ⟨hl, hr⟩ := node_locals (j := j) (l := lt) (r := rt) space
  simp [RecursiveLexicalFields.bindValues, hl, hr]

/- Failure remains failure for any prefix/suffix, heap, locals and stack. -/
set_option maxRecDepth 10000 in
theorem failure_tick (pre post : Array Block) (nb cb : Block) (src : Nat) :
    ReferenceCalls.tick (linked pre post nb cb src)
      (stateAt H vs (pre.size + 5) ks) = none := by
  simp [linked, body, failure, ReferenceCalls.tick, ReferenceCalls.extension,
    ReferenceCfg.tick_eq_rawTick, ReferenceCfg.rawTick, ReferenceCfg.fetch,
    ReferenceCfg.operand, ReferenceCfg.constant, BoundedMir.constant,
    ReferenceCfg.embedValue, stateAt, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/- An invalid tag takes the relocated default, never an appended body. -/
set_option maxRecDepth 10000 in
theorem invalid_dispatch (pre post : Array Block) (nb cb : Block) (src : Nat)
    (tag : vs[1]? = some (some (.i64 n))) (hn : n ≠ 0) (hn' : n ≠ 1) :
    ReferenceCalls.tick (linked pre post nb cb src)
      ⟨0, ⟨pre.size, 1, vs, H⟩, ks⟩ =
      some ⟨.running (stateAt H vs (pre.size + 5) ks), []⟩ := by
  simp [linked, body, relocateBlock, relocateTerm, ReferenceCalls.tick,
    ReferenceCalls.extension, ReferenceCfg.tick_eq_rawTick, ReferenceCfg.rawTick,
    ReferenceCfg.fetch, ReferenceCfg.operand, ReferenceCfg.switchValue,
    ReferenceCfg.select, ReferenceCfg.jump, ReferenceCalls.liftLegacy,
    stateAt, arg, tag, hn, hn', List.find?, beq_eq_false_iff_ne.mpr (Ne.symm hn),
    beq_eq_false_iff_ne.mpr (Ne.symm hn'), Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem nil_copied_entry (pre post : Array Block) (nb cb : Block) (src : Nat)
    (found : H[j]? = some ReferenceHeap.nilObject)
    (selected : vs[src]? = some (some (.pointer j 0))) (space : 7 ≤ vs.size)
    (bound : ks.length ≤ limit) (enough : 5 ≤ fuel) :
    runPrefix (linked pre post nb cb src) fuel 5 limit
      (stateAt H vs (pre.size + 6) ks) =
    some (stateAt (retired H j ReferenceHeap.nilObject) (nilLocals (vs.set! 0 (some (.pointer j 0)))) (pre.size + 3) ks, [.free j]) := by
  have h0 : 0 < vs.size := by omega
  have root : (vs.set! 0 (some (.pointer j 0)))[0]? = some (some (.pointer j 0)) := by
    simp [Array.set!, Array.getElem?_setIfInBounds, h0]
  have size : 7 ≤ (vs.set! 0 (some (.pointer j 0))).size := by simpa using space
  unfold runPrefix
  rw [ite_eq_left enough]
  rw [show 5 = 2 + 3 from rfl, walk_add,
    copy_prefix pre post nb cb src selected space bound]
  dsimp only [Bind.bind, Option.bind]
  rw [nil_prefix pre post nb cb src found root size bound]
  rfl

theorem node_copied_entry (pre post : Array Block) (nb cb : Block) (src : Nat)
    (found : H[j]? = some (ReferenceHeap.node (.object l 0) (.object r 0)))
    (selected : vs[src]? = some (some (.pointer j 0))) (space : 7 ≤ vs.size)
    (bound : ks.length ≤ limit) (enough : 11 ≤ fuel) :
    runPrefix (linked pre post nb cb src) fuel 11 limit
      (stateAt H vs (pre.size + 6) ks) =
    some (stateAt H (nodeLocals (vs.set! 0 (some (.pointer j 0))) j l r) (pre.size + 4) ks, []) := by
  have h0 : 0 < vs.size := by omega
  have root : (vs.set! 0 (some (.pointer j 0)))[0]? = some (some (.pointer j 0)) := by
    simp [Array.set!, Array.getElem?_setIfInBounds, h0]
  have size : 7 ≤ (vs.set! 0 (some (.pointer j 0))).size := by simpa using space
  unfold runPrefix
  rw [ite_eq_left enough]
  rw [show 11 = 2 + 9 from rfl, walk_add,
    copy_prefix pre post nb cb src selected space bound]
  dsimp only [Bind.bind, Option.bind]
  rw [node_prefix pre post nb cb src found root size bound]
  rfl


/- Enumerate every outgoing edge, including the switch default. -/
def edges : Term → List Nat
  | .goto b | .assert _ b | .malloc _ _ b | .free _ _ b => [b]
  | .switch _ cs d => cs.map Prod.snd ++ [d]
  | .ret => []

theorem relocate_edges (base : Nat) (t : Term) :
    edges (relocateTerm base t) = (edges t).map (base + ·) := by
  cases t <;> simp [edges, relocateTerm, List.map_append, List.map_map, Function.comp_def]

/- All five original blocks, including both body blocks, are translated. -/
theorem relocated_lookup (pre post : Array Block) (nb cb : Block) (src i : Nat)
    (hi : i < 5) :
    ((linked pre post nb cb src)[0]'(by simp [linked])).code.base.blocks[pre.size + i]? =
      ((body nb cb).code.base.blocks[i]?).map (relocateBlock pre.size) := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;> simp [linked, body, Nat.add_comm]

theorem copied_node_live {vs : Array (Option Value)} (h : Apart live [0,1,2,3,4,5]) (hk : k ∈ live) :
    (nodeLocals (vs.set! 0 (some (.pointer j 0))) j l r)[k]? = vs[k]? := by
  rw [node_frame, copy_live (live := live) (hk := hk)]
  · intro x hx; have hh := h x hx; simp_all
  · have hh := h k hk; simp_all

theorem copied_nil_live {vs : Array (Option Value)} (h : Apart live [0,1,6]) (hk : k ∈ live) :
    (nilLocals (vs.set! 0 (some (.pointer j 0))))[k]? = vs[k]? := by
  have hh := h k hk
  rw [nil_frame (by simp_all) (by simp_all)]
  apply copy_live (live := live) (hk := hk)
  intro x hx; have hh := h x hx; simp_all


/- The fuel-gated entry result yields actual relational steps and composes
with any separately justified tail using prefix ticks + tail fuel. -/
theorem runPrefix_sound (h : runPrefix p fuel n limit s = some (t, es)) :
    n ≤ fuel ∧ BoundedPrefix p limit n s es t := by
  unfold runPrefix at h
  split at h
  · exact ⟨by assumption, walk_sound h⟩
  · contradiction

open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime

theorem node_entry (pre post : Array Block) (nb cb : Block) (src : Nat)
    (related : Related s H (.node x j l r))
    (selected : env[index]? = some (.data (some x)))
    (connected : vs[src]? = some (some (.pointer j 0))) (space : 7 ≤ vs.size)
    (bound : ks.length ≤ limit) (enough : 11 ≤ fuel) :
    sourceEnter s env index ghosts = some
      (RecursiveLexicalFields.bindValues ghosts ⟨root l.source, root r.source⟩ env, some x) ∧
    runPrefix (linked pre post nb cb src) fuel 11 limit
      (stateAt H vs (pre.size + 6) ks) =
      some (stateAt H (nodeLocals (vs.set! 0 (some (.pointer j 0))) j l.target r.target)
        (pre.size + 4) ks, []) ∧
    Related s H l ∧ Related s H r := by
  obtain ⟨entered, _, left, right⟩ := case_open_total related selected (ghosts := ghosts)
  exact ⟨by simp [sourceEnter, selected, entered],
    node_copied_entry pre post nb cb src related.layout.1 connected space bound enough,
    left, right⟩

theorem nil_entry (pre post : Array Block) (nb cb : Block) (src : Nat)
    (related : Related s H (.nil j))
    (selected : env[index]? = some (.data none))
    (connected : vs[src]? = some (some (.pointer j 0))) (space : 7 ≤ vs.size)
    (bound : ks.length ≤ limit) (enough : 5 ≤ fuel) :
    sourceEnter s env index ghosts = some (env, none) ∧
    runPrefix (linked pre post nb cb src) fuel 5 limit
      (stateAt H vs (pre.size + 6) ks) =
      some (stateAt (retired H j ReferenceHeap.nilObject)
        (nilLocals (vs.set! 0 (some (.pointer j 0)))) (pre.size + 3) ks, [.free j]) := by
  exact ⟨by simp [sourceEnter, selected],
    nil_copied_entry pre post nb cb src related.layout connected space bound enough⟩

end Jihoo.CommonDataCaseRelocation
