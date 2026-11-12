import Jihoo.TreeDropCfg
import Jihoo.CommonDataCoreErasure
import Jihoo.CommonDataReferenceDrop

/-! Fixed binary Tree Drop. Image is a proof witness only. Execution consumes
heap/root and independent instruction fuel. Native pointer casts, reuse and
whole-compiler correctness are outside this abstract reference-cell model. -/
namespace Jihoo.TreeDropCall
open ReferenceCfg ReferenceCalls CommonDataReference

def arg (n : Nat) : Operand := .copy ⟨n, false⟩
def body (dropId : Nat) : ReferenceCalls.Function := ⟨⟨⟨
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
    some (.call ⟨dropId, #[arg 4], ⟨6, false⟩, 4⟩),
    some (.call ⟨dropId, #[arg 5], ⟨6, false⟩, 5⟩), some .retUnit]⟩, #[0]⟩
variable {p : Program} {dropId : Nat}
def locals (j : Nat) : Array (Option Value) :=
  #[some (.pointer j 0), none, none, none, none, none, none]
def start (dropId : Nat) (H : ReferenceHeap.Heap) (j : Nat) (ks : List Continuation := []) : State :=
  ⟨dropId, ⟨0, 0, locals j, H⟩, ks⟩

/-- Running prefixes count instructions and check a separate stack limit. -/
def walk (p : Program) : Nat → Nat → State → Option (State × List Event)
  | 0, limit, s => if stackDepth s ≤ limit then some (s, []) else none
  | n + 1, limit, s => do
      if stackDepth s > limit then none else do
      let next ← ReferenceCalls.tick p s
      let .running t := next.machine | none
      let (u, es) ← walk p n limit t
      pure (u, next.events ++ es)

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

/-- Every active state in the actual prefix obeys the independent stack bound. -/
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


def nilLocals (j : Nat) : Array (Option Value) :=
  #[some (.pointer j 0), some (.i64 0), none, none, none, none, some .unit]
def nodeLocals (j l r : Nat) : Array (Option Value) :=
  #[some (.pointer j 0), some (.i64 1), some (.pointer j 2),
    some (.referenceWord (.object r 0)), some (.pointer l 0), some (.pointer r 0), some .unit]
def stateAt (dropId : Nat) (H : ReferenceHeap.Heap) (vs : Array (Option Value)) (block : Nat)
    (ks : List Continuation) : State := ⟨dropId, ⟨block, 0, vs, H⟩, ks⟩
def saved (dropId : Nat) (vs : Array (Option Value)) (block : Nat) : Continuation :=
  ⟨dropId, block, vs, ⟨6, false⟩⟩

variable (installed : p[dropId]? = some (body dropId))
include installed

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem nil_prefix (found : H[j]? = some ReferenceHeap.nilObject)
    (bound : ks.length ≤ limit) :
    walk p 3 limit (start dropId H j ks) =
      some (stateAt dropId (retired H j ReferenceHeap.nilObject) (nilLocals j) 5 ks, [.free j]) := by
  simp [walk, ReferenceCalls.tick, installed, body, ReferenceCalls.extension,
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
    walk p 9 limit (start dropId H j ks) =
      some (stateAt dropId (retired H j (ReferenceHeap.node (.object l 0) (.object r 0)))
        (nodeLocals j l r) 3 ks, [.free j]) := by
  simp [walk, ReferenceCalls.tick, installed, body, ReferenceCalls.extension,
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
    walk p 1 limit (stateAt dropId H (nodeLocals j l r) 3 ks) =
    some (start dropId H l (saved dropId (nodeLocals j l r) 4 :: ks), []) := by
  have hb : ks.length ≤ limit := by omega
  simp [walk, ReferenceCalls.tick, installed, body, ReferenceCalls.extension,
    ReferenceCfg.fetch, ReferenceCalls.enter, ReferenceCalls.bindArguments,
    ReferenceCfg.initial, ReferenceCfg.write, ReferenceCfg.operand, ReferenceCfg.valueType,
    start, locals, nodeLocals, stateAt, saved, arg, stackDepth, bound,
    Nat.not_lt.mpr hb, Array.replicate_succ]

set_option maxRecDepth 10000 in
theorem call_right (bound : ks.length + 1 ≤ limit) :
    walk p 1 limit (stateAt dropId H (nodeLocals j l r) 4 ks) =
    some (start dropId H r (saved dropId (nodeLocals j l r) 5 :: ks), []) := by
  have hb : ks.length ≤ limit := by omega
  simp [walk, ReferenceCalls.tick, installed, body, ReferenceCalls.extension,
    ReferenceCfg.fetch, ReferenceCalls.enter, ReferenceCalls.bindArguments,
    ReferenceCfg.initial, ReferenceCfg.write, ReferenceCfg.operand, ReferenceCfg.valueType,
    start, locals, nodeLocals, stateAt, saved, arg, stackDepth, bound,
    Nat.not_lt.mpr hb, Array.replicate_succ]

set_option maxRecDepth 10000 in
theorem return_child (bound : ks.length + 1 ≤ limit) (blockBound : b < 6) :
    walk p 1 limit (stateAt dropId H vs 5 (saved dropId (nodeLocals j l r) b :: ks)) =
    some (stateAt dropId H (nodeLocals j l r) b ks, []) := by
  have hb : ks.length ≤ limit := by omega
  simp [walk, ReferenceCalls.tick, installed, body, ReferenceCalls.extension,
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
    ∃ K, walk p (ticks i) limit (start dropId H i.target ks) =
      some (stateAt dropId K (finalLocals i) 5 ks, i.ids.map HeapLifecycle.Event.free) ∧ Frees H i.ids K := by
  induction i generalizing H ks with
  | nil j =>
    obtain ⟨_, freed, _⟩ := empty_case_total layout
    refine ⟨retired H j ReferenceHeap.nilObject, ?_, .cons freed .nil⟩
    exact nil_prefix installed (ks := ks) (limit := limit) layout (by simp [Image.depth] at bound; omega)
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
      (ks := saved dropId (nodeLocals j l.target r.target) 4 :: ks) bounds.1
    have rl : Layout M r := by
      apply layout.2.2.congr
      intro k hk
      rw [leftFrees.frame (fun hl => apart k hl k hk rfl)]
      exact ReferenceHeap.Frame.release_agree release k
        (fun eq => rootApart (List.mem_append_right _ (eq ▸ hk)))
    obtain ⟨K, rightRun, rightFrees⟩ := ihr rl ur
      (ks := saved dropId (nodeLocals j l.target r.target) 5 :: ks) bounds.2
    refine ⟨K, ?_, .cons release (leftFrees.append rightFrees)⟩
    have count : ticks (.node x j l r) =
        9 + (1 + (ticks l + (1 + (1 + (ticks r + 1))))) := by simp [ticks]; omega
    simp only [Image.target]
    simp only [Image.object] at leftRun
    rw [count, walk_add, node_prefix installed (ks := ks) (limit := limit) layout.1 (by omega)]
    simp only [bind, Option.bind_some]
    rw [walk_add, call_left installed hb]
    simp only [bind, Option.bind_some]
    rw [walk_add, leftRun]
    simp only [bind, Option.bind_some]
    rw [walk_add, return_child installed hb (by decide : 4 < 6)]
    simp only [bind, Option.bind_some]
    rw [walk_add, call_right installed hb]
    simp only [bind, Option.bind_some]
    rw [walk_add, rightRun]
    simp only [bind, Option.bind_some]
    rw [return_child installed hb (by decide : 5 < 6)]
    simp [finalLocals, Image.ids, List.map_append]



omit installed in
/-- The zero-ID instance is exactly the original fixed executable. -/
theorem body_zero : body 0 = TreeDropCfg.body := rfl

omit installed in
/-- All legacy instructions, local types and parameter bindings are unchanged. -/
theorem body_unchanged : (body dropId).code.base = TreeDropCfg.body.code.base ∧
    (body dropId).parameters = TreeDropCfg.body.parameters := ⟨rfl, rfl⟩

omit installed in
theorem recursive_destinations :
    (body dropId).code.exits[3]? = some (some (.call ⟨dropId, #[arg 4], ⟨6, false⟩, 4⟩)) ∧
    (body dropId).code.exits[4]? = some (some (.call ⟨dropId, #[arg 5], ⟨6, false⟩, 5⟩)) := by
  exact ⟨rfl, rfl⟩

omit installed in
theorem steps_append (a : ReferenceCalls.Steps p m es n)
    (b : ReferenceCalls.Steps p n fs t) :
    ReferenceCalls.Steps p m (es ++ fs) t := by
  induction a with
  | nil => exact b
  | cons head _ ih => simpa [List.append_assoc] using ReferenceCalls.Steps.cons head (ih b)

/-- Caller and Drop IDs are independent. The destination is an ordinary unit
local, and the continuation is an existing block in the caller's code. -/
structure Site (p : Program) (s : State) (dest continuation : Nat) : Prop where
  caller : ∃ fn, p[s.function]? = some fn ∧
    continuation < fn.code.base.blocks.size ∧ fn.code.base.locals[dest]? = some .unit
  space : dest < s.frame.locals.size

def call (dropId : Nat) (owner : Operand) (dest continuation : Nat) : Call :=
  ⟨dropId, #[owner], ⟨dest, false⟩, continuation⟩
/-- Append a call block without renumbering the already compiled body. Existing
body exits are retained (missing overrides remain absent). The returned entry
is `compiled.base.blocks.size`; the continuation is the body's existing entry. -/
def compileDrop (compiled : ReferenceCalls.Code) (dropId : Nat) (owner : Operand)
    (dest bodyEntry : Nat) : ReferenceCalls.Code :=
  ⟨{ compiled.base with blocks := compiled.base.blocks.push ⟨#[], .ret⟩ },
    (Array.ofFn (fun n : Fin compiled.base.blocks.size =>
      (compiled.exits[n.val]?).join)).push (some (.call (call dropId owner dest bodyEntry)))⟩

omit installed in
theorem compileDrop_entry (compiled : ReferenceCalls.Code) :
    ReferenceCalls.extension (compileDrop compiled dropId owner dest bodyEntry)
      ⟨compiled.base.blocks.size, 0, vs, H⟩ =
        some (.call (call dropId owner dest bodyEntry)) := by
  simp [compileDrop, ReferenceCalls.extension, ReferenceCfg.fetch, Array.getElem_push]

omit installed in
theorem compileDrop_body_block (inside : block < compiled.base.blocks.size) :
    (compileDrop compiled dropId owner dest bodyEntry).base.blocks[block]? =
      compiled.base.blocks[block]? := by
  simp [compileDrop, Array.getElem?_push, inside, Nat.ne_of_lt inside]

omit installed in
theorem compileDrop_body_exit (inside : block < compiled.base.blocks.size) :
    ((compileDrop compiled dropId owner dest bodyEntry).exits[block]?).join =
      (compiled.exits[block]?).join := by
  simp [compileDrop, Array.getElem?_push, inside, Nat.ne_of_lt inside]

def suspension (s : State) (dest continuation : Nat) : Continuation :=
  ⟨s.function, continuation, s.frame.locals, ⟨dest, false⟩⟩
def resume (s : State) (dest continuation : Nat) (K : ReferenceHeap.Heap) : State :=
  ⟨s.function, ⟨continuation, 0, s.frame.locals.set! dest (some .unit), K⟩, s.stack⟩

set_option maxRecDepth 10000 in
theorem enter_owner (site : Site p s dest continuation)
    (selected : ReferenceCfg.operand s.frame owner = some (.pointer root 0)) :
    ReferenceCalls.enter p s (call dropId owner dest continuation) =
      some (start dropId s.frame.heap root (suspension s dest continuation :: s.stack)) := by
  obtain ⟨fn, found, block, ty⟩ := site.caller
  simp [ReferenceCalls.enter, call, found, installed, body, Nat.not_le.mpr block,
    ty, Nat.not_le.mpr site.space, selected, ReferenceCalls.bindArguments,
    ReferenceCfg.initial, ReferenceCfg.write, ReferenceCfg.valueType,
    start, locals, suspension, Array.replicate_succ]

set_option maxRecDepth 10000 in
theorem return_owner (site : Site p s dest continuation) :
    ReferenceCalls.tick p (stateAt dropId K vs 5 (suspension s dest continuation :: s.stack)) =
      some ⟨.running (resume s dest continuation K), []⟩ := by
  obtain ⟨fn, found, block, ty⟩ := site.caller
  simp [ReferenceCalls.tick, stateAt, installed, body, ReferenceCalls.extension,
    ReferenceCfg.fetch, ReferenceCalls.leave, suspension, found, Nat.not_le.mpr block,
    ReferenceCfg.write, ty, ReferenceCfg.valueType, site.space, resume]

omit installed in
theorem resume_local (different : slot ≠ dest) :
    (resume s dest continuation K).frame.locals[slot]? = s.frame.locals[slot]? := by
  simp only [resume]
  unfold Array.set! Array.setIfInBounds
  split <;> simp [Ne.symm different]

/-- Includes the caller's actual call instruction, all recursive calls, and
unit return to the compiled body's entry. No body execution is assumed. -/
theorem invoke (site : Site p s dest continuation)
    (atCall : ∃ fn, p[s.function]? = some fn ∧
      ReferenceCalls.extension fn.code s.frame = some (.call (call dropId owner dest continuation)))
    (selected : ReferenceCfg.operand s.frame owner = some (.pointer i.target 0))
    (layout : Layout s.frame.heap i) (unique : i.ids.Nodup)
    (depth : s.stack.length + 1 + i.depth ≤ limit) :
    ∃ K, ReferenceCalls.Steps p (.running s) (i.ids.map HeapLifecycle.Event.free)
      (.running (resume s dest continuation K)) ∧ Frees s.frame.heap i.ids K := by
  obtain ⟨fn, found, extension⟩ := atCall
  have head := ReferenceCalls.Step.call found extension (enter_owner installed site selected)
  obtain ⟨K, pre, frees⟩ := tree_prefix installed layout unique
    (ks := suspension s dest continuation :: s.stack) (limit := limit) depth
  have tail := ReferenceCalls.Steps.cons
    (ReferenceCalls.tick_sound (return_owner installed (K := K) (vs := finalLocals i) site))
    ReferenceCalls.Steps.nil
  exact ⟨K, .cons head (by simpa using steps_append (walk_sound pre).steps tail), frees⟩

/-- An arbitrary surrounding heap frame survives the entire call. -/
theorem invoke_effect (site : Site p s dest continuation)
    (atCall : ∃ fn, p[s.function]? = some fn ∧
      ReferenceCalls.extension fn.code s.frame = some (.call (call dropId owner dest continuation)))
    (selected : ReferenceCfg.operand s.frame owner = some (.pointer i.target 0))
    (layout : Layout s.frame.heap i) (unique : i.ids.Nodup)
    (depth : s.stack.length + 1 + i.depth ≤ limit) :
    ∃ K, ReferenceCalls.Steps p (.running s) (i.ids.map HeapLifecycle.Event.free)
      (.running (resume s dest continuation K)) ∧
      (∀ j, K[j]? = if j ∈ i.ids then s.frame.heap[j]?.map deadObject else s.frame.heap[j]?) := by
  obtain ⟨K, steps, frees⟩ := invoke installed site atCall selected layout unique depth
  exact ⟨K, steps, frees.effect unique⟩

omit installed in
/-- The recursive compiler must provide this interface for the body at its
actual resumed entry. It is not a theorem that arbitrary bodies compile. -/
def BodyIH (p : Program) (env : List RecursiveLexicalFields.Value)
    (b : CommonDataCoreErasure.Term) (middle : CommonData.State) (entry : State)
    (Post : RecursiveLexicalFields.Value → List HeapLeases.Event → CommonData.State →
      List Event → ReferenceCalls.Machine → Prop) : Prop :=
  ∀ result after t, CommonDataCoreErasure.Eval env b middle result after t →
    ∃ events finish, ReferenceCalls.Steps p (.running entry) events finish ∧
      Post result after t events finish

/-- General drop compiler rule: select the owner's operand, call the relocated
Drop, and enter the compiled body. Full execution is conditional on BodyIH.
Source and target event lists deliberately differ (boxed Nil shells). -/
theorem drop_simulation
    (site : Site p s dest continuation)
    (atCall : ∃ fn, p[s.function]? = some fn ∧
      ReferenceCalls.extension fn.code s.frame = some (.call (call dropId owner dest continuation)))
    (selected : ReferenceCfg.operand s.frame owner = some (.pointer i.target 0))
    (related : Related source s.frame.heap i)
    (valid : HeapLeases.Valid source.buffers.heap)
    (owned : LinearHeapPrograms.Owns source.buffers.heap (i.source.owners ++ frame))
    (ownerAt : env[k]? = some (.data (RecursiveFieldRuntime.root i.source)))
    (depth : s.stack.length + 1 + i.depth ≤ limit)
    (bodyIH : ∀ middle K, CommonData.Destroy (RecursiveFieldRuntime.root i.source) source
        (i.source.owners.map HeapLeases.Event.free) middle →
      Frees s.frame.heap i.ids K → BodyIH p env b middle (resume s dest continuation K) Post)
    (evaluation : CommonDataCoreErasure.Eval env (.drop k b) source result events target) :
    ∃ K middle after targetEvents finish,
      events = i.source.owners.map HeapLeases.Event.free ++ after ∧
      CommonData.Destroy (RecursiveFieldRuntime.root i.source) source
        (i.source.owners.map HeapLeases.Event.free) middle ∧
      CommonDataCoreErasure.Eval env b middle result after target ∧
      Frees s.frame.heap i.ids K ∧
      ReferenceCalls.Steps p (.running s)
        (i.ids.map HeapLifecycle.Event.free ++ targetEvents) finish ∧
      Post result after target targetEvents finish ∧
      i.pairs.map Prod.fst = i.source.owners ∧
      (∀ j, i.ids.count j = (i.pairs.map Prod.snd).count j + i.nils.count j) ∧
      i.nils.length = i.source.owners.length + 1 := by
  cases evaluation with
  | drop lookup destroyed evaluated =>
    have refEq := Option.some.inj (ownerAt.symm.trans lookup)
    cases refEq
    have trace := (CommonData.destroy_every_run related.fields valid owned destroyed).1
    obtain ⟨K, preSteps, frees⟩ := invoke installed site atCall selected related.layout related.distinct depth
    obtain ⟨tes, finish, bodySteps, post⟩ := bodyIH _ K (trace ▸ destroyed) frees _ _ _ evaluated
    exact ⟨K, _, _, tes, finish, by rw [trace], trace ▸ destroyed, evaluated, frees,
      steps_append preSteps bodySteps, post, source_pairs i, resource_count i, nil_count i⟩

end Jihoo.TreeDropCall
