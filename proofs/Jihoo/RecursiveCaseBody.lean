import Jihoo.RecursiveBodyProjection

/-! A source-typed Buffer body segment between recursive field entry and shell
release. This is not a complete source Case rule: children remain owned for a
later continuation and no constructor tag or dependent motive is checked. -/
namespace Jihoo.RecursiveCaseBody
open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime
open RecursiveLexicalFields RecursiveBodyProjection

structure State where
  buffers : SizedBufferHeap.State
  cells : Cells

def State.recursive (s : State) : RecursiveFieldRuntime.State := ⟨s.buffers.heap, s.cells⟩

def finish (s : State) (x : Nat) : State :=
  ⟨SizedBufferHeap.release s.buffers x, put s.cells x none⟩

/-- Existing source evaluation on the same heap, with the cell store frozen.
Events and results come from source evaluation. Frame preservation and
ownership safety are not premises of this operational rule. -/
inductive BodyRun (g : ScopedLend.Graph.Graph) : List Value → Nat → State → Nat →
    List SizedBufferHeap.Event → State → Prop where
  | core : SizedCoreExecution.Eval g (environment env) body s.buffers (.scalar n) es t →
      BodyRun g env body s n es ⟨t, s.cells⟩

theorem owns_rotate (h : Owns heap (xs ++ ys)) : Owns heap (ys ++ xs) := by
  constructor
  · exact (List.perm_append_comm.nodup_iff).mp h.distinct
  · intro x member; exact h.live x (by simpa [List.mem_append, or_comm] using member)
  · intro x member; exact h.leaseFree x (by simpa [List.mem_append, or_comm] using member)

/-- The retained Data context and pending shell survive an actual typed body.
The body consumes only the Buffer suffix. Preservation follows from the old
source theorem's accounting and lease frame, not a body-specific hypothesis. -/
theorem body_total
    (typed : SizedCoreTyping.Typing g (context retained.length ctx) sizes body .scalar)
    (agreement : Agrees (retained ++ owners.map Capability.buffer) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes)
    (valid : SizedBufferHeap.Valid s.buffers)
    (owned : Owns s.buffers.heap (owners ++ (parent :: footprint retained)))
    (fields : Fields s.cells retained) :
    ∃ n es t, BodyRun g env body s n es t ∧
      SizedBufferHeap.Steps s.buffers es t.buffers ∧ SizedBufferHeap.Valid t.buffers ∧
      Owns t.buffers.heap (parent :: footprint retained) ∧ Fields t.cells retained ∧
      Agrees retained (continuation retained.length ctx) (.scalar n :: env) ∧
      SizedCoreTyping.Account owners (.scalar n) es := by
  obtain ⟨result, es, t, run, steps, vt, post, account⟩ :=
    typed.total_accounted (project_agrees agreement) layout valid
      (OwnedApplicationFrame.owns_left owned)
  cases result <;> simp only [SizedCoreTyping.Post] at post
  case scalar n =>
    have empty : Owns t.heap [] := ⟨by simp, by simp, by simp⟩
    have retained := OwnedApplicationFrame.recombine valid owned
      (SizedBufferHeap.steps_project steps) empty run.lease_frame account
    exact ⟨n, es, ⟨t, s.cells⟩, .core run, steps, vt, retained, fields,
      continuation_agrees agreement, account⟩

/-- Every admitted body run has the same resource result as totality. -/
theorem BodyRun.deterministic (a : BodyRun g env body s n es t)
    (b : BodyRun g env body s m fs u) : n = m ∧ es = fs ∧ t = u := by
  cases a with
  | core first =>
    cases b with
    | core second =>
      obtain ⟨eq, rfl, rfl⟩ := first.deterministic second
      cases eq
      exact ⟨rfl, rfl, rfl⟩

/-- Safety and non-release hold for every admitted source body execution.
In particular, retained allocations cannot be freed and later reallocated. -/
theorem body_every_run
    (typed : SizedCoreTyping.Typing g (context retained.length ctx) sizes body .scalar)
    (agreement : Agrees (retained ++ owners.map Capability.buffer) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes)
    (valid : SizedBufferHeap.Valid s.buffers)
    (owned : Owns s.buffers.heap (owners ++ (parent :: footprint retained)))
    (fields : Fields s.cells retained) (observed : BodyRun g env body s n es t) :
    SizedBufferHeap.Steps s.buffers es t.buffers ∧ SizedBufferHeap.Valid t.buffers ∧
      Owns t.buffers.heap (parent :: footprint retained) ∧ Fields t.cells retained ∧
      Agrees retained (continuation retained.length ctx) (.scalar n :: env) ∧
      (∀ x ∈ parent :: footprint retained,
        x ∉ released (es.map SizedBufferHeap.Event.project)) := by
  obtain ⟨m, fs, u, canonical, steps, vu, kept, fsafe, lexical, account⟩ :=
    body_total typed agreement layout valid owned fields
  obtain ⟨rfl, rfl, rfl⟩ := observed.deterministic canonical
  refine ⟨steps, vu, kept, fsafe, lexical, ?_⟩
  intro x member
  exact (OwnedApplicationFrame.frame_not_accounted valid owned
    (SizedBufferHeap.steps_project steps) account member).1

/-- The source roots are original graph IDs. This checks a variable scrutinee
and a scalar Buffer body under the actual child-binding layout; it does not
claim to recognize a source Case node or its constructor telescope. -/
structure SegmentTyping (g : ScopedLend.Graph.Graph) (ctx : List Entry)
    (sizes : List Nat) (scrutinee index ghosts body : Nat) : Prop where
  shape : ScopedLend.Graph.nodeAt g scrutinee = .var index
  selected : ctx[index]? = some (.data 0)
  typed : SizedCoreTyping.Typing g (context 2 (bindContext ghosts ctx)) sizes body .scalar

/-- Operational order is field loads, source body, then parent release. -/
inductive SegmentRun (g : ScopedLend.Graph.Graph) : List Value → Nat → Nat → Nat → State →
    Nat → List SizedBufferHeap.Event → State → Prop where
  | node : ScopedLend.Graph.nodeAt g scrutinee = .var index →
    enter s.recursive env index ghosts = some (opened, parent) →
    BodyRun g opened body s n es t →
    SegmentRun g env scrutinee ghosts body s n (es ++ [.free parent]) (finish t parent)

theorem SegmentRun.deterministic (a : SegmentRun g env scrutinee ghosts body s n es t)
    (b : SegmentRun g env scrutinee ghosts body s m fs u) : n = m ∧ es = fs ∧ t = u := by
  cases a with
  | node shape entered first =>
    cases b with
    | node shape' entered' second =>
      have eq := shape.symm.trans shape'
      cases eq
      have eq := Option.some.inj (entered.symm.trans entered')
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
      obtain ⟨rfl, rfl, rfl⟩ := first.deterministic second
      exact ⟨rfl, rfl, rfl⟩

theorem footprint_append : footprint (xs ++ ys) = footprint xs ++ footprint ys := by
  induction xs with
  | nil => rfl
  | cons c cs ih => simp [footprint, ih, List.append_assoc]

private theorem steps_append (a : SizedBufferHeap.Steps s es t)
    (b : SizedBufferHeap.Steps t fs u) : SizedBufferHeap.Steps s (es ++ fs) u := by
  induction a with
  | nil => exact b
  | cons step _ ih => exact .cons step (ih b)

/-- Entry, source body preservation and final release compose. Child ownership
and the restored mixed lexical continuation are conclusions. The children are
residual resources, not silently discarded by a scalar Case result. -/
theorem segment_total (typed : SegmentTyping g ctx sizes scrutinee index ghosts body)
    (agreement : Agrees (.data (.node parent left right) :: owners.map Capability.buffer) ctx env)
    (inventory : Inventory s.recursive (.data (.node parent left right) :: owners.map Capability.buffer))
    (layout : SizedBufferContext.Layout s.buffers owners sizes)
    (valid : SizedBufferHeap.Valid s.buffers) :
    ∃ n es t opened,
      enter s.recursive env index ghosts = some (opened, parent) ∧
      SegmentRun g env scrutinee ghosts body s n es t ∧
      SizedBufferHeap.Steps s.buffers es t.buffers ∧ SizedBufferHeap.Valid t.buffers ∧
      Inventory t.recursive [.data left, .data right] ∧
      Agrees [.data left, .data right] (continuation 2 (bindContext ghosts ctx))
        (.scalar n :: opened) := by
  obtain ⟨opened, entered, agrees, pending, fields⟩ :=
    enter_total (ghosts := ghosts) agreement typed.selected inventory
  have ordered : Owns s.buffers.heap
      (owners ++ (parent :: footprint [.data left, .data right])) := by
    apply owns_rotate
    simpa [footprint, Capability.owners, footprint_buffers, List.append_assoc,
      State.recursive] using pending
  have childFields : Fields s.cells [.data left, .data right] := by
    intro c member
    exact fields c (List.mem_append_left (owners.map Capability.buffer) member)
  obtain ⟨n, before, middle, bodyRun, steps, vm, kept, keptFields, lexical, account⟩ :=
    body_total (retained := [.data left, .data right]) typed.typed agrees layout valid ordered childFields
  have releaseStep : SizedBufferHeap.Step middle.buffers (.free parent)
      (finish middle parent).buffers :=
    .free (kept.live parent (by simp)) (kept.leaseFree parent (by simp))
  have final := finish_safe (s := middle.recursive) vm kept keptFields
  exact ⟨n, before ++ [.free parent], finish middle parent, opened, entered,
    .node typed.shape entered bodyRun, steps_append steps (.cons releaseStep .nil),
    final.2.1, final.2.2, lexical⟩

/-- Every operational segment, not just the constructed witness, preserves
its residual child inventory and has a safe trace. -/
theorem segment_every_run (typed : SegmentTyping g ctx sizes scrutinee index ghosts body)
    (agreement : Agrees (.data (.node parent left right) :: owners.map Capability.buffer) ctx env)
    (inventory : Inventory s.recursive (.data (.node parent left right) :: owners.map Capability.buffer))
    (layout : SizedBufferContext.Layout s.buffers owners sizes)
    (valid : SizedBufferHeap.Valid s.buffers)
    (observed : SegmentRun g env scrutinee ghosts body s n es t) :
    SizedBufferHeap.Steps s.buffers es t.buffers ∧ SizedBufferHeap.Valid t.buffers ∧
      Inventory t.recursive [.data left, .data right] := by
  obtain ⟨m, fs, u, opened, _, canonical, steps, vu, children, _⟩ :=
    segment_total typed agreement inventory layout valid
  obtain ⟨rfl, rfl, rfl⟩ := observed.deterministic canonical
  exact ⟨steps, vu, children⟩

end Jihoo.RecursiveCaseBody
