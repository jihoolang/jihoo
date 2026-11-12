import Jihoo.CommonDataSyntax
import Jihoo.ReferenceHeapFrame

/-! State/resource bridge only: source empty owns nothing; target Nil is boxed.
No identity equality, CFG, native casts, reuse or recursive Drop is assumed. -/
namespace Jihoo.CommonDataReference
open HeapLeases LinearHeapPrograms OwnedCoreContinuation RecursiveFieldOwnership
open RecursiveFieldRuntime

inductive Image where
  | nil (target : Nat)
  | node (source target : Nat) (left right : Image)
  deriving Repr, DecidableEq

def Image.source : Image → Tree
  | .nil _ => .empty
  | .node x _ l r => .node x l.source r.source

def Image.target : Image → Nat
  | .nil j | .node _ j _ _ => j

def Image.pairs : Image → List (Nat × Nat)
  | .nil _ => []
  | .node x j l r => (x,j) :: (l.pairs ++ r.pairs)

def Image.nils : Image → List Nat
  | .nil j => [j]
  | .node _ _ l r => l.nils ++ r.nils

def Image.ids : Image → List Nat
  | .nil j => [j]
  | .node _ j l r => j :: (l.ids ++ r.ids)

def Image.object : Image → ReferenceHeap.Object
  | .nil _ => ReferenceHeap.nilObject
  | .node _ _ l r => ReferenceHeap.node (.object l.target 0) (.object r.target 0)

/-- Shape entails live, in-bounds, initialized tags and references. -/
def Layout (H : ReferenceHeap.Heap) : Image → Prop
  | .nil j => H[j]? = some ReferenceHeap.nilObject
  | .node _ j l r => H[j]? = some (ReferenceHeap.node (.object l.target 0) (.object r.target 0)) ∧
      Layout H l ∧ Layout H r

structure Related (s : CommonData.State) (H : ReferenceHeap.Heap) (i : Image) : Prop where
  fields : Represents s.cells i.source
  owned : OwnsTree s.buffers.heap i.source
  layout : Layout H i
  distinct : i.ids.Nodup

theorem source_pairs (i : Image) : i.pairs.map Prod.fst = i.source.owners := by
  induction i <;> simp_all [Image.pairs, Image.source, Tree.owners]

theorem target_resources (i : Image) (j : Nat) :
    j ∈ i.ids ↔ j ∈ i.pairs.map Prod.snd ∨ j ∈ i.nils := by
  induction i <;> simp_all [Image.ids, Image.pairs, Image.nils] <;> grind

theorem nil_count (i : Image) : i.nils.length = i.source.owners.length + 1 := by
  induction i <;> simp_all [Image.nils, Image.source, Tree.owners] <;> omega

theorem Layout.root (h : Layout H i) : H[i.target]? = some i.object := by
  cases i <;> simp_all [Layout, Image.target, Image.object]

theorem Layout.bound (h : Layout H i) (member : j ∈ i.ids) : j < H.size := by
  induction i with
  | nil k =>
    simp only [Image.ids, List.mem_singleton] at member
    subst j
    exact Array.getElem?_eq_some_iff.mp h |>.1
  | node x k l r ihl ihr =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Array.getElem?_eq_some_iff.mp h.1 |>.1
    · rcases List.mem_append.mp member with member | member
      · exact ihl h.2.1 member
      · exact ihr h.2.2 member

theorem Layout.congr (h : Layout H i) (same : ∀ j ∈ i.ids, K[j]? = H[j]?) : Layout K i := by
  induction i with
  | nil j => exact (same j (by simp [Image.ids])).trans h
  | node x j l r ihl ihr =>
    exact ⟨(same j (by simp [Image.ids])).trans h.1,
      ihl h.2.1 (fun k hk => same k (by simp [Image.ids, hk])),
      ihr h.2.2 (fun k hk => same k (by simp [Image.ids, hk]))⟩

theorem Layout.push (h : Layout H i) (o : ReferenceHeap.Object) : Layout (H.push o) i :=
  h.congr (fun _ member => ReferenceHeap.external_frame (h.bound member) o)

theorem tag_total (h : Layout H i) : ReferenceHeap.loadScalar H (.object i.target 0) =
    some (match i with | .nil _ => 0 | .node .. => 1) := by
  have found := h.root
  cases i <;> simp_all [Image.target, Image.object, ReferenceHeap.loadScalar,
    ReferenceHeap.load, ReferenceHeap.address, ReferenceHeap.nilObject, ReferenceHeap.node]

theorem children_total (h : Layout H (.node x j l r)) :
    ReferenceHeap.loadRef H (.object j 1) = some (.object l.target 0) ∧
    ReferenceHeap.loadRef H (.object j 2) = some (.object r.target 0) := by
  simp [ReferenceHeap.loadRef, ReferenceHeap.load, ReferenceHeap.address, h.1, ReferenceHeap.node, ReferenceHeap.pointerToWord]

def makeNil (H : ReferenceHeap.Heap) : Option ReferenceHeap.Heap := do
  let allocated ← ReferenceHeap.allocate H 8
  ReferenceHeap.store allocated (.object H.size 0) (.scalar 0)

def makeNode (H : ReferenceHeap.Heap) (l r : Nat) : Option ReferenceHeap.Heap := do
  let allocated ← ReferenceHeap.allocate H 24
  let tagged ← ReferenceHeap.store allocated (.object H.size 0) (.scalar 1)
  let left ← ReferenceHeap.store tagged (.object H.size 1) (ReferenceHeap.pointerToWord (.object l 0))
  ReferenceHeap.store left (.object H.size 2) (ReferenceHeap.pointerToWord (.object r 0))

def Budget (H : ReferenceHeap.Heap) (cells : Nat) : Prop :=
  H.size < 512 ∧ (H.toList.map (fun o => o.cells.size)).sum + cells ≤ 4096

theorem makeNil_total (capacity : Budget H 1) : makeNil H = some (H.push ReferenceHeap.nilObject) := by
  simp [makeNil, ReferenceHeap.allocate, capacity.1, capacity.2, ReferenceHeap.store, ReferenceHeap.address,
    ReferenceHeap.validCell, ReferenceHeap.nilObject, BoundedMir.scalarBound, Array.replicate_succ,
    Array.set!, Array.setIfInBounds, Array.set_push]

theorem makeNode_total (capacity : Budget H 3) :
    makeNode H l r = some (H.push (ReferenceHeap.node (.object l 0) (.object r 0))) := by
  simp [makeNode, ReferenceHeap.node_allocate capacity.1 capacity.2,
    ReferenceHeap.node_store_tag, ReferenceHeap.node_store_left, ReferenceHeap.node_store_right]

/-- Source empty stutters; target allocates an extra Nil. -/
theorem empty_total (s : CommonData.State) (capacity : Budget H 1) :
    makeNil H = some (H.push ReferenceHeap.nilObject) ∧ Related s (H.push ReferenceHeap.nilObject) (.nil H.size) ∧
      (∀ j < H.size, (H.push ReferenceHeap.nilObject)[j]? = H[j]?) := by
  refine ⟨makeNil_total capacity, ⟨trivial, ?_, by simp [Layout], by simp [Image.ids]⟩,
    fun _ hj => ReferenceHeap.external_frame hj _⟩
  exact ⟨by simp [Image.source, Tree.owners], by simp [Image.source, Tree.owners],
    by simp [Image.source, Tree.owners]⟩

/-- Initial ownership/separation are joint across the children. -/
theorem allocate_total (valid : Valid s.buffers.heap)
    (lf : Represents s.cells l.source) (rf : Represents s.cells r.source)
    (owned : Owns s.buffers.heap (l.source.owners ++ r.source.owners ++ frame))
    (ll : Layout H l) (rl : Layout H r) (separate : (l.ids ++ r.ids).Nodup)
    (capacity : Budget H 3) :
    let t := CommonData.allocate s (root l.source) (root r.source)
    let K := H.push (ReferenceHeap.node (.object l.target 0) (.object r.target 0))
    makeNode H l.target r.target = some K ∧
    Related t K (.node s.buffers.heap.nextObject H.size l r) ∧
    Valid t.buffers.heap ∧
    Owns t.buffers.heap ((Tree.node s.buffers.heap.nextObject l.source r.source).owners ++ frame) ∧
    (∀ j < H.size, K[j]? = H[j]?) := by
  obtain ⟨vt, ft, ot⟩ := RecursiveFieldRuntime.allocate_safe (s := s.recursive) valid lf rf owned (payload := 0)
  refine ⟨makeNode_total capacity, ⟨ft, OwnedApplicationFrame.owns_left ot, ?_, ?_⟩,
    vt, ot, fun _ hj => ReferenceHeap.external_frame hj _⟩
  · exact ⟨by simp, ll.push _, rl.push _⟩
  · apply List.nodup_cons.mpr
    refine ⟨?_, separate⟩
    intro member
    rcases List.mem_append.mp member with member | member
    · have := ll.bound member; omega
    · have := rl.bound member; omega

/-- Case observes the shell; release is delayed to finish. -/
def openNode (H : ReferenceHeap.Heap) (j : Nat) : Option (ReferenceHeap.Ref × ReferenceHeap.Ref) := do
  let tag ← ReferenceHeap.loadScalar H (.object j 0)
  if tag = 1 then
    pure (← ReferenceHeap.loadRef H (.object j 1), ← ReferenceHeap.loadRef H (.object j 2))
  else none

theorem case_open_total (related : Related s H (.node x j l r))
    (selected : env[k]? = some (.data (some x))) :
    RecursiveLexicalFields.enter s.recursive env k ghosts =
      some (RecursiveLexicalFields.bindValues ghosts ⟨root l.source, root r.source⟩ env, x) ∧
    openNode H j = some (.object l.target 0, .object r.target 0) ∧
    Related s H l ∧ Related s H r := by
  have live := related.owned.live x (by simp [Image.source, Tree.owners])
  have children := children_total related.layout
  have sep := (List.nodup_cons.mp related.distinct).2
  have owners : Owns s.buffers.heap (l.source.owners ++ r.source.owners) :=
    ⟨(List.nodup_cons.mp related.owned.distinct).2,
      fun y hy => related.owned.live y (List.mem_cons_of_mem _ hy),
      fun y hy => related.owned.leaseFree y (List.mem_cons_of_mem _ hy)⟩
  refine ⟨?_, ?_, ⟨related.fields.2.1, OwnedApplicationFrame.owns_left owners,
    related.layout.2.1, (List.nodup_append.mp sep).1⟩,
    ⟨related.fields.2.2, OwnedApplicationFrame.owns_right owners,
    related.layout.2.2, (List.nodup_append.mp sep).2.1⟩⟩
  · simp [RecursiveLexicalFields.enter, selected, RecursiveCaseBody.State.recursive,
      live, related.fields.1]
  · have tag : ReferenceHeap.loadScalar H (.object j 0) = some 1 := tag_total related.layout
    simp [openNode, tag, children.1, children.2]

/-- The pending shell is an explicit resource, separate from retained trees. -/
def retired (H : ReferenceHeap.Heap) (j : Nat) (obj : ReferenceHeap.Object) : ReferenceHeap.Heap :=
  H.set! j {obj with alive := false}

private theorem release_known (found : H[j]? = some obj) (live : obj.alive = true) :
    ReferenceHeap.release H (.object j 0) = some (retired H j obj) := by
  exact ReferenceHeap.Frame.release_success_iff.mpr ⟨obj, found, live, rfl, rfl⟩

private theorem retired_other (different : j ≠ k) :
    (retired H j obj)[k]? = H[k]? := by
  exact ReferenceHeap.Frame.set_other H _ (Ne.symm different)

/-- Finish consumes a source pending owner and its mapped target shell.
The retained tree may be any finite tree; no body run or target success is assumed.
External target objects may be dead, absent, buffers, or unrelated allocations. -/
theorem finish_total (valid : Valid s.buffers.heap)
    (fields : Represents s.cells i.source)
    (owned : Owns s.buffers.heap (x :: (i.source.owners ++ frame)))
    (layout : Layout H i) (distinct : i.ids.Nodup)
    (pending : H[j]? = some obj) (live : obj.alive = true)
    (separate : j ∉ i.ids) :
    HeapLeases.Step s.buffers.heap (.free x) (CommonData.finish s x).buffers.heap ∧
    Valid (CommonData.finish s x).buffers.heap ∧
    ReferenceHeap.release H (.object j 0) = some (retired H j obj) ∧
    Related (CommonData.finish s x) (retired H j obj) i ∧
    Owns (CommonData.finish s x).buffers.heap (i.source.owners ++ frame) ∧
    (∀ k, k ≠ j → (retired H j obj)[k]? = H[k]?) := by
  have step : HeapLeases.Step s.buffers.heap (.free x) (freedState s.buffers.heap x) :=
    .free (owned.live x (by simp)) (owned.leaseFree x (by simp))
  have kept := free_owns owned Select.here
  have absent : x ∉ i.source.owners := fun hx =>
    (List.nodup_cons.mp owned.distinct).1 (List.mem_append_left frame hx)
  exact ⟨step, step_valid valid step, release_known pending live,
    ⟨fields.clear_other absent, OwnedApplicationFrame.owns_left kept,
      layout.congr (fun _ hk => retired_other (fun eq => separate (eq ▸ hk))), distinct⟩,
    kept, fun _ hk => retired_other (Ne.symm hk)⟩

/-- A node's child/frame disjointness supplies the finish premises. -/
theorem finish_children (valid : Valid s.buffers.heap)
    (related : Related s H (.node x j l r)) :
    ReferenceHeap.release H (.object j 0) = some (retired H j (.node x j l r : Image).object) ∧
    Related (CommonData.finish s x) (retired H j (.node x j l r : Image).object) l ∧
    Related (CommonData.finish s x) (retired H j (.node x j l r : Image).object) r := by
  have sep := List.nodup_cons.mp related.distinct
  have own : Owns s.buffers.heap (x :: (l.source.owners ++ r.source.owners)) := related.owned
  have left := finish_total (frame := r.source.owners) valid related.fields.2.1 own
    related.layout.2.1 (List.nodup_append.mp sep.2).1 related.layout.1 (by rfl)
    (fun hj => sep.1 (List.mem_append_left _ hj))
  have rightOwn : Owns s.buffers.heap (x :: (r.source.owners ++ l.source.owners)) :=
    CommonData.owns_permute own (List.Perm.cons x List.perm_append_comm)
  have right := finish_total (frame := l.source.owners) valid related.fields.2.2 rightOwn
    related.layout.2.2 (List.nodup_append.mp sep.2).2.1 related.layout.1 (by rfl)
    (fun hj => sep.1 (List.mem_append_right _ hj))
  exact ⟨left.2.2.1, left.2.2.2.1, right.2.2.2.1⟩

/-- Boxed empty Case consumes a target-only Nil shell; source state stutters. -/
theorem empty_case_total (layout : Layout H (.nil j)) :
    ReferenceHeap.loadScalar H (.object j 0) = some 0 ∧
    ReferenceHeap.release H (.object j 0) = some (retired H j ReferenceHeap.nilObject) ∧
    (∀ k, k ≠ j → (retired H j ReferenceHeap.nilObject)[k]? = H[k]?) :=
  ⟨tag_total layout, release_known layout rfl, fun _ hk => retired_other (Ne.symm hk)⟩

/-- Retained uniform-fill buffers have an independent identity and exact cells.
This is preservation of retained Buffer resources, not execution of Buffer bodies. -/
structure BufferRelated (s : CommonData.State) (H : ReferenceHeap.Heap) (x j : Nat) : Prop where
  live : s.buffers.heap.live x = true
  object : H[j]? = some ⟨true, Array.replicate (s.buffers.length x)
    (some (.scalar (s.buffers.heap.payload x)))⟩

theorem BufferRelated.finish (h : BufferRelated s H x j)
    (sourceSeparate : x ≠ parent) (targetSeparate : parentTarget ≠ j) :
    BufferRelated (CommonData.finish s parent) (retired H parentTarget obj) x j := by
  constructor
  · simpa [CommonData.finish, RecursiveCaseBody.finish, SizedBufferHeap.release,
      put, sourceSeparate] using h.live
  · simpa [CommonData.finish, RecursiveCaseBody.finish, SizedBufferHeap.release,
      retired_other targetSeparate] using h.object

theorem BufferRelated.allocate (h : BufferRelated s H x j)
    (valid : Valid s.buffers.heap) (fresh : ReferenceHeap.Object) :
    BufferRelated (CommonData.allocate s left right) (H.push fresh) x j := by
  have old := valid.allocated x h.live
  have bound : j < H.size := (Array.getElem?_eq_some_iff.mp h.object).1
  constructor
  · simp [CommonData.allocate, allocatedState, put, Nat.ne_of_lt old, h.live]
  · simpa [CommonData.allocate, allocatedState, put, Nat.ne_of_lt old,
      ReferenceHeap.external_frame bound fresh] using h.object

/-- Exact multiplicity accounting, including the extra Nil allocations. -/
theorem resource_count (i : Image) (j : Nat) :
    i.ids.count j = (i.pairs.map Prod.snd).count j + i.nils.count j := by
  induction i <;> simp_all [Image.ids, Image.pairs, Image.nils, List.count_cons] <;> omega

/-- Source/target allocations preserve any independently retained tree. -/
theorem Related.allocate (h : Related s H i) (valid : Valid s.buffers.heap)
    (fresh : ReferenceHeap.Object) :
    Related (CommonData.allocate s left right) (H.push fresh) i := by
  constructor
  · apply h.fields.congr
    intro x hx
    have bound := valid.allocated x (h.owned.live x hx)
    simp [CommonData.allocate, put, Nat.ne_of_lt bound]
  · constructor
    · exact h.owned.distinct
    · intro x hx
      have bound := valid.allocated x (h.owned.live x hx)
      simp [CommonData.allocate, allocatedState, put, Nat.ne_of_lt bound, h.owned.live x hx]
    · exact h.owned.leaseFree
  · exact h.layout.push fresh
  · exact h.distinct

/-- A target-only Nil release leaves disjoint retained source/target trees related. -/
theorem Related.retireNil (h : Related s H i) (separate : j ∉ i.ids) :
    Related s (retired H j ReferenceHeap.nilObject) i :=
  ⟨h.fields, h.owned,
    h.layout.congr (fun _ hk => retired_other (fun eq => separate (eq ▸ hk))), h.distinct⟩

theorem BufferRelated.retireNil (h : BufferRelated s H x j) (separate : nilId ≠ j) :
    BufferRelated s (retired H nilId ReferenceHeap.nilObject) x j :=
  ⟨h.live, (retired_other separate).trans h.object⟩

/-- Target-only allocation (notably boxed Nil) preserves the same source state. -/
theorem Related.push (h : Related s H i) (fresh : ReferenceHeap.Object) :
    Related s (H.push fresh) i := ⟨h.fields, h.owned, h.layout.push fresh, h.distinct⟩

theorem BufferRelated.push (h : BufferRelated s H x j) (fresh : ReferenceHeap.Object) :
    BufferRelated s (H.push fresh) x j :=
  ⟨h.live, (ReferenceHeap.external_frame (Array.getElem?_eq_some_iff.mp h.object).1 fresh).trans h.object⟩

end Jihoo.CommonDataReference
