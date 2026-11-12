import Jihoo.CommonDataReference
import Jihoo.CommonDataDestroy

/-! Executable abstract boxed binary Tree destruction. Native casts, pending
reuse, MIR CFG execution and whole-compiler correctness are outside this model. -/
namespace Jihoo.CommonDataReference
open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime

/-- Fuel bounds recursion depth, including boxed Nil. Execution inspects only
heap, root and fuel. Both children are saved before releasing the parent. -/
def drop (H : ReferenceHeap.Heap) (root : ReferenceHeap.Ref) : Nat →
    Option (ReferenceHeap.Heap × List Nat)
  | 0 => none
  | fuel + 1 => do
    let .object j 0 := root | none
    let tag ← ReferenceHeap.loadScalar H root
    if tag = 0 then
      pure (← ReferenceHeap.release H root, [j])
    else if tag = 1 then
      let left ← ReferenceHeap.loadRef H (.object j 1)
      let right ← ReferenceHeap.loadRef H (.object j 2)
      let start ← ReferenceHeap.release H root
      let (middle, ls) ← drop start left fuel
      let (finish, rs) ← drop middle right fuel
      pure (finish, j :: (ls ++ rs))
    else none

inductive Frees : ReferenceHeap.Heap → List Nat → ReferenceHeap.Heap → Prop where
  | nil : Frees H [] H
  | cons : ReferenceHeap.release H (.object j 0) = some K →
      Frees K js L → Frees H (j :: js) L

theorem Frees.append (a : Frees H xs K) (b : Frees K ys L) :
    Frees H (xs ++ ys) L := by
  induction a with
  | nil => exact b
  | cons h _ ih => exact .cons h (ih b)

theorem Frees.frame (run : Frees H ids K) (outside : j ∉ ids) : K[j]? = H[j]? := by
  induction run with
  | nil => rfl
  | @cons H x M xs K h tail ih =>
    have hs : j ≠ x ∧ j ∉ xs := by simpa using outside
    exact (ih hs.2).trans (ReferenceHeap.Frame.release_agree h j hs.1)

def deadObject (o : ReferenceHeap.Object) : ReferenceHeap.Object := {o with alive := false}

/-- Exact contents and absence: already-dead external objects remain unchanged. -/
theorem Frees.effect (run : Frees H ids K) (unique : ids.Nodup) :
    ∀ j, K[j]? = if j ∈ ids then H[j]?.map deadObject else H[j]? := by
  induction run with
  | nil => simp
  | @cons H x M xs K release tail ih =>
    obtain ⟨hx, distinct⟩ := List.nodup_cons.mp unique
    obtain ⟨obj, found, live, base, updated⟩ := ReferenceHeap.Frame.release_object release
    intro j
    by_cases eq : j = x
    · subst j
      rw [tail.frame hx, updated]
      simp [found, deadObject]
    · rw [ih distinct]
      rw [ReferenceHeap.Frame.release_agree release j eq]
      simp [eq]

def Image.depth : Image → Nat
  | .nil _ => 1
  | .node _ _ l r => max l.depth r.depth + 1

/-- Child success is derived, never assumed. No allocation capacity is needed. -/
theorem drop_total (layout : Layout H i) (unique : i.ids.Nodup)
    (enough : i.depth ≤ fuel) :
    ∃ K, drop H (.object i.target 0) fuel = some (K, i.ids) ∧ Frees H i.ids K := by
  induction i generalizing H fuel with
  | nil j =>
    cases fuel with
    | zero => simp [Image.depth] at enough
    | succ fuel =>
      obtain ⟨tag, freed, _⟩ := empty_case_total layout
      refine ⟨retired H j ReferenceHeap.nilObject, ?_, .cons freed .nil⟩
      simp [drop, Image.target, Image.ids, tag, freed]
  | node x j l r ihl ihr =>
    cases fuel with
    | zero => simp [Image.depth] at enough
    | succ fuel =>
      have bounds : l.depth ≤ fuel ∧ r.depth ≤ fuel := by
        simpa [Image.depth, Nat.max_le] using enough
      obtain ⟨rootApart, children⟩ := List.nodup_cons.mp unique
      obtain ⟨ul, ur, apart⟩ := List.nodup_append.mp children
      have release : ReferenceHeap.release H (.object j 0) =
          some (retired H j (Image.node x j l r).object) :=
        ReferenceHeap.Frame.release_success_iff.mpr ⟨_, layout.1, rfl, rfl, rfl⟩
      have leftLayout : Layout (retired H j (Image.node x j l r).object) l :=
        layout.2.1.congr (fun k hk => ReferenceHeap.Frame.release_agree release k
          (fun eq => rootApart (List.mem_append_left _ (eq ▸ hk))))
      obtain ⟨M, leftRun, leftFrees⟩ := ihl leftLayout ul bounds.1
      have rightLayout : Layout M r := by
        apply layout.2.2.congr
        intro k hk
        rw [leftFrees.frame (fun hl => apart k hl k hk rfl)]
        exact ReferenceHeap.Frame.release_agree release k
          (fun eq => rootApart (List.mem_append_right _ (eq ▸ hk)))
      obtain ⟨K, rightRun, rightFrees⟩ := ihr rightLayout ur bounds.2
      refine ⟨K, ?_, .cons release (leftFrees.append rightFrees)⟩
      have tag : ReferenceHeap.loadScalar H (.object j 0) = some 1 := tag_total layout
      have refs := children_total layout
      change drop H (.object j 0) (fuel + 1) = some (K, j :: (l.ids ++ r.ids))
      simp [drop, tag, refs.1, refs.2, release, leftRun, rightRun]

/-- Both executions follow preorder, but target includes extra boxed Nil frees.
Source identities correspond via pairs, not numeric identity or raw trace equality. -/
theorem destroy_correspondence (related : Related s H i)
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (i.source.owners ++ frame))
    (enough : i.depth ≤ fuel) :
    ∃ t K, CommonData.Destroy (root i.source) s (i.source.owners.map Event.free) t ∧
      Steps s.buffers.heap (i.source.owners.map Event.free) t.buffers.heap ∧
      Valid t.buffers.heap ∧ Owns t.buffers.heap frame ∧
      drop H (.object i.target 0) fuel = some (K, i.ids) ∧ Frees H i.ids K ∧
      (∀ j, K[j]? = if j ∈ i.ids then H[j]?.map deadObject else H[j]?) ∧
      i.pairs.map Prod.fst = i.source.owners ∧
      (∀ j, i.ids.count j = (i.pairs.map Prod.snd).count j + i.nils.count j) ∧
      i.nils.length = i.source.owners.length + 1 := by
  obtain ⟨t, source, steps, vt, kept⟩ := CommonData.destroy_total related.fields valid owned
  obtain ⟨K, target, frees⟩ := drop_total related.layout related.distinct enough
  exact ⟨t, K, source, steps, vt, kept, target, frees, frees.effect related.distinct,
    source_pairs i, resource_count i, nil_count i⟩

/-- Source destruction changes only live bits and removed node cells. -/
theorem source_unchanged (run : CommonData.Destroy ref s es t) :
    t.buffers.heap.payload = s.buffers.heap.payload ∧
    t.buffers.heap.lease = s.buffers.heap.lease ∧
    t.buffers.heap.nextObject = s.buffers.heap.nextObject ∧
    t.buffers.heap.nextLease = s.buffers.heap.nextLease := by
  induction run with
  | empty => exact ⟨rfl, rfl, rfl, rfl⟩
  | node _ _ _ ihl ihr =>
    simpa [CommonData.finish, RecursiveCaseBody.finish, SizedBufferHeap.release] using
      And.intro (ihr.1.trans ihl.1) (And.intro (ihr.2.1.trans ihl.2.1)
        (And.intro (ihr.2.2.1.trans ihl.2.2.1) (ihr.2.2.2.trans ihl.2.2.2)))

theorem source_live_frame (run : CommonData.Destroy ref s es t)
    (outside : x ∉ released es) : t.buffers.heap.live x = s.buffers.heap.live x := by
  induction run with
  | empty => rfl
  | @node cell s y left middle right t lookup l r ihl ihr =>
    have parts : x ≠ y ∧ x ∉ released left ∧ x ∉ released right := by
      simpa [released, List.filterMap_append] using outside
    rw [ihr parts.2.2, ihl parts.2.1]
    simp [CommonData.finish, RecursiveCaseBody.finish, SizedBufferHeap.release, put, parts.1]

/-- Any independently retained finite Tree keeps the same source fields, owners
and exact target objects. This applies to the runs constructed above. -/
theorem retained_tree {i : Image} (source : CommonData.Destroy (root i.source) s
    (i.source.owners.map Event.free) t) (target : Frees H i.ids K)
    (kept : Related s H retained)
    (sourceApart : ∀ x ∈ retained.source.owners, x ∉ i.source.owners)
    (targetApart : ∀ j ∈ retained.ids, j ∉ i.ids) : Related t K retained := by
  have absent : ∀ x ∈ retained.source.owners, x ∉ released (i.source.owners.map Event.free) := by
    simpa [released, Function.comp_def] using sourceApart
  refine ⟨kept.fields.congr (fun x hx => source.cells_frame (absent x hx)), ?_,
    kept.layout.congr (fun j hj => target.frame (targetApart j hj)), kept.distinct⟩
  exact ⟨kept.owned.distinct,
    fun x hx => (source_live_frame source (absent x hx)).trans (kept.owned.live x hx),
    by simpa [HeapLeases.Unborrowed, (source_unchanged source).2.1] using kept.owned.leaseFree⟩

theorem retained_buffer {i : Image} (source : CommonData.Destroy (root i.source) s
    (i.source.owners.map Event.free) t) (target : Frees H i.ids K)
    (kept : BufferRelated s H x j) (sourceApart : x ∉ i.source.owners)
    (targetApart : j ∉ i.ids) : BufferRelated t K x j := by
  constructor
  · exact (source_live_frame source (by simpa [released, Function.comp_def] using sourceApart)).trans kept.live
  · rw [target.frame targetApart, source.lengths, (source_unchanged source).1]
    exact kept.object

/-- Existing Destroy determinism transfers the correspondence to any observed
source run, rather than choosing a source execution after seeing the target. -/
theorem every_source_run (related : Related s H i) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (i.source.owners ++ frame))
    (source : CommonData.Destroy (root i.source) s es t) (enough : i.depth ≤ fuel) :
    es = i.source.owners.map Event.free ∧
    (∀ x ∈ i.source.owners, t.buffers.heap.live x = false) ∧
    ∃ K, drop H (.object i.target 0) fuel = some (K, i.ids) ∧
      (∀ j, K[j]? = if j ∈ i.ids then H[j]?.map deadObject else H[j]?) := by
  obtain ⟨rfl, steps, _, _⟩ := CommonData.destroy_every_run related.fields valid owned source
  obtain ⟨K, run, frees⟩ := drop_total related.layout related.distinct enough
  exact ⟨rfl, fun x hx => released_dead valid steps (List.mem_map.mpr ⟨x, hx, rfl⟩),
    K, run, frees.effect related.distinct⟩

end Jihoo.CommonDataReference
