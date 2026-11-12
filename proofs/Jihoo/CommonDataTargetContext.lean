import Jihoo.TreeDropCall
import Jihoo.SymbolicCommonDataSource

/-! Resource contexts at callable boxed Tree Drop boundaries, not body lowering
or native correctness. Lexical aliases are distinct from ownership slots. -/
namespace Jihoo.CommonDataTargetContext
open CommonDataReference RecursiveLexicalFields RecursiveFieldRuntime
open RecursiveFieldOwnership HeapLeases LinearHeapPrograms

inductive Resource where
  | data (image : Image)
  | buffer (source target : Nat)
  deriving Repr, DecidableEq

def Resource.source : Resource → Capability
  | .data i => .data i.source
  | .buffer x _ => .buffer x

def Resource.ids : Resource → List Nat
  | .data i => i.ids
  | .buffer _ j => [j]

def Resource.Related (s : CommonData.State) (H : ReferenceHeap.Heap) : Resource → Prop
  | .data i => CommonDataReference.Related s H i
  | .buffer x j => BufferRelated s H x j

def sources (rs : List Resource) := rs.map Resource.source
def targets (rs : List Resource) := rs.flatMap Resource.ids

/-- Only shell authority: a pending parent's children may already be stale. -/
structure Pending where
  source : Nat
  target : Nat
  object : ReferenceHeap.Object

def Pending.Valid (s : CommonData.State) (H : ReferenceHeap.Heap) (a : Pending) : Prop :=
  s.buffers.heap.live a.source = true ∧ H[a.target]? = some a.object ∧ a.object.alive = true

def Local (f : ReferenceCfg.Frame) (slot : Nat) (value : ReferenceCfg.Value) : Prop :=
  f.locals[slot]? = some (some value)

/-- Dead and erased entries impose no local constraint; consuming authority
need not clear the old pointer. All lexical operands are non-dereferencing. -/
def Binding (rs : List Resource) (f : ReferenceCfg.Frame) : Entry → Nat → Prop
  | .data k, slot => ∃ i, rs[k]? = some (.data i) ∧ Local f slot (.pointer i.target 0)
  | .buffer k, slot => ∃ x j, rs[k]? = some (.buffer x j) ∧ Local f slot (.pointer j 0)
  | .nat n, slot => Local f slot (.u64 n)
  | .scalar, slot => ∃ n, Local f slot (.i64 n)
  | .ghost, _ | .dead, _ => True

inductive Bindings (rs : List Resource) (f : ReferenceCfg.Frame) : List Entry → List Nat → Prop where
  | nil : Bindings rs f [] []
  | cons : Binding rs f e slot → Bindings rs f ctx slots →
      Bindings rs f (e :: ctx) (slot :: slots)

theorem Bindings.lookup {k : Nat} (h : Bindings rs f ctx slots) (lookup : ctx[k]? = some e) :
    ∃ slot, slots[k]? = some slot ∧ Binding rs f e slot := by
  induction h generalizing k with
  | nil => simp at lookup
  | cons head tail ih =>
    cases k with
    | zero => cases Option.some.inj lookup; exact ⟨_, rfl, head⟩
    | succ k => exact ih lookup

/-- Binder extension does not itself create ownership. -/
theorem Bindings.bind (h : Bindings rs f ctx slots) (new : Binding rs f e slot) :
    Bindings rs f (e :: ctx) (slot :: slots) := .cons new h

/-- Extensible pointwise reindexing/partition law; no execution premise. -/
theorem Bindings.map (h : Bindings rs f ctx slots)
    (law : ∀ e slot, Binding rs f e slot → Binding ts g (change e) slot) :
    Bindings ts g (ctx.map change) slots := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (law _ _ head) ih

theorem Binding.remove (h : Binding (.data i :: rs) f e slot) :
    Binding rs f (CommonData.removeEntry e) slot := by
  cases e with
  | data k | buffer k => cases k <;> first | trivial | exact h
  | nat _ | scalar | ghost | dead => exact h

theorem Bindings.remove (h : Bindings (.data i :: rs) f ctx slots) :
    Bindings rs f (CommonData.removeHead ctx) slots := h.map (fun _ _ h => h.remove)

def Active : Entry → Prop
  | .data _ | .buffer _ | .nat _ | .scalar => True
  | .ghost | .dead => False

/-- Site checks the unit destination's type, but surviving locals must also
exclude it. This covers scalar/nat locals as well as resource pointers. -/
def Fresh (ctx : List Entry) (slots : List Nat) (dest : Nat) : Prop :=
  ∀ (k : Nat) e slot, ctx[k]? = some e → slots[k]? = some slot → Active e → slot ≠ dest

theorem Binding.resume (h : Binding rs s.frame e slot) (apart : Active e → slot ≠ dest) :
    Binding rs (TreeDropCall.resume s dest continuation K).frame e slot := by
  cases e with
  | data k =>
    obtain ⟨i, hi, hv⟩ := h
    exact ⟨i, hi, (TreeDropCall.resume_local (apart trivial)).trans hv⟩
  | buffer k =>
    obtain ⟨x, j, hi, hv⟩ := h
    exact ⟨x, j, hi, (TreeDropCall.resume_local (apart trivial)).trans hv⟩
  | nat n => exact (TreeDropCall.resume_local (apart trivial)).trans h
  | scalar =>
    obtain ⟨n, hv⟩ := h
    exact ⟨n, (TreeDropCall.resume_local (apart trivial)).trans hv⟩
  | ghost | dead => trivial

theorem Bindings.resume (h : Bindings rs s.frame ctx slots) (fresh : Fresh ctx slots dest) :
    Bindings rs (TreeDropCall.resume s dest continuation K).frame ctx slots := by
  induction h with
  | nil => exact .nil
  | @cons e slot ctx slots head tail ih =>
    exact .cons (head.resume (fresh 0 e slot rfl rfl))
      (ih (fun k e slot he hs => fresh (k+1) e slot he hs))

theorem local_operand (h : Local f slot v) :
    ReferenceCfg.operand f (TreeDropCall.arg slot) = some v := by
  simp [ReferenceCfg.operand, TreeDropCall.arg, Local] at h ⊢
  rw [h]
  rfl

/-- Each resource occurs once in the ownership inventory, regardless of how
many lexical aliases refer to its slot. Target Nil has its own target resource.
External target objects may be dead or absent. -/
structure Context (rs : List Resource) (pending : List Pending)
    (sourceFrame targetFrame : List Nat) (ctx : List Entry) (env : List Value)
    (slots : List Nat) (s : CommonData.State) (f : ReferenceCfg.Frame) : Prop where
  valid : Valid s.buffers.heap
  agreement : Agrees (sources rs) ctx env
  bindings : Bindings rs f ctx slots
  resources : ∀ r ∈ rs, r.Related s f.heap
  owned : Owns s.buffers.heap
    (footprint (sources rs) ++ (pending.map Pending.source ++ sourceFrame))
  separated : (targets rs ++ (pending.map Pending.target ++ targetFrame)).Nodup
  shells : ∀ a ∈ pending, a.Valid s f.heap

theorem Context.data_lookup {k n : Nat} (h : Context rs pending sf tf ctx env slots source f)
    (lookup : ctx[k]? = some (.data n)) :
    ∃ i slot, rs[n]? = some (.data i) ∧ slots[k]? = some slot ∧
      env[k]? = some (.data (root i.source)) ∧
      ReferenceCfg.operand f (TreeDropCall.arg slot) = some (.pointer i.target 0) ∧
      CommonDataReference.Related source f.heap i := by
  obtain ⟨slot, hs, i, hi, hvlocal⟩ := h.bindings.lookup lookup
  refine ⟨i, slot, hi, hs, ?_, local_operand hvlocal, h.resources _ (List.mem_of_getElem? hi)⟩
  exact CommonData.data_lookup h.agreement lookup (by simp [sources, hi, Resource.source])

theorem Context.buffer_lookup {k n : Nat} (h : Context rs pending sf tf ctx env slots source f)
    (lookup : ctx[k]? = some (.buffer n)) :
    ∃ x j slot, rs[n]? = some (.buffer x j) ∧ slots[k]? = some slot ∧
      env[k]? = some (.buffer x) ∧
      ReferenceCfg.operand f (TreeDropCall.arg slot) = some (.pointer j 0) ∧
      BufferRelated source f.heap x j := by
  obtain ⟨slot, hs, x, j, hi, hvlocal⟩ := h.bindings.lookup lookup
  obtain ⟨v, hv, y, hy, rfl⟩ := h.agreement.lookup lookup
  have eq : x = y := by simpa [sources, hi, Resource.source] using hy
  subst y
  exact ⟨x, j, slot, hi, hs, hv, local_operand hvlocal, h.resources _ (List.mem_of_getElem? hi)⟩

private theorem source_member (hr : r ∈ rs) (hx : x ∈ r.source.owners) :
    x ∈ footprint (sources rs) :=
  footprint_member (List.mem_map.mpr ⟨r, hr, rfl⟩) hx

private theorem target_member (hr : r ∈ rs) (hj : j ∈ r.ids) : j ∈ targets rs :=
  List.mem_flatMap.mpr ⟨r, hr, hj⟩

/-- Context after actual destruction: every consumed alias is dead, while
retained resources, pending parents, and ambient frames are preserved. -/
theorem Context.after_drop (h : Context (.data i :: rs) pending sf tf ctx env slots source s.frame)
    (destroy : CommonData.Destroy (root i.source) source (i.source.owners.map Event.free) middle)
    (frees : Frees s.frame.heap i.ids K)
    (fresh : Fresh (CommonData.removeHead ctx) slots dest) :
    Context rs pending sf tf (CommonData.removeHead ctx) env slots middle
      (TreeDropCall.resume s dest continuation K).frame := by
  have rel : CommonDataReference.Related source s.frame.heap i := h.resources (.data i) (by simp)
  have own : Owns source.buffers.heap
      (i.source.owners ++ (footprint (sources rs) ++ (pending.map Pending.source ++ sf))) := by
    simpa [sources, footprint, Resource.source, Capability.owners, List.append_assoc] using h.owned
  obtain ⟨_, _, valid, owned⟩ := CommonData.destroy_every_run rel.fields h.valid own destroy
  have sapart := (List.nodup_append.mp own.distinct).2.2
  have sep : (i.ids ++ (targets rs ++ (pending.map Pending.target ++ tf))).Nodup := by
    simpa [targets, Resource.ids, List.append_assoc] using h.separated
  have tapart := (List.nodup_append.mp sep).2.2
  refine ⟨valid, CommonData.agrees_remove h.agreement,
    h.bindings.remove.resume fresh, ?_, owned, (List.nodup_append.mp sep).2.1, ?_⟩
  · intro r hr
    have kept := h.resources r (by simp [hr])
    have sa : ∀ x ∈ r.source.owners, x ∉ i.source.owners := by
      intro x hx hi
      exact sapart x hi x (List.mem_append_left _ (source_member hr hx)) rfl
    have ta : ∀ j ∈ r.ids, j ∉ i.ids := by
      intro j hj hi
      exact tapart j hi j (List.mem_append_left _ (target_member hr hj)) rfl
    cases r with
    | data a => exact retained_tree destroy frees kept sa ta
    | buffer x j =>
      exact retained_buffer destroy frees kept (sa x (by simp [Resource.source, Capability.owners]))
        (ta j (by simp [Resource.ids]))
  · intro a ha
    obtain ⟨live, obj, alive⟩ := h.shells a ha
    have sa : a.source ∉ i.source.owners := by
      intro hx
      exact sapart _ hx _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩))) rfl
    have ta : a.target ∉ i.ids := by
      intro hj
      exact tapart _ hj _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩))) rfl
    exact ⟨(source_live_frame destroy (by simpa [released, Function.comp_def] using sa)).trans live,
      (frees.frame ta).trans obj, alive⟩

/-- Constructs source Destroy and the actual caller/callee/return prefix.
No body success, BodyIH, or arbitrary Post is assumed. -/
theorem drop_prefix {k : Nat} (h : Context (.data i :: rs) pending sf tf ctx env slots source s.frame)
    (selected : ctx[k]? = some (.data 0))
    (installed : p[dropId]? = some (TreeDropCall.body dropId))
    (site : TreeDropCall.Site p s dest continuation)
    (callAt : ∀ slot, slots[k]? = some slot → ∃ fn, p[s.function]? = some fn ∧
      ReferenceCalls.extension fn.code s.frame = some (.call
        (TreeDropCall.call dropId (TreeDropCall.arg slot) dest continuation)))
    (fresh : Fresh (CommonData.removeHead ctx) slots dest)
    (depth : s.stack.length + 1 + i.depth ≤ limit) :
    ∃ middle K,
      CommonData.Destroy (root i.source) source (i.source.owners.map Event.free) middle ∧
      ReferenceCalls.Steps p (.running s) (i.ids.map HeapLifecycle.Event.free)
        (.running (TreeDropCall.resume s dest continuation K)) ∧
      Context rs pending sf tf (CommonData.removeHead ctx) env slots middle
        (TreeDropCall.resume s dest continuation K).frame ∧
      (∀ j, K[j]? = if j ∈ i.ids then s.frame.heap[j]?.map deadObject else s.frame.heap[j]?) := by
  obtain ⟨a, slot, ha, hs, _, operand, related⟩ := h.data_lookup selected
  have eq : i = a := by simpa using ha
  subst a
  have own : Owns source.buffers.heap
      (i.source.owners ++ (footprint (sources rs) ++ (pending.map Pending.source ++ sf))) := by
    simpa [sources, footprint, Resource.source, Capability.owners, List.append_assoc] using h.owned
  obtain ⟨middle, destroyed, _, _, _⟩ := CommonData.destroy_total related.fields h.valid own
  obtain ⟨K, steps, frees⟩ := TreeDropCall.invoke installed site (callAt slot hs)
    operand related.layout related.distinct depth
  exact ⟨middle, K, destroyed, steps, h.after_drop destroyed frees fresh, frees.effect related.distinct⟩



/-- A Case replaces parent authority by two child slots; all parent aliases
are retired, and other resource indices shift without moving lexical locals. -/
theorem Binding.children (h : Binding (.data parent :: rs) f e slot) :
    Binding (.data left :: .data right :: rs) f (retireEntry e) slot := by
  cases e with
  | data k | buffer k => cases k <;> first | trivial | exact h
  | nat _ | scalar | ghost | dead => exact h

theorem Bindings.ghosts (h : Bindings rs f ctx slots) (ghostSlots : List Nat) :
    Bindings rs f (List.replicate ghostSlots.length .ghost ++ ctx) (ghostSlots ++ slots) := by
  induction ghostSlots with
  | nil => exact h
  | cons slot rest ih => exact .cons trivial ih

theorem Bindings.children (h : Bindings (.data parent :: rs) f ctx slots)
    (ll : Local f leftSlot (.pointer left.target 0))
    (rl : Local f rightSlot (.pointer right.target 0)) (ghostSlots : List Nat) :
    Bindings (.data left :: .data right :: rs) f (bindContext ghostSlots.length ctx)
      (rightSlot :: leftSlot :: (ghostSlots ++ slots)) :=
  .cons ⟨right, rfl, rl⟩ (.cons ⟨left, rfl, ll⟩
    ((h.map (fun _ _ h => h.children)).ghosts ghostSlots))

/-- Actual Case opening plus an inventory/binder law. Child locals are the
explicit interface for later lowering of field loads; no branch run is assumed. -/
theorem Context.open_case {k : Nat}
    (h : Context (.data (.node x j left right) :: rs) pending sf tf ctx env slots source f)
    (selected : ctx[k]? = some (.data 0))
    (ll : Local f leftSlot (.pointer left.target 0))
    (rl : Local f rightSlot (.pointer right.target 0)) (ghostSlots : List Nat) :
    RecursiveLexicalFields.enter source.recursive env k ghostSlots.length =
      some (bindValues ghostSlots.length ⟨root left.source, root right.source⟩ env, x) ∧
    openNode f.heap j = some (.object left.target 0, .object right.target 0) ∧
    Context (.data left :: .data right :: rs)
      (⟨x, j, (Image.node x j left right).object⟩ :: pending) sf tf
      (bindContext ghostSlots.length ctx)
      (bindValues ghostSlots.length ⟨root left.source, root right.source⟩ env)
      (rightSlot :: leftSlot :: (ghostSlots ++ slots)) source f := by
  have parent : CommonDataReference.Related source f.heap (.node x j left right) :=
    h.resources (.data (.node x j left right)) (by simp)
  have selectedValue : env[k]? = some (.data (some x)) :=
    CommonData.data_lookup h.agreement selected rfl
  obtain ⟨entered, opened, lh, rh⟩ := case_open_total parent selectedValue (ghosts := ghostSlots.length)
  refine ⟨entered, opened, h.valid, h.agreement.bind,
    h.bindings.children ll rl ghostSlots, ?_, ?_, ?_, ?_⟩
  · intro r member
    rcases List.mem_cons.mp member with rfl | member
    · exact lh
    rcases List.mem_cons.mp member with rfl | member
    · exact rh
    · exact h.resources r (List.mem_cons_of_mem _ member)
  · apply CommonData.move_pending
    simpa [sources, footprint, Resource.source, Capability.owners, Image.source,
      Tree.owners, List.append_assoc] using h.owned
  · have old : (j :: ((left.ids ++ right.ids ++ targets rs) ++
        (pending.map Pending.target ++ tf))).Nodup := by
      simpa [targets, Resource.ids, Image.ids, List.append_assoc] using h.separated
    have perm : (j :: ((left.ids ++ right.ids ++ targets rs) ++
        (pending.map Pending.target ++ tf))).Perm
        ((left.ids ++ right.ids ++ targets rs) ++ (j :: (pending.map Pending.target ++ tf))) := by
      simpa [List.append_assoc] using
        (List.perm_append_comm (l₁ := [j]) (l₂ := left.ids ++ right.ids ++ targets rs)).append_right
          (pending.map Pending.target ++ tf)
    simpa [targets, Resource.ids, List.append_assoc] using perm.nodup_iff.mp old
  · intro a member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨parent.owned.live x (by simp [Image.source, Tree.owners]), parent.layout.1, rfl⟩
    · exact h.shells a member

/-- Exposes the source derivation's continuation and selected alias, without
an Eval or a successful body execution premise. -/
theorem typing_drop {k : Nat} (typed : CommonData.Typing g ctx (count+1) sizes term kind)
    (shape : CommonData.nodeAt g term = .drop 0 owner body)
    (ownerShape : CommonData.nodeAt g owner = .core (.var k)) :
    ctx[k]? = some (.data 0) ∧
      CommonData.Typing g (CommonData.removeHead ctx) count sizes body kind := by
  cases typed <;> simp_all

/-- The symbolic source judgment closes into precisely the same Drop boundary. -/
theorem symbolic_typing_drop {k : Nat}
    (typed : SymbolicCommonDataSource.Typing g symbolic (count+1) sizes term kind)
    (closing : SymbolicCommonDataContext.Closes symbolic ctx)
    (inventory : SymbolicCoreContext.SizesEval (SymbolicCommonDataContext.naturalEnv ctx) sizes concrete)
    (shape : CommonDataSource.nodeAt g term = .drop 0 owner body)
    (ownerShape : CommonDataSource.nodeAt g owner = .core (.var k)) :
    ctx[k]? = some (.data 0) ∧
      CommonData.Typing (CommonDataSourceRules.graph g) (CommonData.removeHead ctx) count concrete body kind := by
  apply typing_drop (owner := owner) ((typed.instantiate closing inventory).elaborate)
  · simp [CommonDataSourceRules.adapted_at, shape, CommonDataSourceRules.adaptNode, CommonDataSource.adaptNode]
  · simp [CommonDataSourceRules.adapted_at, ownerShape, CommonDataSourceRules.adaptNode, CommonDataSource.adaptNode]



/-- The common judgment's ordered Data prefix and Buffer suffix. -/
def inventory (images : List Image) (buffers : List (Nat × Nat)) : List Resource :=
  images.map Resource.data ++ buffers.map (fun (x,j) => Resource.buffer x j)

theorem sources_inventory : sources (inventory images buffers) =
    CommonData.caps (images.map Image.source) (buffers.map Prod.fst) := by
  simp [sources, inventory, CommonData.caps, List.map_map, Function.comp_def, Resource.source]

structure CommonContext (images : List Image) (buffers : List (Nat × Nat))
    (sizes : List Nat) (pending : List Pending) (sf tf : List Nat)
    (ctx : List Entry) (env : List Value) (slots : List Nat)
    (source : CommonData.State) (f : ReferenceCfg.Frame) : Prop extends
    Context (inventory images buffers) pending sf tf ctx env slots source f where
  bufferSizes : SizedBufferContext.Layout source.buffers (buffers.map Prod.fst) sizes

theorem CommonContext.after_drop
    (h : CommonContext (i :: images) buffers sizes pending sf tf ctx env slots source s.frame)
    (destroy : CommonData.Destroy (root i.source) source (i.source.owners.map Event.free) middle)
    (frees : Frees s.frame.heap i.ids K)
    (fresh : Fresh (CommonData.removeHead ctx) slots dest) :
    CommonContext images buffers sizes pending sf tf (CommonData.removeHead ctx) env slots middle
      (TreeDropCall.resume s dest continuation K).frame := by
  refine ⟨h.toContext.after_drop destroy frees fresh, h.bufferSizes.length, ?_⟩
  intro k x n hx hn
  rw [destroy.lengths]
  exact h.bufferSizes.lookup k x n hx hn

variable {active retained : List Image} {used saved : List (Nat × Nat)}

theorem Binding.argument (h : Binding (inventory (active ++ retained) (used ++ saved)) f e slot) :
    Binding (inventory active used) f
      (CommonData.argumentEntry active.length retained.length used.length e) slot := by
  cases e with
  | data k =>
    by_cases bound : k < active.length
    · obtain ⟨i, lookup, hv⟩ := h
      simp only [CommonData.argumentEntry, bound]
      refine ⟨i, ?_, hv⟩
      simpa [inventory, List.map_append, List.getElem?_append, bound] using lookup
    · simp [CommonData.argumentEntry, bound, Binding]
  | buffer k =>
    by_cases bound : active.length + retained.length ≤ k ∧ k < active.length + retained.length + used.length
    · obtain ⟨x, j, lookup, hv⟩ := h
      simp only [CommonData.argumentEntry, bound]
      refine ⟨x, j, ?_, hv⟩
      have a : ¬ k < active.length := by omega
      have r : ¬ k - active.length < retained.length := by omega
      have b : k - active.length - retained.length < used.length := by omega
      have n : ¬ k - retained.length < active.length := by omega
      have same : k - retained.length - active.length = k - active.length - retained.length := by omega
      simpa [inventory, List.map_append, List.append_assoc, List.getElem?_append, a, r, b, n, same] using lookup
    · simp [CommonData.argumentEntry, bound, Binding]
  | nat _ | scalar | ghost | dead => exact h

theorem Binding.captured (h : Binding (inventory (active ++ retained) (used ++ saved)) f e slot) :
    Binding (inventory (result :: retained) saved) f
      (CommonData.capturedEntry active.length retained.length used.length e) slot := by
  cases e with
  | data k =>
    by_cases bound : active.length ≤ k ∧ k < active.length + retained.length
    · obtain ⟨i, lookup, hv⟩ := h
      simp only [CommonData.capturedEntry, bound]
      refine ⟨i, ?_, hv⟩
      have a : ¬ k < active.length := by omega
      have r : k - active.length < retained.length := by omega
      simpa [inventory, List.map_append, List.append_assoc, List.getElem?_append, a, r, Nat.add_comm] using lookup
    · simp [CommonData.capturedEntry, bound, Binding]
  | buffer k =>
    by_cases bound : active.length + retained.length + used.length ≤ k
    · obtain ⟨x, j, lookup, hv⟩ := h
      simp only [CommonData.capturedEntry, bound]
      refine ⟨x, j, ?_, hv⟩
      have a : ¬ k < active.length := by omega
      have r : ¬ k - active.length < retained.length := by omega
      have b : ¬ k - active.length - retained.length < used.length := by omega
      have n : ¬ retained.length + (k - (active.length + retained.length + used.length)) < retained.length := by omega
      have same : k - active.length - retained.length - used.length = k - (active.length + retained.length + used.length) := by omega
      have index : 1 + retained.length + (k - (active.length + retained.length + used.length)) =
          (retained.length + (k - (active.length + retained.length + used.length))) + 1 := by omega
      rw [index]
      simp only [inventory, List.map_cons, List.cons_append, List.getElem?_cons_succ]
      simpa [inventory, List.map_append, List.append_assoc, List.getElem?_append, a, r, b, n, same] using lookup
    · simp [CommonData.capturedEntry, bound, Binding]
  | nat _ | scalar | ghost | dead => exact h

theorem Bindings.argument (h : Bindings (inventory (active ++ retained) (used ++ saved)) f ctx slots) :
    Bindings (inventory active used) f
      (CommonData.argumentContext active.length retained.length used.length ctx) slots :=
  h.map (fun _ _ h => h.argument)

theorem Bindings.captured (h : Bindings (inventory (active ++ retained) (used ++ saved)) f ctx slots)
    (value : Local f resultSlot (.pointer result.target 0)) :
    Bindings (inventory (result :: retained) saved) f
      (CommonData.capturedContext active.length retained.length used.length ctx) (resultSlot :: slots) :=
  .cons ⟨result, rfl, value⟩ (h.map (fun _ _ h => h.captured))

/-- Typed common Drop obtains its selected operand and continuation context
from the derivation, never from an assumed successful body run. -/
theorem typed_drop_prefix {k : Nat}
    (h : CommonContext (i :: images) buffers sizes pending sf tf ctx env slots source s.frame)
    (typed : CommonData.Typing g ctx (images.length+1) sizes term kind)
    (shape : CommonData.nodeAt g term = .drop 0 owner body)
    (ownerShape : CommonData.nodeAt g owner = .core (.var k))
    (installed : p[dropId]? = some (TreeDropCall.body dropId))
    (site : TreeDropCall.Site p s dest continuation)
    (callAt : ∀ slot, slots[k]? = some slot → ∃ fn, p[s.function]? = some fn ∧
      ReferenceCalls.extension fn.code s.frame = some (.call
        (TreeDropCall.call dropId (TreeDropCall.arg slot) dest continuation)))
    (fresh : Fresh (CommonData.removeHead ctx) slots dest)
    (depth : s.stack.length + 1 + i.depth ≤ limit) :
    CommonData.Typing g (CommonData.removeHead ctx) images.length sizes body kind ∧
    ∃ middle K,
      CommonData.Destroy (root i.source) source (i.source.owners.map Event.free) middle ∧
      ReferenceCalls.Steps p (.running s) (i.ids.map HeapLifecycle.Event.free)
        (.running (TreeDropCall.resume s dest continuation K)) ∧
      CommonContext images buffers sizes pending sf tf (CommonData.removeHead ctx) env slots middle
        (TreeDropCall.resume s dest continuation K).frame ∧
      (∀ j, K[j]? = if j ∈ i.ids then s.frame.heap[j]?.map deadObject else s.frame.heap[j]?) := by
  obtain ⟨lookup, bodyTyped⟩ := typing_drop typed shape ownerShape
  obtain ⟨middle, K, destroyed, steps, ctxAfter, effect⟩ :=
    drop_prefix h.toContext lookup installed site callAt fresh depth
  refine ⟨bodyTyped, middle, K, destroyed, steps, ⟨ctxAfter, h.bufferSizes.length, ?_⟩, effect⟩
  intro k x n hx hn
  rw [destroyed.lengths]
  exact h.bufferSizes.lookup k x n hx hn



/-- Symbolic sizes and binders close through the existing source judgment.
The returned context is at the actual target continuation entry. -/
theorem symbolic_drop_prefix {k : Nat}
    (h : CommonContext (i :: images) buffers concrete pending sf tf ctx env slots source s.frame)
    (typed : SymbolicCommonDataSource.Typing g symbolic (images.length+1) sizes term kind)
    (closing : SymbolicCommonDataContext.Closes symbolic ctx)
    (sizeValues : SymbolicCoreContext.SizesEval (SymbolicCommonDataContext.naturalEnv ctx) sizes concrete)
    (shape : CommonDataSource.nodeAt g term = .drop 0 owner body)
    (ownerShape : CommonDataSource.nodeAt g owner = .core (.var k))
    (installed : p[dropId]? = some (TreeDropCall.body dropId))
    (site : TreeDropCall.Site p s dest continuation)
    (callAt : ∀ slot, slots[k]? = some slot → ∃ fn, p[s.function]? = some fn ∧
      ReferenceCalls.extension fn.code s.frame = some (.call
        (TreeDropCall.call dropId (TreeDropCall.arg slot) dest continuation)))
    (fresh : Fresh (CommonData.removeHead ctx) slots dest)
    (depth : s.stack.length + 1 + i.depth ≤ limit) :
    CommonData.Typing (CommonDataSourceRules.graph g) (CommonData.removeHead ctx)
      images.length concrete body kind ∧
    ∃ middle K,
      CommonData.Destroy (root i.source) source (i.source.owners.map Event.free) middle ∧
      ReferenceCalls.Steps p (.running s) (i.ids.map HeapLifecycle.Event.free)
        (.running (TreeDropCall.resume s dest continuation K)) ∧
      CommonContext images buffers concrete pending sf tf (CommonData.removeHead ctx) env slots middle
        (TreeDropCall.resume s dest continuation K).frame ∧
      (∀ j, K[j]? = if j ∈ i.ids then s.frame.heap[j]?.map deadObject else s.frame.heap[j]?) := by
  apply typed_drop_prefix h ((typed.instantiate closing sizeValues).elaborate)
    (owner := owner) (k := k) (dropId := dropId) (limit := limit)
  · simp [CommonDataSourceRules.adapted_at, shape, CommonDataSourceRules.adaptNode, CommonDataSource.adaptNode]
  · simp [CommonDataSourceRules.adapted_at, ownerShape, CommonDataSourceRules.adaptNode, CommonDataSource.adaptNode]
  · exact installed
  · exact site
  · exact callAt
  · exact fresh
  · exact depth



/-- Return writes exactly one local. Heap reads through consumed pointers are
intentionally excluded; arbitrary other direct operands retain their value. -/
theorem resume_operand (different : slot ≠ dest) :
    ReferenceCfg.operand (TreeDropCall.resume s dest continuation K).frame (TreeDropCall.arg slot) =
      ReferenceCfg.operand s.frame (TreeDropCall.arg slot) := by
  simp [ReferenceCfg.operand, TreeDropCall.arg, TreeDropCall.resume_local different]

/-- Resource accounting deliberately distinguishes source nodes and target-only
Nil boxes; the two destruction traces need not have equal length. -/
theorem data_accounting (i : Image) :
    i.pairs.map Prod.fst = i.source.owners ∧
    (∀ j, i.ids.count j = (i.pairs.map Prod.snd).count j + i.nils.count j) ∧
    i.nils.length = i.source.owners.length + 1 :=
  ⟨source_pairs i, resource_count i, nil_count i⟩

end Jihoo.CommonDataTargetContext
