import Jihoo.RecursiveFieldOwnership

/-! Runtime field interpretation for finite binary owned trees. Field references
are stored independently of the ownership witness and read by `take`. This is
an abstract pointer heap, not native bytes or a source Core Case judgment. -/
namespace Jihoo.RecursiveFieldRuntime
open HeapLeases LinearHeapPrograms OwnedCoreContinuation RecursiveFieldOwnership

abbrev Ref := Option Nat

def root : Tree → Ref
  | .empty => none
  | .node x _ _ => some x

structure Cell where
  left : Ref
  right : Ref
  deriving DecidableEq, Repr

abbrev Cells := Nat → Option Cell

structure State where
  heap : HeapLeases.State
  cells : Cells

/-- Stored field references, not a producer-supplied list of capabilities. -/
def Represents (cells : Cells) : Tree → Prop
  | .empty => True
  | .node x l r => cells x = some ⟨root l, root r⟩ ∧ Represents cells l ∧ Represents cells r

/-- A stored root cannot be assigned two different finite tree witnesses.
This prevents the ownership inventory from being chosen independently of the
actual stored child references. Ownership is still a separate requirement. -/
theorem Represents.unique {left right : Tree} (a : Represents cells left)
    (b : Represents cells right) (same : root left = root right) : left = right := by
  induction left generalizing right with
  | empty =>
    cases right with
    | empty => rfl
    | node y l r => cases same
  | node x l r ihl ihr =>
    cases right with
    | empty => cases same
    | node y l' r' =>
      have eq : x = y := Option.some.inj same
      subst y
      have childRoots := Cell.mk.inj (Option.some.inj (a.1.symm.trans b.1))
      have leftEq := ihl a.2.1 b.2.1 childRoots.1
      have rightEq := ihr a.2.2 b.2.2 childRoots.2
      cases leftEq; cases rightEq; rfl

/-- Runtime interpretation includes both field layout and linear authority. -/
structure Interprets (s : State) (reference : Ref) (tree : Tree) : Prop where
  reference_eq : reference = root tree
  fields : Represents s.cells tree
  owned : OwnsTree s.heap tree

/-- Runtime removal of a parent clears its cell as well as its liveness. -/
def release (s : State) (x : Nat) : State :=
  ⟨freedState s.heap x, put s.cells x none⟩

/-- Reads actual stored fields. Ownership/lease safety is supplied by the
interpretation theorem, not checked by this small operational function. -/
def take (s : State) (x : Nat) : Option (Cell × State) :=
  if s.heap.live x then
    match s.cells x with
    | none => none
    | some fields => some (fields, release s x)
  else none

theorem Represents.congr (h : Represents cells tree)
    (same : ∀ x ∈ tree.owners, other x = cells x) : Represents other tree := by
  induction tree with
  | empty => trivial
  | node x l r ihl ihr =>
    obtain ⟨cell, left, right⟩ := h
    refine ⟨(same x (by simp [Tree.owners])).trans cell, ?_, ?_⟩
    · exact ihl left (fun y hy => same y (by simp [Tree.owners, hy]))
    · exact ihr right (fun y hy => same y (by simp [Tree.owners, hy]))

theorem Represents.clear_other (h : Represents cells tree) (absent : x ∉ tree.owners) :
    Represents (put cells x none) tree := by
  apply h.congr
  intro y hy
  have ne : y ≠ x := fun eq => absent (eq ▸ hy)
  simp [put, ne]

/-- Interpreted nonempty data cannot get stuck reading its parent cell. The
returned references are derived from the store/witness relation. -/
theorem take_total (h : Interprets s (some x) (.node x l r)) :
    take s x = some (⟨root l, root r⟩, release s x) := by
  have live := h.owned.live x (by simp [Tree.owners])
  simp [take, live, h.fields.1]

/-- A successful parent split derives safe release and interpreted children
jointly owned with their ambient frame. Neither child ownership nor successful
execution is assumed separately. -/
theorem split_safe (valid : Valid s.heap)
    (fields : Represents s.cells (.node x l r))
    (owned : Owns s.heap ((Tree.node x l r).owners ++ frame)) :
    take s x = some (⟨root l, root r⟩, release s x) ∧
    Step s.heap (.free x) (release s x).heap ∧ Valid (release s x).heap ∧
    Owns (release s x).heap (l.owners ++ r.owners ++ frame) ∧
    Interprets (release s x) (root l) l ∧ Interprets (release s x) (root r) r := by
  have treeOwned := OwnedApplicationFrame.owns_left owned
  have interpretation : Interprets s (some x) (.node x l r) := ⟨rfl, fields, treeOwned⟩
  obtain ⟨step, valid', children⟩ := release_node valid owned
  have absent := root_not_in_fields treeOwned
  have childOwned := OwnedApplicationFrame.owns_left children
  exact ⟨take_total interpretation, step, valid', children,
    ⟨rfl, fields.2.1.clear_other absent.1, OwnedApplicationFrame.owns_left childOwned⟩,
    ⟨rfl, fields.2.2.clear_other absent.2, OwnedApplicationFrame.owns_right childOwned⟩⟩

/-- Every returned value of the executable split agrees with the interpreted
fields; a forged child pointer cannot be accepted as an observation. -/
theorem take_result (h : Interprets s (some x) (.node x l r))
    (observed : take s x = some (cell, t)) :
    cell = ⟨root l, root r⟩ ∧ t = release s x := by
  have eq := Option.some.inj (observed.symm.trans (take_total h))
  exact Prod.mk.inj eq

def allocate (s : State) (left right : Ref) (payload : Nat) : State :=
  ⟨allocatedState s.heap payload, put s.cells s.heap.nextObject (some ⟨left, right⟩)⟩

/-- Constructing a parent installs its actual fields. Freshness protects all
existing field cells and all ambient capabilities, rather than assuming the
post-allocation interpretation. -/
theorem allocate_safe (valid : Valid s.heap)
    (left : Represents s.cells l) (right : Represents s.cells r)
    (owned : Owns s.heap (l.owners ++ r.owners ++ frame)) :
    Valid (allocate s (root l) (root r) payload).heap ∧
    Represents (allocate s (root l) (root r) payload).cells
      (.node s.heap.nextObject l r) ∧
    Owns (allocate s (root l) (root r) payload).heap
      ((Tree.node s.heap.nextObject l r).owners ++ frame) := by
  have unchanged : ∀ y ∈ l.owners ++ r.owners,
      (allocate s (root l) (root r) payload).cells y = s.cells y := by
    intro y member
    have bound := valid.allocated y (owned.live y (List.mem_append_left frame member))
    have ne : y ≠ s.heap.nextObject := by omega
    simp [allocate, put, ne]
  refine ⟨step_valid valid (Step.alloc (value := payload)), ?_, allocate_node valid owned⟩
  refine ⟨by simp [allocate, put], ?_, ?_⟩
  · exact left.congr (fun y hy => unchanged y (List.mem_append_left r.owners hy))
  · exact right.congr (fun y hy => unchanged y (List.mem_append_right l.owners hy))

/-- The old Core consumer receives the left footprint after a store-derived
split. Its heap execution preserves interpretation of the right subtree.
The witness footprint is supplied separately, not decoded into a lexical
environment by take. Cells are an added semantic component: ordinary Core steps here operate only
on the old heap and leave that component unchanged. No source Case is added. -/
theorem consume_left_total (typed : OwnedCoreApplications.Typing g kind ctx n m body)
    (length : l.owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s.heap) (fields : Represents s.cells (.node x l r))
    (owned : Owns s.heap ((Tree.node x l r).owners ++ frame)) :
    ∃ value events t,
      take s x = some (⟨root l, root r⟩, release s x) ∧
      OwnedCoreApplications.Evaluation g kind ctx body l.owners values
        (release s x).heap value events t ∧
      Steps s.heap (.free x :: events) t ∧ Valid t ∧
      Owns t (OwnedCoreApplications.resultOwners kind value ++ (r.owners ++ frame)) ∧
      Interprets ⟨t, (release s x).cells⟩ (root r) r := by
  obtain ⟨split, _, _, _, _, right⟩ := split_safe valid fields owned
  obtain ⟨v, es, t, run, steps, vt, finalOwned⟩ :=
    RecursiveFieldOwnership.consume_left_total typed length scalarLength valid owned
  have retained := OwnedApplicationFrame.owns_left (OwnedApplicationFrame.owns_right finalOwned)
  exact ⟨v, es, t, split, run, steps, vt, finalOwned, ⟨rfl, right.fields, retained⟩⟩

end Jihoo.RecursiveFieldRuntime
