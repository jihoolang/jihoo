import Jihoo.OwnedApplicationFrame

/-! A resource interface for finite recursive boxed data. The tree records
allocation identities, not native layouts or source constructors. Its footprint
can feed existing Core ownership judgments. No recursive Core typing, field
payload correspondence, Back rule, or compiler refinement is claimed here. -/
namespace Jihoo.RecursiveFieldOwnership
open HeapLeases LinearHeapPrograms OwnedCoreContinuation

inductive Tree where
  | empty
  | node (object : Nat) (left right : Tree)
  deriving DecidableEq, Repr

def Tree.owners : Tree → List Nat
  | .empty => []
  | .node x l r => x :: (l.owners ++ r.owners)

abbrev OwnsTree (s : State) (tree : Tree) := Owns s tree.owners

/-- Unpacking exposes the exact existing inventory, including its frame. -/
theorem unpack (owned : Owns s ((Tree.node x l r).owners ++ frame)) :
    Owns s (x :: (l.owners ++ r.owners ++ frame)) := by
  simpa [Tree.owners, List.append_assoc] using owned

/-- A node cannot own itself through either recursive field. -/
theorem root_not_in_fields (owned : OwnsTree s (.node x l r)) :
    x ∉ l.owners ∧ x ∉ r.owners := by
  have absent := (List.nodup_cons.mp owned.distinct).1
  simpa [List.mem_append] using absent

/-- Distinct fields cannot contain the same allocation at any depth. -/
theorem fields_separate (owned : OwnsTree s (.node x l r))
    (left : y ∈ l.owners) : y ∉ r.owners := by
  have fields := (List.nodup_cons.mp owned.distinct).2
  intro right
  exact (List.pairwise_append.mp fields).2.2 y left y right rfl

/-- Allocation wraps already-owned fields; freshness follows from Valid. -/
theorem allocate_node (valid : Valid s)
    (owned : Owns s (l.owners ++ r.owners ++ frame)) :
    Owns (allocatedState s payload) ((Tree.node s.nextObject l r).owners ++ frame) := by
  simpa [Tree.owners, List.append_assoc] using allocate_owns (v := payload) valid owned

/-- Consuming a parent frees just its allocation, preserving every recursive
field and ambient owner. The Step is derived, not assumed. -/
theorem release_node (valid : Valid s)
    (owned : Owns s ((Tree.node x l r).owners ++ frame)) :
    Step s (.free x) (freedState s x) ∧ Valid (freedState s x) ∧
      Owns (freedState s x) (l.owners ++ r.owners ++ frame) := by
  have all := unpack owned
  have selected : Select (x :: (l.owners ++ r.owners ++ frame)) 0 x
      (l.owners ++ r.owners ++ frame) := .here
  have step := Step.free (all.live x (by simp)) (all.leaseFree x (by simp))
  exact ⟨step, step_valid valid step, free_owns all selected⟩

/-- Exact identity accounting for destructuring, including duplicate counts in
arbitrary input trees. Safety separately excludes those duplicates. -/
theorem release_accounting (treeLeft treeRight : Tree) (x y : Nat) :
    (if x = y then 1 else 0) + (treeLeft.owners ++ treeRight.owners).count y =
      (Tree.node x treeLeft treeRight).owners.count y := by
  simp [Tree.owners, List.count_cons, Nat.add_comm]

/-- Concrete bridge to existing Core typing: after releasing the parent, a
Core consumer checked against all left-field capabilities retains the right
field and ambient frame. The consumer still uses the existing flat context;
this does not admit a new source data eliminator. -/
theorem consume_left (typed : OwnedCoreApplications.Typing g kind ctx n m root)
    (length : l.owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s ((Tree.node x l r).owners ++ frame))
    (run : OwnedCoreApplications.Evaluation g kind ctx root l.owners values
      (freedState s x) value events t) :
    Steps s (.free x :: events) t ∧ Valid t ∧
      Owns t (OwnedCoreApplications.resultOwners kind value ++ (r.owners ++ frame)) := by
  obtain ⟨step, valid', fields⟩ := release_node valid owned
  have fields' : Owns (freedState s x) (l.owners ++ (r.owners ++ frame)) := by
    simpa [List.append_assoc] using fields
  obtain ⟨steps, finalValid, finalOwned⟩ :=
    OwnedApplicationFrame.framed_safe typed length scalarLength valid' fields' run
  exact ⟨.cons step steps, finalValid, finalOwned⟩

/-- Progress at the Core interface: no successful consumer run is a premise. -/
theorem consume_left_total (typed : OwnedCoreApplications.Typing g kind ctx n m root)
    (length : l.owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s ((Tree.node x l r).owners ++ frame)) :
    ∃ value events t,
      OwnedCoreApplications.Evaluation g kind ctx root l.owners values
        (freedState s x) value events t ∧
      Steps s (.free x :: events) t ∧ Valid t ∧
      Owns t (OwnedCoreApplications.resultOwners kind value ++ (r.owners ++ frame)) := by
  obtain ⟨_, valid', fields⟩ := release_node valid owned
  have fields' : Owns (freedState s x) (l.owners ++ (r.owners ++ frame)) := by
    simpa [List.append_assoc] using fields
  obtain ⟨v, es, t, run⟩ := OwnedCoreApplications.total typed length scalarLength
    valid' (OwnedApplicationFrame.owns_left fields')
  exact ⟨v, es, t, run, consume_left typed length scalarLength valid owned run⟩

end Jihoo.RecursiveFieldOwnership
