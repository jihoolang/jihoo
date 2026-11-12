import Jihoo.CommonDataFrame
import Jihoo.SizedCoreAccounting

/-! Allocation-identity conservation for the common binary Data fragment.
Empty logical capabilities have no allocation footprint. -/
namespace Jihoo.CommonData
open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime
open RecursiveLexicalFields

/-- Ambient frame identities are excluded on both sides of this equation. -/
def Account (input output : List Nat) (events : List Event) : Prop :=
  ∀ x, (released events).count x + output.count x = input.count x + (allocations events).count x

/-- The same actual tree witness supplies representation, ownership and the
returned allocation footprint. A root alone is not a recursive footprint. -/
def AccountedPost (kind : Result) (s : State) (v : Value) (frame input : List Nat)
    (events : List Event) : Prop :=
  match kind with
  | .scalar => (∃ n, v = .scalar n) ∧ Owns s.buffers.heap frame ∧ Account input [] events
  | .data => ∃ tree, v = .data (root tree) ∧ Represents s.cells tree ∧
      Owns s.buffers.heap (tree.owners ++ frame) ∧ Account input tree.owners events

theorem AccountedPost.map_account (post : AccountedPost kind s v frame input events)
    (change : ∀ {output}, Account input output events → Account input' output events') :
    AccountedPost kind s v frame input' events' := by
  cases kind with
  | scalar => exact ⟨post.1,post.2.1,change post.2.2⟩
  | data => obtain ⟨tree,eq,rep,owned,account⟩ := post
            exact ⟨tree,eq,rep,owned,change account⟩

theorem AccountedPost.toPost (h : AccountedPost kind s v frame input events) : Post kind s v frame := by
  cases kind with
  | scalar => exact ⟨h.1,h.2.1⟩
  | data => obtain ⟨tree,value,fields,owned,_⟩ := h; exact ⟨tree,value,fields,owned⟩

theorem Account.refl : Account input input [] := by intro x; simp [released,allocations]

theorem Account.free : Account input [] (input.map Event.free) := by
  intro x
  induction input with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons,released,allocations,List.filterMap_cons,List.count_cons,List.count_nil] at ih ⊢
    omega

theorem Account.compose (first : Account input middle before)
    (last : Account (middle ++ retained) output after) :
    Account (input ++ retained) output (before ++ after) := by
  intro x
  have a := first x; have b := last x
  simp only [released, allocations, List.filterMap_append, List.count_append] at a b ⊢
  omega

theorem AccountedPost.compose (first : Account input middle before)
    (last : AccountedPost kind t v frame (middle ++ retained) after) :
    AccountedPost kind t v frame (input ++ retained) (before ++ after) := by
  cases kind with
  | scalar => exact ⟨last.1,last.2.1,first.compose last.2.2⟩
  | data => obtain ⟨tree,value,fields,owned,account⟩ := last
            exact ⟨tree,value,fields,owned,first.compose account⟩

theorem AccountedPost.permute (post : AccountedPost kind s v frame input events)
    (perm : input.Perm other) : AccountedPost kind s v frame other events := by
  have change {output : List Nat} (h : Account input output events) : Account other output events := by
    intro x; rw [← perm.count_eq x]; exact h x
  cases kind with
  | scalar => exact ⟨post.1,post.2.1,change post.2.2⟩
  | data => obtain ⟨tree,value,fields,owned,account⟩ := post
            exact ⟨tree,value,fields,owned,change account⟩

/-- A pending Case shell is in the branch frame, not its input accounting.
The final release accounts for the one parent absent from the branch input. -/
theorem AccountedPost.finish (post : AccountedPost kind s v (parent :: frame) input events)
    (valid : Valid s.buffers.heap) :
    Step s.buffers.heap (.free parent) (finish s parent).buffers.heap ∧
      Valid (finish s parent).buffers.heap ∧
      AccountedPost kind (finish s parent) v frame (parent :: input) (events ++ [.free parent]) := by
  have account {output : List Nat} (h : Account input output events) : Account (parent :: input) output (events ++ [.free parent]) := by
    intro x; have eq := h x
    simp only [released,allocations,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      List.count_append,List.count_cons,List.count_nil] at eq ⊢
    omega
  cases kind with
  | scalar =>
    obtain ⟨step,vt,final⟩ := post.toPost.finish valid
    exact ⟨step,vt,final.1,final.2,account post.2.2⟩
  | data =>
    obtain ⟨tree,value,fields,owned,conserved⟩ := post
    have pending := restore_pending owned
    have step := Step.free (pending.live parent (by simp)) (pending.leaseFree parent (by simp))
    have absent : parent ∉ tree.owners := by
      intro member
      exact (List.nodup_cons.mp pending.distinct).1 (List.mem_append_left frame member)
    exact ⟨step,step_valid valid step,tree,value,fields.clear_other absent,
      OwnedCoreContinuation.free_owns pending Select.here,account conserved⟩

/-- The complete returned allocation footprint is interpreted from the final
stored tree, not guessed from a root identity or a producer resource list. -/
def ResultFootprint (cells : Cells) (v : Value) (output : List Nat) : Prop :=
  match v with
  | .scalar _ => output = []
  | .data reference => ∃ tree, reference = root tree ∧ Represents cells tree ∧ output = tree.owners
  | _ => False

theorem ResultFootprint.unique (a : ResultFootprint cells v xs) (b : ResultFootprint cells v ys) : xs = ys := by
  cases v <;> simp only [ResultFootprint] at a b
  case scalar => exact a.trans b.symm
  case data reference =>
    obtain ⟨left,lroot,lrep,rfl⟩ := a
    obtain ⟨right,rroot,rrep,rfl⟩ := b
    exact congrArg Tree.owners (lrep.unique rrep (lroot.symm.trans rroot))
  all_goals contradiction

theorem AccountedPost.output (post : AccountedPost kind s v frame input events) :
    ∃ output, ResultFootprint s.cells v output ∧ Owns s.buffers.heap (output ++ frame) ∧
      Account input output events := by
  cases kind with
  | scalar => obtain ⟨⟨n,rfl⟩,owned,account⟩ := post; exact ⟨[],rfl,owned,account⟩
  | data => obtain ⟨tree,rfl,fields,owned,account⟩ := post
            exact ⟨tree.owners,⟨tree,rfl,fields,rfl⟩,owned,account⟩

/-- Accounting is independent of the finite representation witness chosen by
a caller: actual final field references determine its whole footprint. -/
theorem AccountedPost.account_for {output : List Nat} (post : AccountedPost kind s v frame input events)
    (observed : ResultFootprint s.cells v output) : Account input output events := by
  obtain ⟨actual,represented,_,account⟩ := post.output
  cases represented.unique observed
  exact account

end Jihoo.CommonData
