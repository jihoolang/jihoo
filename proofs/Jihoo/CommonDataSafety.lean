import Jihoo.CommonDataTyping

namespace Jihoo.CommonData
open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime
open RecursiveLexicalFields RecursiveBodyProjection

variable {s : State} {trees : List Tree} {owners : List Nat}

/-- Reuses the full existing sized Core body theorem under arbitrary Data and
pending frames; no post-body ownership or success premise is supplied. -/
theorem scalar_total
    (typed : SizedCoreTyping.Typing (coreGraph g) (context trees.length ctx) sizes term .scalar)
    (agreement : Agrees (caps trees owners) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes)
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) :
    ∃ n es t, SizedCoreExecution.Eval (coreGraph g) (environment env) term s.buffers (.scalar n) es t ∧
      Steps s.buffers.heap (es.map SizedBufferHeap.Event.project) t.heap ∧ Valid t.heap ∧
      Owns t.heap (footprint (trees.map Capability.data) ++ frame) ∧
      Fields s.cells (trees.map Capability.data) ∧
      Agrees (trees.map Capability.data) (continuation trees.length ctx) (.scalar n :: env) := by
  have split : Owns s.buffers.heap (owners ++ (footprint (trees.map Capability.data) ++ frame)) := by
    apply owns_permute owned
    simp only [caps, RecursiveCaseBody.footprint_append, footprint_buffers]
    have perm : ((footprint (trees.map Capability.data) ++ owners) ++ frame).Perm
        ((owners ++ footprint (trees.map Capability.data)) ++ frame) :=
      List.perm_append_comm.append_right frame
    simpa [List.append_assoc] using perm
  have agrees : SizedBufferContext.Agrees (context trees.length ctx) owners (environment env) := by
    simpa using project_agrees agreement
  obtain ⟨result, es, t, run, steps, vt, post, account⟩ :=
    typed.total_accounted agrees layout valid (OwnedApplicationFrame.owns_left split)
  cases result <;> simp only [SizedCoreTyping.Post] at post
  case scalar n =>
    have empty : Owns t.heap [] := ⟨by simp, by simp, by simp⟩
    have kept := OwnedApplicationFrame.recombine valid split
      (SizedBufferHeap.steps_project steps) empty run.lease_frame account
    refine ⟨n, es, t, run, SizedBufferHeap.steps_project steps, vt, kept, ?_, ?_⟩
    · intro c member; exact fields c (List.mem_append_left _ member)
    · simpa using continuation_agrees agreement

theorem empty_layout {bufferState : SizedBufferHeap.State} : SizedBufferContext.Layout bufferState [] [] :=
  ⟨rfl, by intro k x n h; simp at h⟩

/-- A single judgment now constructs safe execution and ownership of the final
scalar/data result. The postcondition contains no residual child inventory;
this theorem does not assert exact trace accounting for all input allocations. -/
theorem Typing.total (typed : Typing g ctx count sizes term kind)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes)
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) :
    ∃ v es t, Eval g env term s v es t ∧ Steps s.buffers.heap es t.buffers.heap ∧
      Valid t.buffers.heap ∧ Post kind t v frame := by
  induction typed generalizing trees owners env s frame with
  | core shape old =>
    have nil := List.eq_nil_of_length_eq_zero length
    subst trees
    obtain ⟨n, es, t, run, steps, vt, kept, _, _⟩ :=
      scalar_total old agreement layout valid owned fields
    exact ⟨.scalar n, _, ⟨t,s.cells⟩, .core shape run, steps, vt, ⟨n,rfl⟩, kept⟩
  | empty shape =>
    have noTrees := List.eq_nil_of_length_eq_zero length
    have noOwners : owners = [] := List.eq_nil_of_length_eq_zero layout.length
    subst trees; subst owners
    exact ⟨.data none, [], s, .empty shape, .nil, valid, Tree.empty, rfl, trivial, owned⟩
  | dataVar shape selected =>
    have noOwners : owners = [] := List.eq_nil_of_length_eq_zero layout.length
    subst owners
    cases trees with
    | nil => simp at length
    | cons tree rest =>
      have noRest : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using length)
      subst rest
      have lookup := data_lookup agreement selected (tree := tree) rfl
      exact ⟨.data (root tree), [], s, .dataVar shape lookup, .nil, valid, tree, rfl,
        fields (.data tree) (by simp [caps]), by simpa [caps, footprint, Capability.owners] using owned⟩
  | construct shape leftVar leftSlot rightVar rightSlot =>
    have noOwners : owners = [] := List.eq_nil_of_length_eq_zero layout.length
    subst owners
    cases trees with
    | nil => simp at length
    | cons left rest =>
      cases rest with
      | nil => simp at length
      | cons right rest =>
        have noRest : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using length)
        subst rest
        have lrep : Represents s.cells left := fields (.data left) (by simp [caps])
        have rrep : Represents s.cells right := fields (.data right) (by simp [caps])
        have arranged : Owns s.buffers.heap (left.owners ++ right.owners ++ frame) := by
          simpa [caps, footprint, Capability.owners, List.append_assoc] using owned
        have fresh := allocate_safe (s := s.recursive) (payload := 0) valid lrep rrep arranged
        exact ⟨.data (some s.buffers.heap.nextObject), _, allocate s (root left) (root right),
          .construct shape leftVar (data_lookup agreement leftSlot rfl)
            rightVar (data_lookup agreement rightSlot rfl), .cons .alloc .nil,
          fresh.1, .node s.buffers.heap.nextObject left right, rfl, fresh.2.1, fresh.2.2⟩
  | bufferLet shape lam scalarTy arg body ih =>
    have argTyped := arg
    rw [← length] at argTyped
    obtain ⟨n, before, middle, first, steps, vm, kept, fs, lexical⟩ :=
      scalar_total argTyped agreement layout valid owned fields
    obtain ⟨v, after, t, second, tail, vt, post⟩ :=
      ih (owners := []) (s := ⟨middle,s.cells⟩) length
        (by simpa [caps, length] using lexical) empty_layout vm
        (by simpa [caps] using kept) (by simpa [caps] using fs)
    exact ⟨v, _, t, .bufferLet shape lam scalarTy first second,
      steps_append steps tail, vt, post⟩
  | caseTree shape scrutinee selected nilBody nodeBody nilIH nodeIH =>
    cases trees with
    | nil => simp at length
    | cons tree rest =>
      have restLength : rest.length = _ := Nat.succ.inj length
      have lookup := data_lookup agreement selected (tree := tree) rfl
      cases tree with
      | empty =>
        have lexical := agrees_remove agreement
        have kept : Owns s.buffers.heap (footprint (caps rest owners) ++ frame) := by
          simpa [caps, footprint, Capability.owners, Tree.owners] using owned
        have fs : Fields s.cells (caps rest owners) := by
          intro c member; exact fields c (List.mem_cons_of_mem _ member)
        obtain ⟨v, es, t, run, steps, vt, post⟩ :=
          nilIH restLength lexical layout valid kept fs
        exact ⟨v, es, t, .emptyCase shape scrutinee lookup run, steps, vt, post⟩
      | node parent left right =>
        have inventory : Inventory s.recursive (.data (.node parent left right) :: caps rest owners) :=
          ⟨OwnedApplicationFrame.owns_left owned, fields⟩
        obtain ⟨opened, entered, lexical, _, fs⟩ := enter_total agreement selected inventory
        have arranged : Owns s.buffers.heap
            (footprint (caps (left :: right :: rest) owners) ++ (parent :: frame)) := by
          apply move_pending
          simpa [caps, footprint, Capability.owners, Tree.owners, List.append_assoc] using owned
        obtain ⟨v, es, t, run, steps, vt, post⟩ :=
          nodeIH (trees := left :: right :: rest) (frame := parent :: frame)
            (by simp only [List.length_cons]; omega) lexical layout valid arranged fs
        obtain ⟨last, vu, finalPost⟩ := post.finish vt
        exact ⟨v, es ++ [.free parent], finish t parent,
          .nodeCase shape scrutinee entered run, steps_append steps (.cons last .nil), vu, finalPost⟩

end Jihoo.CommonData
