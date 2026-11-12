import Jihoo.CommonDataConservation

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

/-- A single judgment constructs safe execution and exact allocation-ID
conservation, using the same returned-tree witness as runtime ownership. -/
theorem Typing.total_accounted (typed : Typing g ctx count sizes term kind)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes)
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) :
    ∃ v es t, Eval g env term s v es t ∧ Steps s.buffers.heap es t.buffers.heap ∧
      Valid t.buffers.heap ∧ AccountedPost kind t v frame (footprint (caps trees owners)) es := by
  induction typed generalizing trees owners env s frame with
  | core shape old =>
    have nil := List.eq_nil_of_length_eq_zero length
    subst trees
    obtain ⟨n, es, t, run, steps, vt, kept, _, _⟩ :=
      scalar_total old agreement layout valid owned fields
    refine ⟨.scalar n, _, ⟨t,s.cells⟩, .core shape run, steps, vt, ⟨n,rfl⟩, kept, ?_⟩
    have counted := old.every_run_accounted (by simpa [caps] using project_agrees agreement)
      layout valid (by simpa [caps,footprint_buffers] using OwnedApplicationFrame.owns_left owned) run
    simpa [SizedCoreTyping.Account,SizedCoreTyping.resultOwners,Account,caps,footprint_buffers] using counted
  | literal shape bound =>
    have noTrees := List.eq_nil_of_length_eq_zero length
    have noOwners : owners = [] := List.eq_nil_of_length_eq_zero layout.length
    subst trees; subst owners
    exact ⟨_, [], s, .literal shape, .nil, valid, ⟨_,rfl⟩, owned, Account.refl⟩
  | empty shape =>
    have noTrees := List.eq_nil_of_length_eq_zero length
    have noOwners : owners = [] := List.eq_nil_of_length_eq_zero layout.length
    subst trees; subst owners
    exact ⟨.data none, [], s, .empty shape, .nil, valid, Tree.empty, rfl, trivial, owned, Account.refl⟩
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
        fields (.data tree) (by simp [caps]), by simpa [caps, footprint, Capability.owners] using owned,
        by simpa [caps,footprint,Capability.owners] using (Account.refl (input := tree.owners))⟩
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
        refine ⟨.data (some s.buffers.heap.nextObject), _, CommonData.allocate s (root left) (root right),
          .construct shape leftVar (data_lookup agreement leftSlot rfl)
            rightVar (data_lookup agreement rightSlot rfl), .cons .alloc .nil,
          fresh.1, .node s.buffers.heap.nextObject left right, rfl, fresh.2.1, fresh.2.2, ?_⟩
        intro x
        simp [released,allocations,caps,footprint,Capability.owners,Tree.owners,List.count_append,List.count_cons]
  | bufferLet shape lam scalarTy arg body ih =>
    have argTyped := arg
    rw [← length] at argTyped
    obtain ⟨n, before, middle, first, steps, vm, kept, fs, lexical⟩ :=
      scalar_total argTyped agreement layout valid owned fields
    obtain ⟨v, after, t, second, tail, vt, post⟩ :=
      ih (owners := []) (s := ⟨middle,s.cells⟩) length
        (by simpa [caps, length] using lexical) empty_layout vm
        (by simpa [caps] using kept) (by simpa [caps] using fs)
    have bufferOwned : Owns s.buffers.heap owners := by
      apply OwnedApplicationFrame.owns_right (xs := footprint (trees.map Capability.data))
      simpa [caps,RecursiveCaseBody.footprint_append,footprint_buffers] using
        OwnedApplicationFrame.owns_left owned
    have firstAccount := argTyped.every_run_accounted (by simpa using project_agrees agreement)
      layout valid bufferOwned first
    have scalarAccount : Account owners [] (before.map SizedBufferHeap.Event.project) := firstAccount
    have last : AccountedPost _ _ _ _ ([] ++ footprint (caps trees [])) after := post
    have combined := AccountedPost.compose scalarAccount last
    refine ⟨v, _, t, .bufferLet shape lam scalarTy first second,steps_append steps tail,vt,?_⟩
    apply combined.permute
    simp only [caps,RecursiveCaseBody.footprint_append,footprint_buffers,List.append_nil]
    exact List.perm_append_comm
  | @allocate _ _ _ _ _ _ count ctx n _ _ _ _ shape lam ty annotation alloc len init body ih =>
    have projected := project_agrees agreement
    simp only [List.length_map] at projected
    rw [length] at projected
    obtain ⟨fill,initial⟩ := init.total projected
    have lengthRun := len.transport (fun _ _ h => projected.nats_transport h)
    have step : SizedBufferHeap.Step s.buffers (.alloc s.buffers.heap.nextObject n fill)
        (SizedBufferHeap.allocate s.buffers n fill) := .alloc
    have bufferOwned : Owns s.buffers.heap owners := by
      apply OwnedApplicationFrame.owns_right (xs := footprint (trees.map Capability.data))
      simpa [caps,RecursiveCaseBody.footprint_append,footprint_buffers] using
        OwnedApplicationFrame.owns_left owned
    have freshOwned := SizedBufferHeap.allocate_owns (n := n) (v := fill) valid owned
    have kept : Owns (SizedBufferHeap.allocate s.buffers n fill).heap
        (footprint (caps trees (s.buffers.heap.nextObject :: owners)) ++ frame) := by
      apply owns_permute freshOwned
      simp only [caps,RecursiveCaseBody.footprint_append,footprint_buffers]
      simpa [List.append_assoc] using
        (List.perm_append_comm (l₁ := [s.buffers.heap.nextObject])
          (l₂ := footprint (trees.map Capability.data))).append_right (owners ++ frame)
    have fs : Fields s.cells (caps trees (s.buffers.heap.nextObject :: owners)) := by
      intro c member
      cases c with
      | buffer _ => trivial
      | data tree =>
        apply fields (.data tree)
        simpa [caps] using member
    obtain ⟨v,es,t,run,steps,vt,post⟩ := ih (owners := s.buffers.heap.nextObject :: owners)
      (s := ⟨SizedBufferHeap.allocate s.buffers n fill,s.cells⟩) length
      (by simpa [length] using agrees_freshBuffer agreement)
      (layout.allocate valid bufferOwned) (SizedBufferHeap.step_valid valid step) kept fs
    have first : Account [] [s.buffers.heap.nextObject] [.alloc s.buffers.heap.nextObject fill] := by
      intro x; simp [released, allocations]
    have arranged := post.permute (show (footprint (caps trees (s.buffers.heap.nextObject :: owners))).Perm
        ([s.buffers.heap.nextObject] ++ footprint (caps trees owners)) from by
      simp only [caps,RecursiveCaseBody.footprint_append,footprint_buffers]
      simp)
    refine ⟨v,_,t,.allocate shape lam ty
      (.allocate (by simp [core_at,alloc,projectNode]) lengthRun initial) run,
      .cons (SizedBufferHeap.step_project step) steps,vt,?_⟩
    simpa [SizedBufferHeap.Event.project] using AccountedPost.compose first arranged
  | freeBuffer shape owner selected bound body ih =>
    obtain ⟨x,rest,selection⟩ := select_total (xs := owners) (by rw [layout.length]; exact bound)
    obtain ⟨value,lookup,y,cap,rfl⟩ := agreement.lookup selected
    obtain ⟨_,slotLookup⟩ := caps_buffer cap
    have eq : x = y := Option.some.inj ((LinearCoreCallers.Select.lookup_selected selection).symm.trans
      (by simpa [length] using slotLookup))
    subst y
    have framed := select_frame selection (footprint (trees.map Capability.data)) frame
    have arranged : Owns s.buffers.heap (footprint (trees.map Capability.data) ++ (owners ++ frame)) := by
      simpa [caps,RecursiveCaseBody.footprint_append,footprint_buffers,List.append_assoc] using owned
    have step : SizedBufferHeap.Step s.buffers (.free x) (SizedBufferHeap.release s.buffers x) :=
      .free (arranged.live x framed.member) (arranged.leaseFree x framed.member)
    have kept := SizedBufferHeap.release_owns arranged framed
    have fs : Fields s.cells (caps trees rest) := by
      intro c member
      cases c with
      | buffer _ => trivial
      | data tree => apply fields (.data tree); simpa [caps] using member
    obtain ⟨v,es,t,run,steps,vt,post⟩ := ih (owners := rest)
      (s := ⟨SizedBufferHeap.release s.buffers x,s.cells⟩) length
      (by simpa [length] using agrees_consumeBuffer agreement selection)
      (layout.consumed selection) (SizedBufferHeap.step_valid valid step)
      (by simpa [caps,RecursiveCaseBody.footprint_append,footprint_buffers,List.append_assoc] using kept) fs
    have account {output : List Nat} (h : Account (footprint (caps trees rest)) output es) :
        Account (footprint (caps trees owners)) output (.free x :: es) := by
      intro z; have eq := h z; have count := selection.count z
      simp only [caps,RecursiveCaseBody.footprint_append,footprint_buffers,
        List.count_append,released,allocations,List.filterMap_cons,List.count_cons] at eq ⊢
      split <;> simp_all <;> omega
    refine ⟨v,_,t,.freeBuffer shape owner lookup run,.cons (SizedBufferHeap.step_project step) steps,vt,?_⟩
    exact post.map_account (fun h => account h)
  | dataLet shape lam domain arg body argIH bodyIH =>
    obtain ⟨value, before, middle, first, steps, vm, post⟩ :=
      argIH length agreement layout valid owned fields
    obtain ⟨tree, rfl, rep, kept, firstAccount⟩ := post
    have fs : Fields middle.cells (caps [tree] []) := by
      intro c member
      simp [caps] at member
      subst c
      exact rep
    obtain ⟨v, after, t, second, tail, vt, result⟩ :=
      bodyIH (trees := [tree]) (owners := []) rfl
        (by simpa [caps] using agrees_dataContinuation (tree := tree) agreement)
        empty_layout vm (by simpa [caps, footprint, Capability.owners] using kept) fs
    refine ⟨v, _, t, .dataLet shape lam domain first second,
      steps_append steps tail, vt, ?_⟩
    simpa [caps,footprint,Capability.owners] using
      (AccountedPost.compose (retained := []) firstAccount (by simpa [caps,footprint,Capability.owners] using result))
  | @dataLetSplit activeCount retainedCount count usedSizes savedSizes sizes term fn arg ty body ctx kind countSplit sizeSplit shape lam domain argTyped bodyTyped argIH bodyIH =>
    subst count; subst sizes
    let active := trees.take activeCount
    let retained := trees.drop activeCount
    let used := owners.take usedSizes.length
    let saved := owners.drop usedSizes.length
    have ts : trees = active ++ retained := (List.take_append_drop _ _).symm
    have os : owners = used ++ saved := (List.take_append_drop _ _).symm
    have alen : active.length = activeCount := by simp [active, length]
    have rlen : retained.length = retainedCount := by simp [retained, length]
    have ulen : used.length = usedSizes.length := by simp [used, layout.length]
    have argLayout : SizedBufferContext.Layout s.buffers used usedSizes := by
      simpa [used] using layout.take (p := usedSizes.length)
    have savedLayout : SizedBufferContext.Layout s.buffers saved savedSizes := by
      simpa [saved] using layout.drop (p := usedSizes.length)
    have lexical := agreement
    rw [ts,os] at lexical
    have argLexical := agrees_argument lexical
    rw [alen,rlen,ulen] at argLexical
    have partitioned : Owns s.buffers.heap
        (footprint (caps active used) ++ (footprint (caps retained saved) ++ frame)) := by
      apply owns_permute owned
      rw [ts,os]
      simp only [caps, List.map_append, RecursiveCaseBody.footprint_append, footprint_buffers]
      have perm := (List.perm_append_comm (l₁ := footprint (retained.map Capability.data))
        (l₂ := used)).append_left (footprint (active.map Capability.data))
      simpa [List.append_assoc] using perm.append_right (saved ++ frame)
    have argFields : Fields s.cells (caps active used) := by
      intro c hc
      apply fields c
      rw [ts,os]
      simp only [caps, List.map_append, List.mem_append] at hc ⊢
      rcases hc with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
    have savedFields : Fields s.cells (caps retained saved) := by
      intro c hc
      apply fields c
      rw [ts,os]
      simp only [caps, List.map_append, List.mem_append] at hc ⊢
      rcases hc with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
    obtain ⟨value,before,middle,first,steps,vm,post⟩ :=
      argIH alen argLexical argLayout valid partitioned argFields
    obtain ⟨result,rfl,rep,kept,firstAccount⟩ := post
    have savedBefore := OwnedApplicationFrame.owns_left (OwnedApplicationFrame.owns_right partitioned)
    have savedAfter := OwnedApplicationFrame.owns_left (OwnedApplicationFrame.owns_right kept)
    have fs := first.frame_fields valid steps savedBefore savedAfter savedFields
    have savedBuffers : Owns s.buffers.heap saved := by
      apply OwnedApplicationFrame.owns_right
      simpa [caps, RecursiveCaseBody.footprint_append, footprint_buffers] using savedBefore
    have bodyLayout := first.frame_layout valid steps savedBuffers savedLayout
    have bodyLexical := agrees_captured (result := result) lexical
    rw [alen,rlen,ulen] at bodyLexical
    have bodyFields : Fields middle.cells (caps (result :: retained) saved) := by
      intro c hc
      change c ∈ Capability.data result :: caps retained saved at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact rep
      · exact fs c hc
    obtain ⟨v,after,t,second,tail,vt,final⟩ :=
      bodyIH (trees := result :: retained) (owners := saved)
        (by simp [rlen]) bodyLexical bodyLayout vm
        (by simpa [caps, footprint, Capability.owners, List.append_assoc] using kept) bodyFields
    have combined := AccountedPost.compose firstAccount
      (show AccountedPost _ _ _ _ (result.owners ++ footprint (caps retained saved)) after from
        by simpa [caps,footprint,Capability.owners,List.append_assoc] using final)
    refine ⟨v,_,t,.dataLet shape lam domain first second,steps_append steps tail,vt,?_⟩
    apply combined.permute
    rw [ts,os]
    simp only [caps,List.map_append,RecursiveCaseBody.footprint_append,footprint_buffers]
    have perm := (List.perm_append_comm (l₁ := used) (l₂ := footprint (retained.map Capability.data))).append_left (footprint (active.map Capability.data))
    simpa [List.append_assoc] using perm.append_right saved
  | drop shape owner selected body ih =>
    cases trees with
    | nil => simp at length
    | cons tree rest =>
      have restLength : rest.length = _ := Nat.succ.inj length
      have lookup := data_lookup agreement selected (tree := tree) rfl
      have rep : Represents s.cells tree := fields (.data tree) (by simp [caps])
      have arranged : Owns s.buffers.heap
          (tree.owners ++ (footprint (caps rest owners) ++ frame)) := by
        simpa [caps, footprint, Capability.owners, List.append_assoc] using owned
      obtain ⟨middle, destroyed, steps, vm, kept⟩ := destroy_total rep valid arranged
      have fs : Fields middle.cells (caps rest owners) := by
        intro c member
        have original := fields c (List.mem_cons_of_mem _ member)
        cases c with
        | buffer x => trivial
        | data subtree =>
          apply original.congr
          intro x hx
          apply destroyed.cells_frame
          have tailMember : x ∈ footprint (caps rest owners) := by
            exact footprint_member member hx
          have absent : x ∉ tree.owners := by
            intro headMember
            exact (List.pairwise_append.mp arranged.distinct).2.2 x headMember x
              (List.mem_append_left frame tailMember) rfl
          simpa [released] using absent
      have lengths : SizedBufferContext.Layout middle.buffers owners _ :=
        ⟨layout.length, fun k x n hx hn => by rw [destroyed.lengths]; exact layout.lookup k x n hx hn⟩
      obtain ⟨v, after, t, run, tail, vt, post⟩ :=
        ih restLength (agrees_remove agreement) lengths vm kept fs
      have firstAccount : Account tree.owners [] (tree.owners.map Event.free) := Account.free
      have combined := AccountedPost.compose firstAccount post
      exact ⟨v, _, t, .drop shape owner lookup destroyed run,steps_append steps tail,vt,
        by simpa [caps,footprint,Capability.owners,List.append_assoc] using combined⟩
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
        exact ⟨v, es, t, .emptyCase shape scrutinee lookup run, steps, vt, by simpa [caps,footprint,Capability.owners,Tree.owners] using post⟩
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
          .nodeCase shape scrutinee entered run, steps_append steps (.cons last .nil), vu,
          by simpa [caps,footprint,Capability.owners,Tree.owners,List.append_assoc] using finalPost⟩

/-- Compatibility projection of the stronger allocation-accounted theorem. -/
theorem Typing.total (typed : Typing g ctx count sizes term kind)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) :
    ∃ v es t, Eval g env term s v es t ∧ Steps s.buffers.heap es t.buffers.heap ∧
      Valid t.buffers.heap ∧ Post kind t v frame := by
  obtain ⟨v,es,t,run,steps,vt,post⟩ := typed.total_accounted length agreement layout valid owned fields
  exact ⟨v,es,t,run,steps,vt,post.toPost⟩

end Jihoo.CommonData
