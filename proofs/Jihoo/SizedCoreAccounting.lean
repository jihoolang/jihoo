import Jihoo.SizedCoreSafety

namespace Jihoo.SizedCoreTyping
open ScopedLend SizedBufferContext SizedCoreExecution LinearHeapPrograms



theorem Typing.every_run_accounted (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners)
    (run : Eval g env root s value events t) : Account owners value events := by
  obtain ⟨v, es, u, canonical, _, _, _, account⟩ := typed.total_accounted agree layout valid owned
  obtain ⟨rfl, rfl, rfl⟩ := run.deterministic canonical
  exact account

/-- Executing the typed producer preserves a disjoint ambient owner frame.
Neither result/frame disjointness nor noninterference is an input premise. -/
theorem Typing.framed_safe (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap (owners ++ frame))
    (run : Eval g env root s value events t) :
    SizedBufferHeap.Steps s events t ∧ SizedBufferHeap.Valid t ∧
      Post kind t value ∧ Owns t.heap (resultOwners value ++ frame) := by
  have initial := OwnedApplicationFrame.owns_left owned
  obtain ⟨safe, vt, post⟩ := typed.every_run_safe agree layout valid initial run
  have accounted := typed.every_run_accounted agree layout valid initial run
  have resultOwned : Owns t.heap (resultOwners value) := by
    cases kind <;> cases value <;> simp only [Post] at post
    case scalar.scalar v => exact ⟨by simp [resultOwners], by simp [resultOwners], by simp [resultOwners]⟩
    case owner.owner n x => exact post.1
  exact ⟨safe, vt, post, OwnedApplicationFrame.recombine valid owned
    (SizedBufferHeap.steps_project safe) resultOwned run.lease_frame accounted⟩

/-- Retained captures keep their exact dynamic lengths and uniform payloads,
not only their liveness. -/
theorem Typing.frame_contents (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap (owners ++ frame))
    (run : Eval g env root s value events t) (member : x ∈ frame) :
    t.length x = s.length x ∧ t.heap.payload x = s.heap.payload x := by
  have safe := (typed.framed_safe agree layout valid owned run).1
  have old := valid.allocated x ((OwnedApplicationFrame.owns_right owned).live x member)
  exact ⟨(SizedBufferHeap.lengths_preserved old safe).2, SizedBufferHeap.payloads_preserved old safe⟩

/-- Every consumed initial or newly allocated identity is actually released
exactly once; equal fill values cannot identify two distinct allocations. -/
theorem Typing.other_released (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners)
    (run : Eval g env root s value events t)
    (tracked : x ∈ owners ∨ x ∈ allocations (events.map SizedBufferHeap.Event.project))
    (notReturned : x ∉ resultOwners value) :
    (HeapLeases.released (events.map SizedBufferHeap.Event.project)).count x = 1 ∧ t.heap.live x = false := by
  have safe := typed.lifecycle_projection agree layout valid owned run
  have eq := typed.every_run_accounted agree layout valid owned run x
  have absent := List.count_eq_zero.mpr notReturned
  rw [absent, Nat.add_zero] at eq
  have positive : 0 < (HeapLeases.released (events.map SizedBufferHeap.Event.project)).count x := by
    rcases tracked with initial | allocated
    · have := List.count_pos_iff.mpr initial; omega
    · have := List.count_pos_iff.mpr allocated; omega
  have member := List.count_pos_iff.mp positive
  have count := (releases_distinct valid safe).count (a := x)
  exact ⟨by simpa [member] using count,
    HeapLeases.released_dead valid safe (HeapLeases.released_mem.mp member)⟩

theorem Post.result_live (post : Post kind s value) (member : x ∈ resultOwners value) :
    s.heap.live x = true := by
  cases kind <;> cases value <;> simp [Post, resultOwners] at post member
  case owner.owner n y =>
    subst x
    exact post.1.live y (by simp)

/-- With initial heap coverage, the live final heap consists exactly of the
returned capability. Ambient untracked objects are not silently included. -/
theorem Typing.heap_accounted (typed : Typing g ctx sizes root kind)
    (agree : Agrees ctx owners env) (layout : Layout s owners sizes)
    (valid : SizedBufferHeap.Valid s) (owned : Owns s.heap owners)
    (run : Eval g env root s value events t)
    (coverage : ∀ x, s.heap.live x = true → x ∈ owners) :
    ∀ x, t.heap.live x = true ↔ x ∈ resultOwners value := by
  intro x
  constructor
  · intro live
    by_cases returned : x ∈ resultOwners value
    · exact returned
    have safe := typed.lifecycle_projection agree layout valid owned run
    have origin := live_origin safe live
    have tracked : x ∈ owners ∨ x ∈ allocations (events.map SizedBufferHeap.Event.project) := by
      rcases origin with initial | allocated
      · exact Or.inl (coverage x initial)
      · exact Or.inr allocated
    have dead := (typed.other_released agree layout valid owned run tracked returned).2
    rw [live] at dead
    contradiction
  · exact (typed.every_run_safe agree layout valid owned run).2.2.result_live

/-- Starting empty, every completed scalar execution leaves no live buffers. -/
theorem Typing.closed_scalar_empty (typed : Typing g ctx [] root .scalar)
    (agree : Agrees ctx [] env)
    (run : Eval g env root SizedBufferHeap.empty value events t) :
    ∀ x, t.heap.live x = false := by
  have layout : Layout SizedBufferHeap.empty [] [] := ⟨rfl, by simp⟩
  have owned : Owns SizedBufferHeap.empty.heap [] := ⟨by simp, by simp, by simp⟩
  have post := (typed.every_run_safe agree layout SizedBufferHeap.empty_valid owned run).2.2
  have accounted := typed.heap_accounted agree layout SizedBufferHeap.empty_valid owned run
    (by simp [SizedBufferHeap.empty, HeapLeases.empty])
  cases value <;> simp [Post] at post
  case scalar v =>
    intro x
    have absent : ¬ t.heap.live x = true := by simpa [resultOwners] using (accounted x).mp
    cases h : t.heap.live x <;> simp_all

end Jihoo.SizedCoreTyping
