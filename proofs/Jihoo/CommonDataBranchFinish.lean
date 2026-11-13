import Jihoo.CommonCompositionContract

/-! Conditional branch-body composition and independent pending-shell retirement.
Body evaluation and installed target execution are explicit inputs. -/
namespace Jihoo.CommonDataBranchFinish
open CommonCompositionContract CommonDataTargetContext CommonDataReference
open RecursiveLexicalFields RecursiveFieldRuntime RecursiveFieldOwnership
open HeapLeases LinearHeapPrograms

variable {a b : Boundary} {shell : Pending} {tail : List Pending} {image : Image}

/-- Retire one shell without reading its child pointers or changing any locals. -/
def finished (a : Boundary) (shell : Pending) (tail : List Pending)
    (machine : ReferenceCalls.State) : Boundary :=
  { a with
    pending := tail
    source := CommonData.finish a.source shell.source
    target := machine }

/-- Placement/execution is deliberately explicit: one installed program, exact
walk, exact retired heap, unchanged locals and suspended callers. No provider
inhabitant or body compiler is assumed globally. -/
structure FinishExecution (p : ReferenceCalls.Program) (limit ticks : Nat)
    (a : Boundary) (shell : Pending) (machine : ReferenceCalls.State) : Prop where
  run : CommonDataCaseRelocation.walk p ticks limit a.target =
    some (machine, [.free shell.target])
  heap : machine.frame.heap = retired a.target.frame.heap shell.target shell.object
  locals : machine.frame.locals = a.target.frame.locals
  callers : machine.stack = a.target.stack

private theorem retire_other (ne : k ≠ j) : (retired H j obj)[k]? = H[k]? :=
  ReferenceHeap.Frame.set_other H _ ne

/-- Resource preservation uses shell authority only; stale child pointers are
irrelevant. Buffers retain identities, lengths and payloads; nested shells stay live. -/
theorem finish_context (h : a.Valid) (head : a.pending = shell :: tail)
    (heap : machine.frame.heap = retired a.target.frame.heap shell.target shell.object)
    (locals : machine.frame.locals = a.target.frame.locals) :
    (finished a shell tail machine).Valid := by
  have own : Owns a.source.buffers.heap (shell.source ::
      (footprint (sources (inventory a.images a.buffers)) ++
        (tail.map Pending.source ++ a.sf))) :=
    CommonData.restore_pending (by simpa [head] using h.owned)
  have kept := OwnedCoreContinuation.free_owns own Select.here
  have sa := (List.nodup_cons.mp own.distinct).1
  have sep : (shell.target :: (targets (inventory a.images a.buffers) ++
      (tail.map Pending.target ++ a.tf))).Nodup := by
    have perm := (List.perm_append_comm (l₁ := [shell.target])
      (l₂ := targets (inventory a.images a.buffers))).append_right
      (tail.map Pending.target ++ a.tf)
    apply perm.nodup_iff.mpr
    simpa [List.append_assoc, head] using h.separated
  have ta := (List.nodup_cons.mp sep).1
  have valid : Valid (CommonData.finish a.source shell.source).buffers.heap :=
    step_valid h.valid (.free (own.live _ (by simp)) (own.leaseFree _ (by simp)))
  have bindings : Bindings (inventory a.images a.buffers) machine.frame a.ctx a.slots :=
    CommonDataCaseEntryContext.Bindings.reframe h.bindings (fun _ _ _ _ _ _ => by rw [locals])
  refine ⟨⟨valid, h.agreement, bindings, ?_, kept,
    (List.nodup_cons.mp sep).2, ?_⟩, ?_⟩
  · intro r hr
    have rel := h.resources r hr
    have sourceApart : ∀ x ∈ r.source.owners, x ≠ shell.source := by
      intro x hx eq
      apply sa
      exact List.mem_append_left _ (eq ▸ footprint_member (List.mem_map.mpr ⟨r, hr, rfl⟩) hx)
    have targetApart : ∀ j ∈ r.ids, j ≠ shell.target := by
      intro j hj eq
      apply ta
      exact List.mem_append_left _ (eq ▸ List.mem_flatMap.mpr ⟨r, hr, hj⟩)
    cases r with
    | data i =>
      change Related _ machine.frame.heap i
      rw [heap]
      refine ⟨rel.fields.clear_other ?_, ?_, rel.layout.congr ?_, rel.distinct⟩
      · intro hx; exact sourceApart _ hx rfl
      · exact ⟨rel.owned.distinct,
          fun x hx => kept.live x (List.mem_append_left _
            (footprint_member (List.mem_map.mpr ⟨.data i, hr, rfl⟩) hx)),
          fun x hx => kept.leaseFree x (List.mem_append_left _
            (footprint_member (List.mem_map.mpr ⟨.data i, hr, rfl⟩) hx))⟩
      · intro j hj; exact retire_other (targetApart j hj)
    | buffer x j =>
      change BufferRelated _ machine.frame.heap x j
      rw [heap]
      exact rel.finish (sourceApart x (by simp [Resource.source, Capability.owners]))
        (Ne.symm (targetApart j (by simp [Resource.ids])))
  · intro other ho
    change other ∈ tail at ho
    obtain ⟨live, found, alive⟩ := h.shells other (by simp [head, ho])
    have sn : other.source ≠ shell.source := by
      intro eq; apply sa
      exact List.mem_append_right _ (List.mem_append_left _
        (List.mem_map.mpr ⟨other, ho, eq⟩))
    have tn : other.target ≠ shell.target := by
      intro eq; apply ta
      exact List.mem_append_right _ (List.mem_append_left _
        (List.mem_map.mpr ⟨other, ho, eq⟩))
    refine ⟨?_, ?_, alive⟩
    · simpa [finished, CommonData.finish, RecursiveCaseBody.finish, SizedBufferHeap.release,
        put, sn] using live
    · change machine.frame.heap[other.target]? = some other.object
      rw [heap, retire_other tn]; exact found
  · exact ⟨h.bufferSizes.length, h.bufferSizes.lookup⟩

/-- Source free and target release follow from valid ownership, independently
of the body evaluator and of instruction placement. -/
theorem finish_authority (h : a.Valid) (head : a.pending = shell :: tail)
    (post : CommonData.Post kind a.source v (a.pending.map Pending.source ++ a.sf)) :
    HeapLeases.Step a.source.buffers.heap (.free shell.source)
      (CommonData.finish a.source shell.source).buffers.heap ∧
    CommonData.Post kind (CommonData.finish a.source shell.source) v
      (tail.map Pending.source ++ a.sf) ∧
    ReferenceHeap.release a.target.frame.heap (.object shell.target 0) =
      some (retired a.target.frame.heap shell.target shell.object) := by
  obtain ⟨step, _, final⟩ := CommonData.Post.finish (by simpa [head] using post) h.valid
  obtain ⟨_, found, live⟩ := h.shells shell (by simp [head])
  exact ⟨step, final, ReferenceHeap.Frame.release_success_iff.mpr
    ⟨shell.object, found, live, rfl, rfl⟩⟩

/-- Construct the frozen contract result from smaller, explicit execution inputs. -/
theorem finish_result (h : a.Valid) (head : a.pending = shell :: tail)
    (post : CommonData.Post kind a.source v (a.pending.map Pending.source ++ a.sf))
    (exec : FinishExecution p limit ticks a shell machine) :
    FinishResult p limit ticks a (finished a shell tail machine) shell tail kind v slot := by
  refine ⟨by simp [finished, exec.locals], head, rfl, rfl, rfl, rfl, rfl,
    ⟨rfl,rfl,rfl⟩, ⟨exec.run, ?_, exec.callers, rfl, rfl⟩, ?_⟩
  · intro ha; exact finish_context ha head exec.heap exec.locals
  · exact (finish_authority h head post).2.1

/-- Body Eval, Typing and Transfer remain explicit assumptions. This theorem
composes their actual execution with shell retirement in the same program. -/
theorem body_finish (valid : a.Valid)
    (body : BodyResult g term kind p limit n a b v se te slot)
    (head : b.pending = shell :: tail)
    (exec : FinishExecution p limit m b shell machine) :
    Transfer p limit (n+m) a (finished b shell tail machine) (te ++ [.free shell.target]) ∧
    FinishResult p limit m b (finished b shell tail machine) shell tail kind v slot := by
  have fin := finish_result (body.transfer.context valid) head body.post exec (slot := slot)
  exact ⟨body.transfer.then fin.transfer, fin⟩

/-- The result representation survives retirement, including a live data image. -/
theorem result_preserved
    (body : BodyResult g term kind p limit n a b v se te slot)
    (exec : FinishExecution p limit m b shell machine) :
    match v with
    | .scalar n => Local machine.frame slot (.i64 n)
    | .data ref => ∃ image ∈ (finished b shell tail machine).images,
        root image.source = ref ∧ Local machine.frame slot (.pointer image.target 0)
    | _ => False := by
  have result := body.result
  cases v with
  | scalar n => simpa [Local, exec.locals] using result
  | data ref => simpa [Local, finished, exec.locals] using result
  | _ => exact result

/-- A pending owner cannot alias a retained data owner. -/
theorem pending_not_result (h : a.Valid) (head : a.pending = shell :: tail)
    (member : image ∈ a.images) : shell.source ∉ image.source.owners := by
  have own := CommonData.restore_pending (by simpa [head] using h.owned)
  have absent := (List.nodup_cons.mp own.distinct).1
  intro hx
  apply absent
  apply List.mem_append_left
  exact footprint_member (List.mem_map.mpr ⟨Resource.data image,
    by simp [inventory, member], rfl⟩) hx

end Jihoo.CommonDataBranchFinish
