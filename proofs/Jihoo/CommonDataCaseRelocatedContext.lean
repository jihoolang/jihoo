import Jihoo.CommonCompositionContract

/-! Concrete inhabitants of the frozen copied-entry contract. All placement,
reservation, ownership and stack assumptions are explicit in CaseInput and
EntryProvider; arbitrary branch bodies are not executed by this theorem. -/
namespace Jihoo.CommonDataCaseRelocatedContext
open CommonCompositionContract CommonDataTargetContext CommonDataCaseCfg
open CommonDataReference RecursiveLexicalFields RecursiveFieldRuntime RecursiveFieldOwnership
open CommonDataCaseEntryContext

attribute [local irreducible] nodeLocals nilLocals

private theorem selected_local (i : CaseInput) (h : i.before.Valid)
    (shape : i.before.images = image :: rest) :
    i.before.env[i.index]? = some (.data (root image.source)) ∧
    i.before.target.frame.locals[i.src]? = some (some (.pointer image.target 0)) ∧
    Related i.before.source i.before.target.frame.heap image := by
  obtain ⟨a, sl, hi, hs, value, operand, related⟩ := h.toContext.data_lookup i.selected
  have eq : a = image := by simpa [inventory, shape] using hi.symm
  subst a
  have eq : sl = i.src := by simpa [i.slot] using hs.symm
  subst sl
  obtain ⟨_, _, hv⟩ := h.bindings.lookup i.selected
  refine ⟨value, ?_, related⟩
  simp_all [Binding, inventory, Local, ReferenceCfg.operand, TreeDropCall.arg]

theorem node (i : CaseInput) x j l r rest limit
    (h : i.before.Valid) (shape : i.before.images = .node x j l r :: rest)
    (reserved : Reserved i.before.ctx i.before.slots [0,1,2,3,4,5])
    (bound : i.before.target.stack.length ≤ limit) :
    sourceEnter i.before.source i.before.env i.index i.ghostSlots.length =
      some ((i.nodeOut x j l r rest).env, some x) ∧
    Transfer i.program limit 11 i.before (i.nodeOut x j l r rest) [] := by
  obtain ⟨value, connected, related⟩ := selected_local i h shape
  obtain ⟨entered, run, _, _⟩ := CommonDataCaseRelocation.node_entry
    i.pre i.post i.nilBody i.nodeBody i.src related value connected i.space bound
    (Nat.le_refl 11) (ghosts := i.ghostSlots.length)
  refine ⟨entered, ?_, ?_, rfl, rfl, rfl⟩
  · change CommonDataCaseRelocation.walk _ _ _ _ = _
    conv => lhs; rw [i.pc]
    simpa [CommonDataCaseRelocation.runPrefix, CaseInput.program, CaseInput.nodeOut] using run
  · intro valid
    have bindings := Bindings.reframe valid.bindings
      (g := (i.nodeOut x j l r rest).target.frame) (by
        intro k e sl he hs ha
        change (nodeLocals (i.before.target.frame.locals.set! 0 (some (.pointer j 0)))
          j l.target r.target)[sl]? = i.before.target.frame.locals[sl]?
        exact CommonDataCaseRelocation.copied_node_live
          (live := [sl]) (fun z hz => by
            have eq : z = sl := by simpa using hz
            subst z
            exact reserved k e sl he hs ha) (by simp))
    have moved := Context.reframe valid.toContext
      (g := (i.nodeOut x j l r rest).target.frame) rfl bindings
    rw [shape] at moved
    have space : 7 ≤ (i.before.target.frame.locals.set! 0 (some (.pointer j 0))).size := by
      simpa using i.space
    obtain ⟨ll, rl⟩ := node_locals (j := j) (l := l.target) (r := r.target) space
    obtain ⟨_, _, opened⟩ := moved.open_case i.selected ll rl i.ghostSlots
    exact ⟨opened, valid.bufferSizes⟩

theorem nil (i : CaseInput) j rest limit
    (h : i.before.Valid) (shape : i.before.images = .nil j :: rest)
    (reserved : Reserved (CommonData.removeHead i.before.ctx) i.before.slots [0,1,6])
    (bound : i.before.target.stack.length ≤ limit) :
    sourceEnter i.before.source i.before.env i.index i.ghostSlots.length =
      some (i.before.env, none) ∧
    Transfer i.program limit 5 i.before (i.nilOut j rest) [.free j] := by
  obtain ⟨value, connected, related⟩ := selected_local i h shape
  obtain ⟨entered, run⟩ := CommonDataCaseRelocation.nil_entry
    i.pre i.post i.nilBody i.nodeBody i.src related value connected i.space bound
    (Nat.le_refl 5) (ghosts := i.ghostSlots.length)
  refine ⟨entered, ?_, ?_, rfl, rfl, rfl⟩
  · conv => lhs; rw [i.pc]
    simpa [CommonDataCaseRelocation.runPrefix, CaseInput.program, CaseInput.nilOut] using run
  · intro valid
    have fresh : Fresh (CommonData.removeHead i.before.ctx) i.before.slots 6 := by
      intro k e sl he hs ha eq
      have outside := reserved k e sl he hs ha
      simp [eq] at outside
    have frees : Frees i.before.target.frame.heap (Image.nil j).ids
        (retired i.before.target.frame.heap j ReferenceHeap.nilObject) :=
      .cons (empty_case_total related.layout).2.1 .nil
    have hv := valid
    change CommonContext _ _ _ _ _ _ _ _ _ _ _ at hv
    rw [shape] at hv
    have after := hv.after_drop (s := i.before.target) (dest := 6)
      (continuation := i.pre.size+3) CommonData.Destroy.empty frees fresh
    have bindings := Bindings.reframe after.bindings
      (g := (i.nilOut j rest).target.frame) (by
        intro k e sl he hs ha
        have apart := reserved k e sl he hs ha
        have ne : sl ≠ 6 := by simp_all
        exact (CommonDataCaseRelocation.copied_nil_live
          (live := [sl]) (fun z hz => by
            have eq : z = sl := by simpa using hz
            subst z
            exact apart) (by simp)).trans
          (TreeDropCall.resume_local (s := i.before.target) ne).symm)
    exact ⟨Context.reframe after.toContext rfl bindings, valid.bufferSizes⟩

/-- Both fields of the unchanged shared interface, with no extra premises. -/
theorem entryProvider : EntryProvider := ⟨node, nil⟩

end Jihoo.CommonDataCaseRelocatedContext
