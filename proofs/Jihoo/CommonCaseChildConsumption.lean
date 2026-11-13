import Jihoo.CommonCompositionContract

/-! A source-level resolution of the Node/literal ownership gap. Explicit
recursive drops consume the two children before evaluating the literal. This
is not an installed target-CFG BodyResult or a compiler correspondence theorem. -/
namespace Jihoo.CommonCaseChildConsumption
open RecursiveLexicalFields RecursiveFieldOwnership RecursiveFieldRuntime
open CommonData HeapLeases LinearHeapPrograms

/-- Node binders are [right, left, ghosts..., outer...]. Drop left first;
removing it shifts right's capability index from one to zero, not its slot. -/
def graph (n : Nat) : CommonDataSource.Graph := #[
  .core (.var 1), .core (.var 0), .core (.integer n),
  .drop 0 1 2, .drop 0 0 3]

theorem typed (bound : n < 2^63) :
    CommonDataSourceRules.Typing (graph n) (bindContext ghosts ctx) 2 [] 4 .scalar := by
  apply CommonDataSourceRules.Typing.drop (index := 1) rfl rfl
  · rfl
  apply CommonDataSourceRules.Typing.drop (index := 0) rfl rfl
  · rfl
  exact .literal rfl bound

/-- Literal typing cannot be framed over nonempty data inventories. -/
theorem literal_inventory_zero
    (shape : CommonDataSource.nodeAt g term = .core (.integer n))
    (typed : CommonDataSourceRules.Typing g ctx count sizes term kind) :
    count = 0 ∧ sizes = [] ∧ kind = .scalar := by
  cases typed <;> simp_all

/-- In particular no literal BodyResult can start directly at Node entry,
even when both children are logical Nil (whose source footprints are empty). -/
theorem no_node_literal_body (i : CommonCompositionContract.CaseInput)
    (shape : CommonDataSource.nodeAt g term = .core (.integer n)) :
    ¬ CommonCompositionContract.BodyResult g term kind p limit ticks
      (i.nodeOut x j l r rest) b v se te slot := by
  intro body
  have h := (literal_inventory_zero shape body.typing).1
  simp [CommonCompositionContract.CaseInput.nodeOut] at h

/-- Genuine source evaluation is derived from typing and resource invariants;
no execution certificate is assumed. The arbitrary frame can contain the
pending parent shell and all ambient reservations. It remains owned, while
the scalar result retains none of the two child footprints. -/
theorem total (bound : n < 2^63)
    (agreement : Agrees (caps [left, right] []) (bindContext ghosts ctx) env)
    (layout : SizedBufferContext.Layout s.buffers [] [])
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps [left, right] []) ++ frame))
    (fields : Fields s.cells (caps [left, right] [])) :
    ∃ v es t, CommonDataSourceExecution.Eval (graph n) env 4 s v es t ∧
      Steps s.buffers.heap es t.buffers.heap ∧ Valid t.buffers.heap ∧
      AccountedPost .scalar t v frame (footprint (caps [left, right] [])) es :=
  CommonDataSourceExecution.total_accounted (typed bound) rfl agreement layout valid owned fields

/-- Every initially owned child allocation is freed exactly once and is dead.
This applies to any observed run, not only the existence witness above. -/
theorem child_released (bound : n < 2^63)
    (agreement : Agrees (caps [left, right] []) (bindContext ghosts ctx) env)
    (layout : SizedBufferContext.Layout s.buffers [] [])
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps [left, right] []) ++ frame))
    (fields : Fields s.cells (caps [left, right] []))
    (run : CommonDataSourceExecution.Eval (graph n) env 4 s (.scalar value) es t)
    (member : x ∈ footprint (caps [left, right] [])) :
    (released es).count x = 1 ∧ t.buffers.heap.live x = false :=
  (typed bound).elaborate.other_released rfl agreement layout valid owned fields
    run.to_common rfl (.inl member) (by simp)

/-- The parent shell is framed only because it is separate from the child
footprints in the initial Owns premise. It is still live and never freed. -/
theorem frame_survives (bound : n < 2^63)
    (agreement : Agrees (caps [left, right] []) (bindContext ghosts ctx) env)
    (layout : SizedBufferContext.Layout s.buffers [] [])
    (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps [left, right] []) ++ frame))
    (fields : Fields s.cells (caps [left, right] []))
    (run : CommonDataSourceExecution.Eval (graph n) env 4 s (.scalar value) es t)
    (member : x ∈ frame) : t.buffers.heap.live x = true ∧ x ∉ released es :=
  (typed bound).elaborate.survivors rfl agreement layout valid owned fields
    run.to_common (output := []) rfl (by simpa using member)

open CommonDataTargetContext CommonDataReference

/-- Two installed recursive calls discharge the exact Node child inventory.
The second site's checks are uniform in the heap produced by the first call;
they are code/local ABI checks, not assumed execution or ownership results.
Both call prefixes run in the same p. No exact tick-count Transfer is claimed. -/
theorem installed_children
    (h : CommonContext [left, right] [] [] pending sf tf
      (bindContext ghosts ctx) env slots source s.frame)
    (bound : n < 2^63)
    (installed : p[dropId]? = some (TreeDropCall.body dropId))
    (siteLeft : TreeDropCall.Site p s destLeft next)
    (callLeft : ∀ slot, slots[1]? = some slot → ∃ fn, p[s.function]? = some fn ∧
      ReferenceCalls.extension fn.code s.frame = some (.call
        (TreeDropCall.call dropId (TreeDropCall.arg slot) destLeft next)))
    (siteRight : ∀ K, TreeDropCall.Site p
      (TreeDropCall.resume s destLeft next K) destRight continuation)
    (callRight : ∀ K slot, slots[0]? = some slot → ∃ fn,
      p[(TreeDropCall.resume s destLeft next K).function]? = some fn ∧
      ReferenceCalls.extension fn.code (TreeDropCall.resume s destLeft next K).frame =
        some (.call (TreeDropCall.call dropId (TreeDropCall.arg slot) destRight continuation)))
    (freshLeft : Fresh (removeHead (bindContext ghosts ctx)) slots destLeft)
    (freshRight : Fresh (removeHead (removeHead (bindContext ghosts ctx))) slots destRight)
    (depthLeft : s.stack.length + 1 + left.depth ≤ limit)
    (depthRight : s.stack.length + 1 + right.depth ≤ limit) :
    ∃ middle K final L,
      Destroy (root left.source) source (left.source.owners.map Event.free) middle ∧
      Destroy (root right.source) middle (right.source.owners.map Event.free) final ∧
      ReferenceCalls.Steps p (.running s) (left.ids.map HeapLifecycle.Event.free)
        (.running (TreeDropCall.resume s destLeft next K)) ∧
      ReferenceCalls.Steps p (.running (TreeDropCall.resume s destLeft next K))
        (right.ids.map HeapLifecycle.Event.free)
        (.running (TreeDropCall.resume (TreeDropCall.resume s destLeft next K)
          destRight continuation L)) ∧
      CommonContext [] [] [] pending sf tf
        (removeHead (removeHead (bindContext ghosts ctx))) env slots final
        (TreeDropCall.resume (TreeDropCall.resume s destLeft next K)
          destRight continuation L).frame := by
  obtain ⟨bodyTyped, middle, K, destroyedLeft, stepsLeft, afterLeft, _⟩ :=
    typed_drop_prefix (owner := 0) (body := 3) h (typed bound).elaborate
      (by simp [CommonDataSourceRules.adapted_at, graph, CommonDataSource.nodeAt, CommonDataSourceRules.adaptNode, CommonDataSource.adaptNode]) (by simp [CommonDataSourceRules.adapted_at, graph, CommonDataSource.nodeAt, CommonDataSourceRules.adaptNode, CommonDataSource.adaptNode]) installed siteLeft callLeft freshLeft depthLeft
  obtain ⟨_, final, L, destroyedRight, stepsRight, afterRight, _⟩ :=
    typed_drop_prefix (owner := 1) (body := 2) afterLeft bodyTyped
      (by simp [CommonDataSourceRules.adapted_at, graph, CommonDataSource.nodeAt, CommonDataSourceRules.adaptNode, CommonDataSource.adaptNode]) (by simp [CommonDataSourceRules.adapted_at, graph, CommonDataSource.nodeAt, CommonDataSourceRules.adaptNode, CommonDataSource.adaptNode]) installed (siteRight K) (callRight K) freshRight
      (by simpa [TreeDropCall.resume] using depthRight)
  exact ⟨middle, K, final, L, destroyedLeft, destroyedRight,
    stepsLeft, stepsRight, afterRight⟩

end Jihoo.CommonCaseChildConsumption
