import Jihoo.TreeCreateContext
import Jihoo.CommonDataTargetContextChecks

namespace Jihoo.TreeCreateContext.Checks
open CommonDataTargetContext CommonDataReference TreeCreateRelocation TreeCreateCfg
open RecursiveLexicalFields ReferenceCfg
open CommonDataReferenceChecks (image source source_valid related)

def q : Slots := ⟨8, 3, 6, 1, 5, 9, 2⟩
def heap := CommonDataTargetContext.Checks.heap
def ctx := CommonDataTargetContext.Checks.ctx
def env := CommonDataTargetContext.Checks.env
def slots : List Nat := [5, 8, 1, 0, 7, 10]
def locals : Array (Option ReferenceCfg.Value) :=
  #[some (.pointer 0 0), some (.pointer 4 0), none, none, none,
    some (.pointer 3 0), none, some (.i64 77), some (.pointer 3 0), none, some (.u64 9)]
def saved : List ReferenceCalls.Continuation := [⟨42, 17, #[some (.i64 7)], ⟨2, false⟩⟩]
def stop : Block := ⟨#[], .ret⟩
def body (node : Bool) : ReferenceCalls.Function :=
  ⟨⟨⟨#[.ptr, .ptr, .ptr, .ptr, .ptr, .ptr, .i64, .i64, .ptr, .ptr, .u64],
    #[stop, build q node 3, stop, stop, entry q node 5 1 1]⟩,
    #[none, none, none, none, none]⟩, #[]⟩
def program (node : Bool) : ReferenceCalls.Program := #[body node]

theorem initial : CommonContext [image, .nil 4] [(4,0)] [2] [] [] [10]
    ctx env slots source (stateAt 0 4 heap locals saved).frame := by
  have old := CommonDataTargetContext.Checks.initial
  refine ⟨⟨old.valid, old.agreement, ?_, old.resources, old.owned, old.separated, old.shells⟩, old.bufferSizes⟩
  exact .cons ⟨_, rfl, rfl⟩ (.cons ⟨_, rfl, rfl⟩
    (.cons ⟨_, rfl, rfl⟩ (.cons ⟨_, _, rfl, rfl⟩ (.cons ⟨_, rfl⟩ (.cons rfl .nil)))))

theorem placement (node : Bool) : Placement (body node) q node 5 1 4 1 3 := by
  cases node <;> constructor <;> decide

theorem safe : Safe (body true) q locals 5 1 := by
  constructor
  · decide
  · intro k hk
    simp only [Slots.writes, q, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with h | h | h | h | h | h | h <;> subst k <;> decide
  · intro k hk
    simp only [Slots.writes, q, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with h | h | h | h | h | h | h <;> subst k <;> decide
  all_goals decide

theorem preserved : Preserved (ctx.map (CommonData.capturedEntry 2 0 0)) slots q.writes := by
  intro k e slot he hs active
  cases k with
  | zero => simp [ctx, CommonDataTargetContext.Checks.ctx, CommonData.capturedEntry] at he; subst e; exact False.elim active
  | succ k =>
    cases k with
    | zero => simp [ctx, CommonDataTargetContext.Checks.ctx, CommonData.capturedEntry] at he; subst e; exact False.elim active
    | succ k =>
      cases k with
      | zero => simp [ctx, CommonDataTargetContext.Checks.ctx, CommonData.capturedEntry] at he; subst e; exact False.elim active
      | succ k =>
        cases k with
        | zero => simp [slots] at hs; subst slot; decide
        | succ k =>
          cases k with
          | zero => simp [slots] at hs; subst slot; decide
          | succ k =>
            cases k with
            | zero => simp [slots] at hs; subst slot; decide
            | succ k => simp [slots] at hs

/-- Both original aliases at locals 5/8 are retired. Swapped destinations 1/5
are safe; live buffer 0, scalar 7, nat 10 and suspended caller survive. -/
theorem swapped_boundary :
    Prefix (program true) 13 (stateAt 0 4 heap locals saved) [.alloc 6 24]
      (nodeOut q 0 3 heap 3 4 locals saved) ∧
    CommonContext [.node 8 6 image (.nil 4)] [(4,0)] [2] [] [] [10]
      (CommonData.capturedContext 2 0 0 ctx) (.data (some 8) :: env) (8 :: slots)
      (CommonData.allocate source (some 7) none) (nodeOut q 0 3 heap 3 4 locals saved).frame :=
  node_prefix_context (l := image) (r := .nil 4) (images := []) (buffers := [(4,0)])
    (q := q) (fn := 0) (start := 4) (work := 1) (cont := 3) (H := heap)
    (vs := locals) (ks := saved) (p := program true) (f := body true) initial (li := 0) (ri := 2) rfl rfl rfl rfl rfl
    (placement true) safe (by constructor <;> decide) preserved (by decide)

theorem alias_consumption : CommonData.capturedContext 2 0 0 ctx =
    [.data 0, .dead, .dead, .dead, .buffer 1, .scalar, .nat 9] := rfl

theorem live_locals_and_stack :
    (nodeOut q 0 3 heap 3 4 locals saved).frame.locals[0]? = locals[0]? ∧
    (nodeOut q 0 3 heap 3 4 locals saved).frame.locals[7]? = locals[7]? ∧
    (nodeOut q 0 3 heap 3 4 locals saved).frame.locals[10]? = locals[10]? ∧
    (nodeOut q 0 3 heap 3 4 locals saved).stack = saved := by decide

theorem scalar_clobber_rejected : ¬ Preserved [.scalar] [7] [7] := by
  intro h; exact h 0 .scalar 7 rfl rfl trivial (by simp)

theorem boxed_nil_alias_rejected : ¬ (targets (inventory [.nil 4, .nil 4] [])).Nodup := by decide

theorem boxed_nil_prefix :
    Prefix (program false) 3 (stateAt 0 4 heap locals saved) [.alloc 6 8]
      (nilOut q 0 3 heap locals saved) :=
  (TreeCreateRelocation.nil_total rfl (placement false) rfl (by decide) (by constructor <;> decide) source).1

/-- Nil retains a nonempty lexical context, including duplicate Tree aliases,
Buffer, scalar and natural bindings. Move the alias at result slot 8 to slot 5:
unlike Node, Nil consumes no aliases, so every old binding must survive. -/
theorem nil_boundary :
    Prefix (program false) 3 (stateAt 0 4 heap locals saved) [.alloc 6 8]
      (nilOut q 0 3 heap locals saved) ∧
    CommonContext [.nil 6, image, .nil 4] [(4,0)] [2] [] [] [10]
      [.data 0, .data 1, .data 1, .data 2, .buffer 3, .scalar, .nat 9]
      (.data none :: env) [8, 5, 5, 1, 0, 7, 10] source
      (nilOut q 0 3 heap locals saved).frame ∧
    (nilOut q 0 3 heap locals saved).frame.locals[0]? = some (some (.pointer 0 0)) ∧
    (nilOut q 0 3 heap locals saved).frame.locals[7]? = some (some (.i64 77)) ∧
    (nilOut q 0 3 heap locals saved).frame.locals[10]? = some (some (.u64 9)) ∧
    (nilOut q 0 3 heap locals saved).frame.heap.toList.take heap.size = heap.toList ∧
    (nilOut q 0 3 heap locals saved).frame.heap[10]? = none ∧
    (nilOut q 0 3 heap locals saved).stack = saved := by
  have h : CommonContext [image, .nil 4] [(4,0)] [2] [] [] [10]
      ctx env [5, 5, 1, 0, 7, 10] source (stateAt 0 4 heap locals saved).frame := by
    refine ⟨⟨initial.valid, initial.agreement, ?_, initial.resources,
      initial.owned, initial.separated, initial.shells⟩, initial.bufferSizes⟩
    exact .cons ⟨_, rfl, rfl⟩ (.cons ⟨_, rfl, rfl⟩
      (.cons ⟨_, rfl, rfl⟩ (.cons ⟨_, _, rfl, rfl⟩ (.cons ⟨_, rfl⟩ (.cons rfl .nil)))))
  have fresh : Preserved (ctx.map (CommonData.capturedEntry 0 2 0))
      [5, 5, 1, 0, 7, 10] [q.result] := by
    intro k e slot _ hs _
    have member := List.mem_of_getElem? hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    simp only [List.mem_singleton, q]
    omega
  have boundary := nil_prefix_context (q := q) (fn := 0) (start := 4) (work := 1) (cont := 3)
    (H := heap) (vs := locals) (ks := saved) (p := program false) (f := body false)
    h rfl (placement false) rfl (by decide) (by constructor <;> decide) fresh (by decide)
  exact ⟨boundary.1, boundary.2, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

def graph : CommonData.Graph := #[.core (.var 0), .core (.var 2), .construct 0 1]
theorem typed_constructor : CommonData.Typing graph ctx 2 [] 2 .data :=
  .construct rfl rfl rfl rfl rfl

theorem source_execution :
    CommonData.Eval graph env 2 source (.data (some 8)) [.alloc 8 0]
      (CommonData.allocate source (some 7) none) :=
  source_construct initial (li := 0) (ri := 2) rfl rfl rfl rfl rfl

end Jihoo.TreeCreateContext.Checks
