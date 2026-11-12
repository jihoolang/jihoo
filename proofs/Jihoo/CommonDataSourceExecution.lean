import Jihoo.CommonDataSourceRules

/-! Independent big-step rules over the restricted source constructor view.
Core scalar execution and the abstract heap/store primitives are shared. -/
namespace Jihoo.CommonDataSourceExecution
open CommonDataSource CommonDataSourceRules CommonData RecursiveLexicalFields
open RecursiveBodyProjection RecursiveFieldRuntime RecursiveFieldOwnership
open HeapLeases LinearHeapPrograms

def coreNode : CommonDataSource.Node → ScopedLend.Graph.Node
  | .core n => n
  | _ => .opaque

def sourceCore (g : CommonDataSource.Graph) := g.map coreNode

private theorem project_case (a : Option Result) (b : Option Nat) (value nil : Nat) :
    CommonData.projectNode (match a,b with
      | some _,some body => .caseTree value nil body 0
      | _,_ => .core .opaque) = .opaque := by
  cases a <;> cases b <;> rfl

private theorem project_adapt (n : CommonDataSource.Node) :
    CommonData.projectNode (CommonDataSourceRules.adaptNode g n) = coreNode n := by
  cases n <;> simp only [CommonDataSourceRules.adaptNode,CommonDataSource.adaptNode,coreNode]
  all_goals repeat first | rfl | (split <;> simp_all [CommonData.projectNode])
  all_goals exact project_case _ _ _ _

theorem sourceCore_eq : sourceCore g = coreGraph (graph g) := by
  simp only [sourceCore,coreGraph,graph,Array.map_map]
  congr 1
  funext n
  exact (project_adapt n).symm

inductive Eval (g : CommonDataSource.Graph) : List Value → Nat → CommonData.State → Value →
    List Event → CommonData.State → Prop where
  | literal : CommonDataSource.nodeAt g term = .core (.integer n) →
      Eval g env term s (.scalar n) [] s
  | empty : CommonDataSource.nodeAt g term = .con 0 0 [] → Eval g env term s (.data none) [] s
  | dataVar : CommonDataSource.nodeAt g term = .core (.var index) → env[index]? = some (.data ref) →
      Eval g env term s (.data ref) [] s
  | construct : CommonDataSource.nodeAt g term = .con 0 1 [l,r] →
      CommonDataSource.nodeAt g l = .core (.var li) → env[li]? = some (.data left) →
      CommonDataSource.nodeAt g r = .core (.var ri) → env[ri]? = some (.data right) →
      Eval g env term s (.data (some s.buffers.heap.nextObject))
        [.alloc s.buffers.heap.nextObject 0] (allocate s left right)
  | bufferLet : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .core .i64 →
      SizedCoreExecution.Eval (sourceCore g) (environment env) arg s.buffers (.scalar n) before middle →
      Eval g (.scalar n :: env) body ⟨middle,s.cells⟩ result after t →
      Eval g env term s result (before.map SizedBufferHeap.Event.project ++ after) t
  | allocate : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) → CommonDataSource.nodeAt g ty = .core (.buffer lengthTy) →
      SizedCoreExecution.Eval (sourceCore g) (environment env) arg s.buffers
        (.owner x) before middle →
      Eval g (.buffer x :: env) body ⟨middle,s.cells⟩ result after t →
      Eval g env term s result (before.map SizedBufferHeap.Event.project ++ after) t
  | freeBuffer : CommonDataSource.nodeAt g term = .core (.free owner body) →
      CommonDataSource.nodeAt g owner = .core (.var index) → env[index]? = some (.buffer x) →
      Eval g env body ⟨SizedBufferHeap.release s.buffers x,s.cells⟩ result events t →
      Eval g env term s result (.free x :: events) t
  | dataLet : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .ind 0 [] →
      Eval g env arg s (.data ref) before middle →
      Eval g (.data ref :: env) body middle result after t →
      Eval g env term s result (before ++ after) t
  | drop : CommonDataSource.nodeAt g term = .drop 0 owner body →
      CommonDataSource.nodeAt g owner = .core (.var index) → env[index]? = some (.data ref) →
      Destroy ref s before middle → Eval g env body middle result after t →
      Eval g env term s result (before ++ after) t
  | emptyCase : CommonDataSource.nodeAt g term = .caseOf 0 motive [nil,node] scrutinee →
      motiveKind g motive = some kind → branchBody g node = some body →
      CommonDataSource.nodeAt g scrutinee = .core (.var index) → env[index]? = some (.data none) →
      Eval g env nil s result es t → Eval g env term s result es t
  | nodeCase : CommonDataSource.nodeAt g term = .caseOf 0 motive [nil,node] scrutinee →
      motiveKind g motive = some kind → branchBody g node = some body →
      CommonDataSource.nodeAt g scrutinee = .core (.var index) →
      enter s.recursive env index 0 = some (opened,parent) →
      Eval g opened body s result es t →
      Eval g env term s result (es ++ [.free parent]) (finish t parent)

private theorem adapted_shape {id : Nat} (h : CommonDataSource.nodeAt g id = n) :
    CommonData.nodeAt (graph g) id = CommonDataSourceRules.adaptNode g n := by
  rw [CommonDataSourceRules.adapted_at,h]

private theorem core_shape {id : Nat} (h : CommonDataSource.nodeAt g id = .core n) :
    CommonData.nodeAt (graph g) id = .core n := by
  simp [CommonDataSourceRules.adapted_at,h,CommonDataSourceRules.adaptNode,CommonDataSource.adaptNode]
private theorem ind_shape {id : Nat} (h : CommonDataSource.nodeAt g id = .ind 0 []) :
    CommonData.nodeAt (graph g) id = .ind 0 [] := by
  simp [CommonDataSourceRules.adapted_at,h,CommonDataSourceRules.adaptNode,CommonDataSource.adaptNode]

theorem Eval.to_common (run : Eval g env term s v es t) :
    CommonData.Eval (graph g) env term s v es t := by
  induction run with
  | literal h => exact .literal (core_shape h)
  | empty h => exact .empty (by simp [CommonDataSourceRules.adapted_at,h,CommonDataSourceRules.adaptNode,CommonDataSource.adaptNode])
  | dataVar h lookup => exact .dataVar (core_shape h) lookup
  | construct h l li r ri =>
    exact .construct (by simp [CommonDataSourceRules.adapted_at,h,CommonDataSourceRules.adaptNode,CommonDataSource.adaptNode]) (core_shape l) li (core_shape r) ri
  | bufferLet h fn ty arg body ih => exact .bufferLet (core_shape h) (core_shape fn) (core_shape ty) (by simpa only [sourceCore_eq] using arg) ih
  | allocate h fn ty arg body ih =>
    exact .allocate (core_shape h) (core_shape fn) (core_shape ty) (by simpa only [sourceCore_eq] using arg) ih
  | freeBuffer h owner lookup body ih => exact .freeBuffer (core_shape h) (core_shape owner) lookup ih
  | dataLet h fn ty arg body ia ib => exact .dataLet (core_shape h) (core_shape fn) (ind_shape ty) ia ib
  | drop h owner lookup destroyed body ih =>
    exact .drop (by simp [CommonDataSourceRules.adapted_at,h,CommonDataSourceRules.adaptNode,CommonDataSource.adaptNode]) (core_shape owner) lookup destroyed ih
  | emptyCase h motive branch scrutinee lookup body ih =>
    have shape := adapted_shape h
    simp only [CommonDataSourceRules.adaptNode,motive,branch] at shape
    exact .emptyCase shape (core_shape scrutinee) lookup ih
  | nodeCase h motive branch scrutinee entered body ih =>
    have shape := adapted_shape h
    simp only [CommonDataSourceRules.adaptNode,motive,branch] at shape
    exact .nodeCase shape (core_shape scrutinee) entered ih

/-- Reflection is restricted by source typing; the adapter alone loses motive information. -/
theorem reflect (typed : CommonDataSourceRules.Typing g ctx count sizes term kind)
    (run : CommonData.Eval (graph g) env term s v es t) : Eval g env term s v es t := by
  induction typed generalizing env s v es t with
  | literal shape bound =>
    have h := core_shape shape
    cases run <;> simp_all
    exact .literal shape
  | empty shape =>
    have h := adapted_shape shape
    simp only [CommonDataSourceRules.adaptNode,CommonDataSource.adaptNode] at h
    cases run <;> simp_all
    exact .empty shape
  | dataVar shape lookup =>
    have h := core_shape shape
    cases run <;> simp_all
    exact .dataVar shape (by assumption)
  | construct shape l li r ri =>
    have h := adapted_shape shape
    simp only [CommonDataSourceRules.adaptNode,CommonDataSource.adaptNode] at h
    have hl := core_shape l
    have hr := core_shape r
    cases run <;> simp_all
    exact .construct shape l (by assumption) r (by assumption)
  | bufferLet shape fn ty arg body ih =>
    have h := core_shape shape
    have hf := core_shape fn
    have ht := core_shape ty
    cases run <;> simp_all
    exact .bufferLet shape fn ty (by simpa only [sourceCore_eq] using (by assumption : SizedCoreExecution.Eval _ _ _ _ _ _ _)) (ih (by assumption))
  | allocate shape fn ty annotation alloc len init body ih =>
    have h := core_shape shape
    have hf := core_shape fn
    have ht := core_shape ty
    cases run <;> simp_all
    exact .allocate shape fn ty (by simpa only [sourceCore_eq] using (by assumption : SizedCoreExecution.Eval _ _ _ _ _ _ _)) (ih (by assumption))
  | bufferApp shape fn ty limit annotation arg body ih =>
    have h := core_shape shape
    have hf := core_shape fn
    have ht := core_shape ty
    cases run <;> simp_all
    exact .allocate shape fn ty (by simpa only [sourceCore_eq] using (by assumption : SizedCoreExecution.Eval _ _ _ _ _ _ _)) (ih (by assumption))
  | freeBuffer shape owner lookup bound body ih =>
    have h := core_shape shape
    have ho := core_shape owner
    cases run <;> simp_all
    exact .freeBuffer shape owner (by assumption) (ih (by assumption))
  | dataLet shape fn ty arg body ia ib =>
    have h := core_shape shape
    have hf := core_shape fn
    have ht := ind_shape ty
    cases run <;> simp_all
    exact .dataLet shape fn ty (ia (by assumption)) (ib (by assumption))
  | dataLetSplit counts sizes shape fn ty arg body ia ib =>
    have h := core_shape shape
    have hf := core_shape fn
    have ht := ind_shape ty
    cases run <;> simp_all
    exact .dataLet shape fn ty (ia (by assumption)) (ib (by assumption))
  | drop shape owner lookup body ih =>
    have h := adapted_shape shape
    simp only [CommonDataSourceRules.adaptNode,CommonDataSource.adaptNode] at h
    have ho := core_shape owner
    cases run <;> simp_all
    exact .drop shape owner (by assumption) (by assumption) (ih (by assumption))
  | caseTree shape motive branch scrutinee lookup nil node ihNil ihNode =>
    have h := adapted_shape shape
    simp only [CommonDataSourceRules.adaptNode,motive,branch] at h
    have hs := core_shape scrutinee
    cases run <;> simp_all
    · exact .emptyCase shape motive branch scrutinee (by assumption) (ihNil (by assumption))
    · exact .nodeCase shape motive branch scrutinee (by assumption) (ihNode (by assumption))

/-- Existence is derived from typing and initial ownership, with no execution premise. -/
theorem total_accounted (typed : CommonDataSourceRules.Typing g ctx count sizes term kind)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) :
    ∃ v es t, Eval g env term s v es t ∧ Steps s.buffers.heap es t.buffers.heap ∧
      Valid t.buffers.heap ∧ AccountedPost kind t v frame (footprint (caps trees owners)) es := by
  obtain ⟨v,es,t,run,steps,valid,post⟩ :=
    typed.total_accounted length agreement layout valid owned fields
  exact ⟨v,es,t,reflect typed run,steps,valid,post⟩

theorem Eval.deterministic (a : Eval g env term s v es t) (b : Eval g env term s w fs u) :
    v = w ∧ es = fs ∧ t = u := a.to_common.deterministic b.to_common

theorem correspondence (typed : CommonDataSourceRules.Typing g ctx count sizes term kind) :
    Eval g env term s v es t ↔ CommonData.Eval (graph g) env term s v es t :=
  ⟨Eval.to_common,reflect typed⟩

theorem every_run_accounted (typed : CommonDataSourceRules.Typing g ctx count sizes term kind)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) (run : Eval g env term s v es t) :
    AccountedPost kind t v frame (footprint (caps trees owners)) es :=
  typed.elaborate.every_run_accounted length agreement layout valid owned fields run.to_common

end Jihoo.CommonDataSourceExecution
