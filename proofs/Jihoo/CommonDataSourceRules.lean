import Jihoo.CommonDataSource
import Jihoo.CommonDataAccounting

/-! Source typing for constant-result binary Case with arbitrary typed branches.
The adapter alone is not a certificate: source Typing checks the motive kind.
No dependent motives, production-checker refinement or new runtime is asserted. -/
namespace Jihoo.CommonDataSourceRules
open CommonDataSource RecursiveLexicalFields RecursiveBodyProjection

/-- The result annotation is recognized before its binder is discarded. -/
def resultType (g : CommonDataSource.Graph) (id : Nat) : Option CommonData.Result :=
  match CommonDataSource.nodeAt g id with
  | .ind 0 [] => some .data
  | .core .i64 => some .scalar
  | _ => none

def motiveKind (g : CommonDataSource.Graph) (id : Nat) : Option CommonData.Result :=
  match CommonDataSource.nodeAt g id with
  | .core (.lam false domain body) =>
    if binaryType g domain then resultType g body else none
  | _ => none

/-- Generalizes the strict adapter, retaining original IDs. Source Typing below
is required to tie a Case's result to the recognized motive. -/
def adaptNode (g : CommonDataSource.Graph) : CommonDataSource.Node → CommonData.Node
  | .caseOf 0 motive [nil,node] value =>
    match motiveKind g motive, branchBody g node with
    | some _, some body => .caseTree value nil body 0
    | _, _ => .core .opaque
  | .caseOf _ _ _ _ => .core .opaque
  | n => CommonDataSource.adaptNode g n

def graph (g : CommonDataSource.Graph) : CommonData.Graph := g.map (adaptNode g)

theorem adapted_at {id : Nat} :
    CommonData.nodeAt (graph g) id = adaptNode g (CommonDataSource.nodeAt g id) := by
  cases found : g[id]? <;>
    simp [CommonData.nodeAt, CommonDataSource.nodeAt, graph, Array.getElem?_map,
      found, adaptNode, CommonDataSource.adaptNode]

inductive Typing (g : CommonDataSource.Graph) :
    List Entry → Nat → List Nat → Nat → CommonData.Result → Prop where
  | literal : CommonDataSource.nodeAt g term = .core (.integer n) → n < 2^63 →
      Typing g ctx 0 [] term .scalar
  | empty : CommonDataSource.nodeAt g term = .con 0 0 [] → Typing g ctx 0 [] term .data
  | dataVar : CommonDataSource.nodeAt g term = .core (.var index) → ctx[index]? = some (.data 0) →
      Typing g ctx 1 [] term .data
  | construct : CommonDataSource.nodeAt g term = .con 0 1 [l,r] →
      CommonDataSource.nodeAt g l = .core (.var li) → ctx[li]? = some (.data 0) →
      CommonDataSource.nodeAt g r = .core (.var ri) → ctx[ri]? = some (.data 1) →
      Typing g ctx 2 [] term .data
  | bufferLet : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .core .i64 →
      SizedCoreTyping.Typing (CommonData.coreGraph (graph g)) (context count ctx) sizes arg .scalar →
      Typing g (continuation count ctx) count [] body kind →
      Typing g ctx count sizes term kind
  | allocate : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .core (.buffer lengthTy) →
      DependentBufferIndices.BufferLength (CommonData.coreGraph (graph g))
        (SizedBufferContext.naturalEnv (context count ctx)) ty n →
      CommonDataSource.nodeAt g arg = .core (.alloc len init) →
      DependentBufferIndices.Eval (CommonData.coreGraph (graph g))
        (SizedBufferContext.naturalEnv (context count ctx)) len n →
      SizedCoreTyping.ScalarTyped (CommonData.coreGraph (graph g)) (context count ctx) init →
      Typing g (CommonData.freshBuffer count ctx) count (n :: sizes) body kind →
      Typing g ctx count sizes term kind
  /-- A direct Buffer application consumes only the selected prefix. -/
  | bufferApp : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .core (.buffer lengthTy) → p ≤ sizes.length →
      DependentBufferIndices.BufferLength (CommonData.coreGraph (graph g))
        (SizedBufferContext.naturalEnv (context count ctx)) ty n →
      SizedCoreTyping.Typing (CommonData.coreGraph (graph g))
        (SizedBufferContext.producer (context count ctx) p) (sizes.take p) arg (.owner n) →
      Typing g (CommonData.bufferCall count p ctx) count (n :: sizes.drop p) body kind →
      Typing g ctx count sizes term kind
  | freeBuffer : CommonDataSource.nodeAt g term = .core (.free owner body) →
      CommonDataSource.nodeAt g owner = .core (.var index) → ctx[index]? = some (.buffer (count+slot)) →
      slot < sizes.length →
      Typing g (CommonData.consumeBuffer (count+slot) ctx) count (sizes.eraseIdx slot) body kind →
      Typing g ctx count sizes term kind
  | dataLet : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .ind 0 [] →
      Typing g ctx count sizes arg .data →
      Typing g (CommonData.dataContinuation ctx) 1 [] body kind →
      Typing g ctx count sizes term kind
  | dataLetSplit : activeCount + retainedCount = count → usedSizes ++ savedSizes = sizes →
      CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .ind 0 [] →
      Typing g (CommonData.argumentContext activeCount retainedCount usedSizes.length ctx)
        activeCount usedSizes arg .data →
      Typing g (CommonData.capturedContext activeCount retainedCount usedSizes.length ctx)
        (retainedCount+1) savedSizes body kind →
      Typing g ctx count sizes term kind
  | drop : CommonDataSource.nodeAt g term = .drop 0 owner body →
      CommonDataSource.nodeAt g owner = .core (.var index) → ctx[index]? = some (.data 0) →
      Typing g (CommonData.removeHead ctx) count sizes body kind →
      Typing g ctx (count+1) sizes term kind
  | caseTree : CommonDataSource.nodeAt g term = .caseOf 0 motive [nil,node] scrutinee →
      motiveKind g motive = some kind → branchBody g node = some body →
      CommonDataSource.nodeAt g scrutinee = .core (.var index) → ctx[index]? = some (.data 0) →
      Typing g (CommonData.removeHead ctx) count sizes nil kind →
      Typing g (bindContext 0 ctx) (count+2) sizes body kind →
      Typing g ctx (count+1) sizes term kind

private theorem core_shape {id : Nat} (h : CommonDataSource.nodeAt g id = .core n) :
    CommonData.nodeAt (graph g) id = .core n := by
  simp [adapted_at,h,adaptNode,CommonDataSource.adaptNode]

private theorem ind_shape {id : Nat} (h : CommonDataSource.nodeAt g id = .ind 0 []) :
    CommonData.nodeAt (graph g) id = .ind 0 [] := by
  simp [adapted_at,h,adaptNode,CommonDataSource.adaptNode]

/-- Every source rule, including recursively nested Case/application bodies,
elaborates to the existing common ownership judgment. -/
theorem Typing.elaborate (typed : Typing g ctx count sizes term kind) :
    CommonData.Typing (graph g) ctx count sizes term kind := by
  induction typed with
  | literal shape bound => exact .literal (core_shape shape) bound
  | empty shape => exact .empty (by simp [adapted_at,shape,adaptNode,CommonDataSource.adaptNode])
  | dataVar shape lookup => exact .dataVar (core_shape shape) lookup
  | construct shape left li right ri =>
    exact .construct (by simp [adapted_at,shape,adaptNode,CommonDataSource.adaptNode])
      (core_shape left) li (core_shape right) ri
  | bufferLet shape fn ty arg body ih =>
    exact .bufferLet (core_shape shape) (core_shape fn) (core_shape ty) arg ih
  | allocate shape fn ty annotation alloc len init body ih =>
    exact .allocate (core_shape shape) (core_shape fn) (core_shape ty) annotation
      (core_shape alloc) len init ih
  | bufferApp shape fn ty limit annotation arg body ih =>
    exact .bufferApp (core_shape shape) (core_shape fn) (core_shape ty) limit annotation arg ih
  | freeBuffer shape owner lookup bound body ih =>
    exact .freeBuffer (core_shape shape) (core_shape owner) lookup bound ih
  | dataLet shape fn ty arg body ia ib =>
    exact .dataLet (core_shape shape) (core_shape fn) (ind_shape ty) ia ib
  | dataLetSplit counts sizes shape fn ty arg body ia ib =>
    exact .dataLetSplit counts sizes (core_shape shape) (core_shape fn) (ind_shape ty) ia ib
  | drop shape owner lookup body ih =>
    exact .drop (by simp [adapted_at,shape,adaptNode,CommonDataSource.adaptNode])
      (core_shape owner) lookup ih
  | caseTree shape motive branch scrutinee lookup nil node ihNil ihNode =>
    exact .caseTree (by simp [adapted_at,shape,adaptNode,motive,branch])
      (core_shape scrutinee) lookup ihNil ihNode

/-- The source judgment cannot ignore a scalar/Data mismatch in a Case motive. -/
theorem Typing.case_motive {value : Nat}
    (shape : CommonDataSource.nodeAt g term = .caseOf 0 motive [nil,node] value)
    (typed : Typing g ctx count sizes term kind) : motiveKind g motive = some kind := by
  cases typed <;> simp_all

/-- Top-level export certificate retains the existing source/family validation
and checks a direct Tree -> scalar/Data signature against its original body. -/
def CheckedEntry (s : Source) (kind : CommonData.Result) : Prop :=
  valid s = true ∧ familyValid s = true ∧
  ∃ body domain result annotation,
    CommonDataSource.nodeAt s.nodes s.typeRoot = .core (.pi false domain result) ∧
    CommonDataSource.nodeAt s.nodes s.root = .core (.lam false annotation body) ∧
    binaryType s.nodes domain = true ∧ binaryType s.nodes annotation = true ∧
    resultType s.nodes result = some kind ∧ Typing s.nodes [.data 0] 1 [] body kind

theorem CheckedEntry.elaborate (checked : CheckedEntry s kind) :
    ∃ body annotation, CommonDataSource.nodeAt s.nodes s.root = .core (.lam false annotation body) ∧
      CommonData.Typing (graph s.nodes) [.data 0] 1 [] body kind := by
  obtain ⟨_,_,body,domain,result,annotation,_,shape,_,_,_,typed⟩ := checked
  exact ⟨body,annotation,shape,typed.elaborate⟩

open CommonData HeapLeases LinearHeapPrograms RecursiveFieldRuntime RecursiveFieldOwnership

/-- Safety and allocation conservation are inherited from common typing, not
assumed as conditions of source typing. -/
theorem Typing.total_accounted (typed : Typing g ctx count sizes term kind)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) ctx env)
    (layout : SizedBufferContext.Layout s.buffers owners sizes) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) :
    ∃ v es t, Eval (graph g) env term s v es t ∧ Steps s.buffers.heap es t.buffers.heap ∧
      Valid t.buffers.heap ∧ AccountedPost kind t v frame (footprint (caps trees owners)) es :=
  typed.elaborate.total_accounted length agreement layout valid owned fields

end Jihoo.CommonDataSourceRules
