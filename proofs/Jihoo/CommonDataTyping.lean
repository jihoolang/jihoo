import Jihoo.CommonDataDestroy
import Jihoo.CommonDataPartition
import Jihoo.CommonDataBufferContext

/-! One closing-instance judgment for binary data reconstruction and existing
scalar Buffer Core, recursive Buffer allocation/release, and binary Drop. No dependent motives are admitted. -/
namespace Jihoo.CommonData
open RecursiveFieldRuntime RecursiveLexicalFields RecursiveBodyProjection

inductive Typing (g : Graph) : List Entry → Nat → List Nat → Nat → Result → Prop where
  | core : nodeAt g term = .embedded body →
      SizedCoreTyping.Typing (coreGraph g) (context 0 ctx) sizes body .scalar →
      Typing g ctx 0 sizes term .scalar
  | literal : nodeAt g term = .core (.integer n) → n < 2^63 →
      Typing g ctx 0 [] term .scalar
  | empty : nodeAt g term = .empty → Typing g ctx 0 [] term .data
  | dataVar : nodeAt g term = .core (.var index) → ctx[index]? = some (.data 0) →
      Typing g ctx 1 [] term .data
  | construct : nodeAt g term = .construct l r →
      nodeAt g l = .core (.var li) → ctx[li]? = some (.data 0) →
      nodeAt g r = .core (.var ri) → ctx[ri]? = some (.data 1) →
      Typing g ctx 2 [] term .data
  | bufferLet : nodeAt g term = .core (.app fn arg) →
      nodeAt g fn = .core (.lam false ty body) → nodeAt g ty = .core .i64 →
      SizedCoreTyping.Typing (coreGraph g) (context count ctx) sizes arg .scalar →
      Typing g (continuation count ctx) count [] body kind →
      Typing g ctx count sizes term kind
  | allocate : nodeAt g term = .core (.app fn arg) →
      nodeAt g fn = .core (.lam false ty body) →
      nodeAt g ty = .core (.buffer lengthTy) →
      DependentBufferIndices.BufferLength (coreGraph g)
        (SizedBufferContext.naturalEnv (context count ctx)) ty n →
      nodeAt g arg = .core (.alloc len init) →
      DependentBufferIndices.Eval (coreGraph g)
        (SizedBufferContext.naturalEnv (context count ctx)) len n →
      SizedCoreTyping.ScalarTyped (coreGraph g) (context count ctx) init →
      Typing g (freshBuffer count ctx) count (n :: sizes) body kind →
      Typing g ctx count sizes term kind
  /-- A direct Buffer application consumes only the selected prefix. -/
  | bufferApp : nodeAt g term = .core (.app fn arg) →
      nodeAt g fn = .core (.lam false ty body) →
      nodeAt g ty = .core (.buffer lengthTy) → p ≤ sizes.length →
      DependentBufferIndices.BufferLength (coreGraph g)
        (SizedBufferContext.naturalEnv (context count ctx)) ty n →
      SizedCoreTyping.Typing (coreGraph g)
        (SizedBufferContext.producer (context count ctx) p) (sizes.take p) arg (.owner n) →
      Typing g (bufferCall count p ctx) count (n :: sizes.drop p) body kind →
      Typing g ctx count sizes term kind
  | freeBuffer : nodeAt g term = .core (.free owner body) →
      nodeAt g owner = .core (.var index) → ctx[index]? = some (.buffer (count+slot)) →
      slot < sizes.length →
      Typing g (consumeBuffer (count+slot) ctx) count (sizes.eraseIdx slot) body kind →
      Typing g ctx count sizes term kind
  | dataLet : nodeAt g term = .core (.app fn arg) →
      nodeAt g fn = .core (.lam false ty body) → nodeAt g ty = .ind 0 [] →
      Typing g ctx count sizes arg .data →
      Typing g (dataContinuation ctx) 1 [] body kind →
      Typing g ctx count sizes term kind
  | dataLetSplit : activeCount + retainedCount = count → usedSizes ++ savedSizes = sizes →
      nodeAt g term = .core (.app fn arg) →
      nodeAt g fn = .core (.lam false ty body) → nodeAt g ty = .ind 0 [] →
      Typing g (argumentContext activeCount retainedCount usedSizes.length ctx)
        activeCount usedSizes arg .data →
      Typing g (capturedContext activeCount retainedCount usedSizes.length ctx)
        (retainedCount+1) savedSizes body kind →
      Typing g ctx count sizes term kind
  | drop : nodeAt g term = .drop 0 owner body →
      nodeAt g owner = .core (.var index) → ctx[index]? = some (.data 0) →
      Typing g (removeHead ctx) count sizes body kind →
      Typing g ctx (count+1) sizes term kind
  | caseTree : nodeAt g term = .caseTree scrutinee nilBranch nodeBranch ghosts →
      nodeAt g scrutinee = .core (.var index) → ctx[index]? = some (.data 0) →
      Typing g (removeHead ctx) count sizes nilBranch kind →
      Typing g (bindContext ghosts ctx) (count+2) sizes nodeBranch kind →
      Typing g ctx (count+1) sizes term kind

/-- One operational relation for old Core execution and the added data nodes.
The datatype is exactly empty/binary-node; no external branch/tag oracle occurs. -/
inductive Eval (g : Graph) : List Value → Nat → State → Value →
    List HeapLeases.Event → State → Prop where
  | core : nodeAt g term = .embedded body →
      SizedCoreExecution.Eval (coreGraph g) (environment env) body s.buffers (.scalar n) es t →
      Eval g env term s (.scalar n) (es.map SizedBufferHeap.Event.project) ⟨t,s.cells⟩
  | literal : nodeAt g term = .core (.integer n) → Eval g env term s (.scalar n) [] s
  | empty : nodeAt g term = .empty → Eval g env term s (.data none) [] s
  | dataVar : nodeAt g term = .core (.var index) → env[index]? = some (.data ref) →
      Eval g env term s (.data ref) [] s
  | construct : nodeAt g term = .construct l r →
      nodeAt g l = .core (.var li) → env[li]? = some (.data left) →
      nodeAt g r = .core (.var ri) → env[ri]? = some (.data right) →
      Eval g env term s (.data (some s.buffers.heap.nextObject))
        [.alloc s.buffers.heap.nextObject 0] (allocate s left right)
  | bufferLet : nodeAt g term = .core (.app fn arg) →
      nodeAt g fn = .core (.lam false ty body) → nodeAt g ty = .core .i64 →
      SizedCoreExecution.Eval (coreGraph g) (environment env) arg s.buffers (.scalar n) before middle →
      Eval g (.scalar n :: env) body ⟨middle,s.cells⟩ result after t →
      Eval g env term s result (before.map SizedBufferHeap.Event.project ++ after) t
  /-- The runtime evaluates an owner argument independently. Typing checks a
  prefix-partitioned producer and the body with the common judgment. -/
  | allocate : nodeAt g term = .core (.app fn arg) →
      nodeAt g fn = .core (.lam false ty body) → nodeAt g ty = .core (.buffer lengthTy) →
      SizedCoreExecution.Eval (coreGraph g) (environment env) arg s.buffers
        (.owner x) before middle →
      Eval g (.buffer x :: env) body ⟨middle,s.cells⟩ result after t →
      Eval g env term s result (before.map SizedBufferHeap.Event.project ++ after) t
  | freeBuffer : nodeAt g term = .core (.free owner body) →
      nodeAt g owner = .core (.var index) → env[index]? = some (.buffer x) →
      Eval g env body ⟨SizedBufferHeap.release s.buffers x,s.cells⟩ result events t →
      Eval g env term s result (.free x :: events) t
  | dataLet : nodeAt g term = .core (.app fn arg) →
      nodeAt g fn = .core (.lam false ty body) → nodeAt g ty = .ind 0 [] →
      Eval g env arg s (.data ref) before middle →
      Eval g (.data ref :: env) body middle result after t →
      Eval g env term s result (before ++ after) t
  | drop : nodeAt g term = .drop 0 owner body →
      nodeAt g owner = .core (.var index) → env[index]? = some (.data ref) →
      Destroy ref s before middle → Eval g env body middle result after t →
      Eval g env term s result (before ++ after) t
  | emptyCase : nodeAt g term = .caseTree scrutinee nilBranch nodeBranch ghosts →
      nodeAt g scrutinee = .core (.var index) → env[index]? = some (.data none) →
      Eval g env nilBranch s result es t → Eval g env term s result es t
  | nodeCase : nodeAt g term = .caseTree scrutinee nilBranch nodeBranch ghosts →
      nodeAt g scrutinee = .core (.var index) →
      enter s.recursive env index ghosts = some (opened,parent) →
      Eval g opened nodeBranch s result es t →
      Eval g env term s result (es ++ [.free parent]) (finish t parent)

end Jihoo.CommonData
