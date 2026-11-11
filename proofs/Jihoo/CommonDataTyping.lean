import Jihoo.CommonDataDestroy

/-! One closing-instance judgment for binary data reconstruction and existing
scalar Buffer Core and store-driven binary Drop. No dependent motives are admitted. -/
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
  | dataLet : nodeAt g term = .core (.app fn arg) →
      nodeAt g fn = .core (.lam false ty body) → nodeAt g ty = .ind 0 [] →
      Typing g ctx count sizes arg .data →
      Typing g (dataContinuation ctx) 1 [] body kind →
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
