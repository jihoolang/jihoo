import Jihoo.SizedBufferContext
import Jihoo.SizedOwnedLend

/-! Direct source-graph execution for uniform sized buffers. Proof arguments
and annotations do not authorize memory operations at runtime. Safety is a
separate consequence of closing-instance typing, not a premise of execution. -/
namespace Jihoo.SizedCoreExecution
open ScopedLend SizedBufferContext
abbrev State := SizedBufferHeap.State
abbrev Event := SizedBufferHeap.Event

inductive Scalar (g : Graph.Graph) (env : Env) : Nat → Nat → Prop where
  | literal : Graph.nodeAt g root = .integer v → Scalar g env root v
  | var : Graph.nodeAt g root = .var k → env[k]? = some (.scalar v) → Scalar g env root v

/-- Source nodes and binder order are retained, including both annotations. -/
inductive ReadLend (g : Graph.Graph) (root owner refTy index proof ownerTy body : Nat) : Prop where
  | intro : Graph.nodeAt g root = .lend owner reader cont →
      Graph.nodeAt g reader = .lam false refTy readRoot →
      Graph.nodeAt g readRoot = .index operand index proof →
      Graph.nodeAt g operand = .var 0 →
      Graph.nodeAt g cont = .lam false scalarTy inner →
      Graph.nodeAt g scalarTy = .i64 →
      Graph.nodeAt g inner = .lam false ownerTy body →
      ReadLend g root owner refTy index proof ownerTy body

/-- A reader allocates a fresh buffer from one in-bounds element. Its result
length is independent of the original borrowed length. -/
inductive OwnedReadLend (g : Graph.Graph)
    (root owner refTy length index proof resultTy ownerTy body : Nat) : Prop where
  | intro : Graph.nodeAt g root = .lend owner reader cont →
      Graph.nodeAt g reader = .lam false refTy allocation →
      Graph.nodeAt g allocation = .alloc length readRoot →
      Graph.nodeAt g readRoot = .index operand index proof →
      Graph.nodeAt g operand = .var 0 →
      Graph.nodeAt g cont = .lam false resultTy inner →
      Graph.nodeAt g inner = .lam false ownerTy body →
      OwnedReadLend g root owner refTy length index proof resultTy ownerTy body

inductive Eval (g : Graph.Graph) : Env → Nat → State → Value → List Event → State → Prop where
  | scalar : Graph.nodeAt g root = .integer v → Eval g env root s (.scalar v) [] s
  | natural : Graph.nodeAt g root = .natural n → Eval g env root s (.nat n) [] s
  | var : Graph.nodeAt g root = .var k → env[k]? = some value → Eval g env root s value [] s
  | app : Graph.nodeAt g root = .app function argument →
      Graph.nodeAt g function = .lam false domain body →
      Eval g env argument s computed before middle →
      Eval g (computed :: env) body middle value after t →
      Eval g env root s value (before ++ after)
        t
  | allocate : Graph.nodeAt g root = .alloc length init →
      DependentBufferIndices.Eval g (runtimeNats env) length n → Scalar g env init v →
      Eval g env root s (.owner s.heap.nextObject)
        [.alloc s.heap.nextObject n v] (SizedBufferHeap.allocate s n v)
  | free : Graph.nodeAt g root = .free owner body → Graph.nodeAt g owner = .var k →
      env[k]? = some (.owner x) →
      Eval g env body (SizedBufferHeap.release s x) value events t →
      Eval g env root s value (.free x :: events) t
  | yes : Graph.nodeAt g root = .ifLt left right yes no →
      DependentBufferIndices.Eval g (runtimeNats env) left a →
      DependentBufferIndices.Eval g (runtimeNats env) right b → a < b →
      Eval g (.ghost :: env) yes s value events t → Eval g env root s value events t
  | no : Graph.nodeAt g root = .ifLt left right yes no →
      DependentBufferIndices.Eval g (runtimeNats env) left a →
      DependentBufferIndices.Eval g (runtimeNats env) right b → ¬ a < b →
      Eval g env no s value events t → Eval g env root s value events t
  | lend : ReadLend g root owner refTy index proof ownerTy body →
      Graph.nodeAt g owner = .var k → env[k]? = some (.owner x) →
      DependentBufferIndices.Eval g (runtimeNats (.borrow x :: env)) index i →
      Eval g (.owner x :: .scalar (s.heap.payload x) :: env) body
        ⟨ScopedLend.restored s.heap, s.length⟩ value suffix t →
      Eval g env root s value
        ([.beginLease s.heap.nextLease x, .read s.heap.nextLease i (s.heap.payload x),
          .close s.heap.nextLease] ++ suffix) t

  | ownedLend : OwnedReadLend g root owner refTy length index proof resultTy ownerTy body →
      Graph.nodeAt g owner = .var k → env[k]? = some (.owner x) →
      DependentBufferIndices.Eval g (runtimeNats (.borrow x :: env)) index i →
      DependentBufferIndices.Eval g (runtimeNats (.borrow x :: env)) length m →
      Eval g (.owner x :: .owner s.heap.nextObject :: env) body
        (SizedOwnedLend.final s m (s.heap.payload x)) value suffix t →
      Eval g env root s value (SizedOwnedLend.events s x i m ++ suffix) t

/-- Every complete execution closes its locally opened leases. This follows
from the runtime rules, independently of a typing plan or safe-trace premise. -/
theorem Eval.lease_frame (run : Eval g env root s value events t) :
    t.heap.lease = s.heap.lease := by
  induction run with
  | scalar _ | natural _ | var _ _ | allocate _ _ _ => rfl
  | app _ _ _ _ first last => exact last.trans first
  | free _ _ _ _ ih => exact ih
  | yes _ _ _ _ _ ih | no _ _ _ _ _ ih => exact ih
  | lend _ _ _ _ _ ih => exact ih
  | ownedLend _ _ _ _ _ _ ih => exact ih

end Jihoo.SizedCoreExecution
