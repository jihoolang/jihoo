import Jihoo.SizedCoreExecution
import Jihoo.SizedCorePure

/-! A semantic closing-instance typing judgment for the original sized Core
fragment. Natural parameters and erased Lt assumptions are interpreted in the
context; owner capability slots carry a separate exact length inventory.
This is not the executable Core checker, nor general dependent Pi preservation. -/
namespace Jihoo.SizedCoreTyping
open ScopedLend SizedBufferContext SizedCoreExecution
open DependentBufferIndices (BufferLength RefLength BoundEvidence)

inductive Result where
  | scalar
  | owner (length : Nat)
  deriving DecidableEq, Repr

inductive ScalarTyped (g : Graph.Graph) (ctx : Context) : Nat → Prop where
  | literal : Graph.nodeAt g root = .integer v → v < 2^63 → ScalarTyped g ctx root
  | var : Graph.nodeAt g root = .var k → ctx[k]? = some .scalar → ScalarTyped g ctx root

inductive Typing (g : Graph.Graph) : Context → List Nat → Nat → Result → Prop where
  | literal : Graph.nodeAt g root = .integer v → v < 2^63 → Typing g ctx [] root .scalar
  | scalar : Graph.nodeAt g root = .var k → ctx[k]? = some .scalar → Typing g ctx [] root .scalar
  | owner : Graph.nodeAt g root = .var k → ctx[k]? = some (.owner 0) →
      Typing g ctx [n] root (.owner n)
  | naturalLet : Graph.nodeAt g root = .app function argument →
      Graph.nodeAt g function = .lam false domain body → Graph.nodeAt g domain = .u64 →
      DependentBufferIndices.Eval g (naturalEnv ctx) argument n →
      Typing g (.nat n :: ctx) sizes body kind → Typing g ctx sizes root kind
  | allocate : Graph.nodeAt g root = .app function argument →
      Graph.nodeAt g function = .lam false domain body → BufferLength g (naturalEnv ctx) domain n →
      Graph.nodeAt g argument = .alloc length init →
      DependentBufferIndices.Eval g (naturalEnv ctx) length n → ScalarTyped g ctx init →
      Typing g (fresh ctx) (n :: sizes) body kind → Typing g ctx sizes root kind
  | allocation : Graph.nodeAt g root = .alloc length init →
      DependentBufferIndices.Eval g (naturalEnv ctx) length n → ScalarTyped g ctx init →
      Typing g ctx [] root (.owner n)
  | free : Graph.nodeAt g root = .free owner body → Graph.nodeAt g owner = .var k →
      ctx[k]? = some (.owner slot) → slot < sizes.length →
      Typing g (consumed slot ctx) (sizes.eraseIdx slot) body kind → Typing g ctx sizes root kind
  | branch : Graph.nodeAt g root = .ifLt left right yes no →
      DependentBufferIndices.Eval g (naturalEnv ctx) left a →
      DependentBufferIndices.Eval g (naturalEnv ctx) right b →
      (∀ h : a < b, Typing g (.bound ⟨a,b,h⟩ :: ctx) sizes yes kind) →
      (¬ a < b → Typing g ctx sizes no kind) → Typing g ctx sizes root kind
  | lend : ReadLend g root owner refTy index proof ownerTy body →
      Graph.nodeAt g owner = .var k → ctx[k]? = some (.owner slot) → sizes[slot]? = some n →
      RefLength g (naturalEnv ctx) refTy n →
      BufferLength g (naturalEnv (.scalar :: ctx)) ownerTy n →
      DependentBufferIndices.Eval g (naturalEnv (.dead :: ctx)) index i →
      BoundEvidence g (proofs (.dead :: ctx)) proof i n →
      Typing g (scalarReturned ctx slot) sizes body kind → Typing g ctx sizes root kind

end Jihoo.SizedCoreTyping
