import Jihoo.SymbolicCoreContext
import Jihoo.SizedCoreTyping

/-! Value-independent, constructor-driven typing for a dependent Buffer rule
family on the original Core graph. Both comparison arms are checked. The
closing theorem connects this judgment to the existing ownership semantics;
no successful evaluation or safe event trace is a typing premise. -/
namespace Jihoo.SymbolicCoreTyping
open ScopedLend SymbolicCoreContext
open DependentBufferIndices (Expr Represents Available)

/-- An actual graph expression has a syntactic U64 derivation in the current
lexical context. Availability excludes owners, scalar, erased and dead slots. -/
structure Index (g : Graph.Graph) (ctx : Context) (root : Nat) (e : Expr) : Prop where
  represents : Represents g root e
  available : Available (natSlots ctx) e

inductive Scalar (g : Graph.Graph) (ctx : Context) : Nat → Prop where
  | literal : Graph.nodeAt g root = .integer v → v < 2^63 → Scalar g ctx root
  | var : Graph.nodeAt g root = .var k → ctx[k]? = some .scalar → Scalar g ctx root

def BufferType (g : Graph.Graph) (ctx : Context) (root : Nat) (e : Expr) : Prop :=
  ∃ indexRoot, Graph.nodeAt g root = .buffer indexRoot ∧ Index g ctx indexRoot e

def RefType (g : Graph.Graph) (ctx : Context) (root : Nat) (e : Expr) : Prop :=
  ∃ bufferRoot, Graph.nodeAt g root = .ref bufferRoot ∧ BufferType g ctx bufferRoot e

/-- A lexical proof must name the exact symbolic index and length. Its truth
comes from the branch hypothesis when the context is interpreted. -/
inductive Evidence (g : Graph.Graph) (ctx : Context) : Nat → Expr → Expr → Prop where
  | decide : Graph.nodeAt g proof = .decide left right →
      Graph.nodeAt g left = .natural i → Graph.nodeAt g right = .natural n →
      i < 2^64 → n < 2^64 → decide (i < n) = true →
      Evidence g ctx proof (.literal i) (.literal n)
  | var : Graph.nodeAt g proof = .var k → ctx[k]? = some (.bound i n) →
      Evidence g ctx proof i n

/-- Every resource length and result type is in the CURRENT lexical scope.
Binding shifts them even when the new binder is erased or non-natural. The
natural application rule substitutes its actual argument into the result. -/
inductive Typing (g : Graph.Graph) : Context → Sizes → Nat → Result → Prop where
  | literal : Graph.nodeAt g root = .integer v → v < 2^63 →
      Typing g ctx [] root .scalar
  | scalar : Graph.nodeAt g root = .var k → ctx[k]? = some .scalar →
      Typing g ctx [] root .scalar
  | owner : Graph.nodeAt g root = .var k → ctx[k]? = some (.owner 0) →
      Typing g ctx [n] root (.owner n)
  | ownedLet : Graph.nodeAt g root = .app function argument →
      Graph.nodeAt g function = .lam false domain body →
      Graph.nodeAt g argument = .var k → ctx[k]? = some (.owner slot) →
      sizes[slot]? = some n → BufferType g ctx domain n →
      Typing g (transferred ctx slot) (sizes.map shift) body (kind.rename Nat.succ) →
      Typing g ctx sizes root kind
  | naturalLet : Graph.nodeAt g root = .app function argument →
      Graph.nodeAt g function = .lam false domain body → Graph.nodeAt g domain = .u64 →
      Index g ctx argument a →
      Typing g (push .nat ctx) (sizes.map shift) body bodyKind →
      Typing g ctx sizes root (bodyKind.subst (Expr.single a))
  | allocate : Graph.nodeAt g root = .app function argument →
      Graph.nodeAt g function = .lam false domain body → BufferType g ctx domain n →
      Graph.nodeAt g argument = .alloc length init → Index g ctx length n → Scalar g ctx init →
      Typing g (fresh ctx) ((n :: sizes).map shift) body (kind.rename Nat.succ) →
      Typing g ctx sizes root kind
  | allocation : Graph.nodeAt g root = .alloc length init → Index g ctx length n → Scalar g ctx init →
      Typing g ctx [] root (.owner n)
  | free : Graph.nodeAt g root = .free owner body → Graph.nodeAt g owner = .var k →
      ctx[k]? = some (.owner slot) → slot < sizes.length →
      Typing g (consumed slot ctx) (sizes.eraseIdx slot) body kind →
      Typing g ctx sizes root kind
  | branch : Graph.nodeAt g root = .ifLt left right yes no →
      Index g ctx left a → Index g ctx right b →
      Typing g (push (.bound a b) ctx) (sizes.map shift) yes (kind.rename Nat.succ) →
      Typing g ctx sizes no kind → Typing g ctx sizes root kind
  | lend : SizedCoreExecution.ReadLend g root owner refTy index proof ownerTy body →
      Graph.nodeAt g owner = .var k → ctx[k]? = some (.owner slot) → sizes[slot]? = some n →
      RefType g ctx refTy n → BufferType g (push .scalar ctx) ownerTy (shift n) →
      Index g (push .dead ctx) index (shift i) →
      Evidence g (push .dead ctx) proof (shift i) (shift n) →
      Typing g (scalarReturned ctx slot) (sizes.map (fun e => shift (shift e))) body
        ((kind.rename Nat.succ).rename Nat.succ) → Typing g ctx sizes root kind

end Jihoo.SymbolicCoreTyping
