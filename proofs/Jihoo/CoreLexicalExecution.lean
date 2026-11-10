import Jihoo.CoreLexicalContext
import Jihoo.OwnedCoreApplications

/-! A direct lexical execution relation for the supported original Core graph.
No resource plan, capability-slot inventory, static role context, or typing
certificate is an argument of Eval. Old lexical values remain present after
moves/free; typing, rather than runtime tombstones, prevents their reuse.
The direct-lambda/Buffer1 reader grammar and mathematical heap are retained.
This is an intermediate Core semantics, not native pointer/LLVM execution. -/
namespace Jihoo.CoreLexicalExecution
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedCoreContinuation
open CoreLexicalContext (Value Env)

def resultValue : ResultKind → Nat → Value
  | .scalar, n => .scalar n
  | .owned, x => .owner x

theorem resultValue_injective (eq : resultValue kind a = resultValue kind b) : a = b := by
  cases kind <;> cases eq <;> rfl

/-- A reference names the dynamically borrowed object. Explicit Borrow(owner)
uses the same concrete object identity, never an arbitrary equal-payload owner. -/
inductive BorrowOperand (g : Graph.Graph) (env : Env) (root owner : Nat) : Prop where
  | reference : Graph.nodeAt g root = .var k → env[k]? = some (.borrow owner) → BorrowOperand g env root owner
  | borrowed : Graph.nodeAt g root = .borrow ownerNode → Graph.nodeAt g ownerNode = .var k →
      env[k]? = some (.owner owner) → BorrowOperand g env root owner

/-- The token/owner parameters are the currently active dynamic reader lease.
They are not an ownership partition or a static lexical role classification. -/
inductive Reads (g : Graph.Graph) (token owner : Nat) : Env → Nat → State → Nat → List Event → Prop where
  | scalar : Graph.nodeAt g root = .integer value → Reads g token owner env root s value []
  | read : Graph.nodeAt g root = .index operand index proof →
      BorrowOperand g env operand owner → Graph.boundZero g index proof = true →
      Reads g token owner env root s (s.payload owner) [.read token (s.payload owner)]
  | strict : Graph.nodeAt g root = .strict first second →
      Reads g token owner env first s a before → Reads g token owner env second s value after →
      Reads g token owner env root s value (before ++ after)
  | app : Graph.nodeAt g root = .app function argument →
      Graph.nodeAt g function = .lam false domain body → Graph.nodeAt g domain = .i64 →
      Reads g token owner env argument s a before →
      Reads g token owner (.scalar a :: env) body s value after →
      Reads g token owner env root s value (before ++ after)
  | yes : Graph.nodeAt g root = .ifLt left right yes no →
      Graph.nodeAt g left = .natural a → Graph.nodeAt g right = .natural b → a < b →
      Reads g token owner (.dead :: env) yes s value events →
      Reads g token owner env root s value events
  | no : Graph.nodeAt g root = .ifLt left right yes no →
      Graph.nodeAt g left = .natural a → Graph.nodeAt g right = .natural b → ¬ a < b →
      Reads g token owner env no s value events →
      Reads g token owner env root s value events

/-- Only the actual lexical environment is threaded through the Core. Applying
an immediate lambda evaluates its argument, then prepends exactly that value. -/
inductive Eval (g : Graph.Graph) : Env → Nat → State → Value → List Event → State → Prop where
  | scalar : Graph.nodeAt g root = .integer value → Eval g env root s (.scalar value) [] s
  | var : Graph.nodeAt g root = .var k → env[k]? = some value → Eval g env root s value [] s
  | allocate : Graph.nodeAt g root = .alloc length init → Graph.nodeAt g length = .natural 1 →
      Graph.nodeAt g init = .integer value →
      Eval g env root s (.owner s.nextObject) [.alloc s.nextObject value] (allocatedState s value)
  | app : Graph.nodeAt g root = .app function argument →
      Graph.nodeAt g function = .lam false domain body →
      Eval g env argument s computed before middle →
      Eval g (computed :: env) body middle value after t →
      Eval g env root s value (before ++ after) t
  | free : Graph.nodeAt g root = .free owner body → Graph.nodeAt g owner = .var k →
      env[k]? = some (.owner x) → Eval g env body (freedState s x) value events t →
      Eval g env root s value (.free x :: events) t
  | lend : OwnedLendContext.Shape g root owner init body → Graph.nodeAt g owner = .var k →
      env[k]? = some (.owner x) →
      Reads g s.nextLease x (.borrow x :: env) init (opened s x) copied reads →
      Eval g (.owner x :: .owner s.nextObject :: env) body (OwnedLendTransfer.final s copied) value suffix t →
      Eval g env root s value (OwnedLendTransfer.events s x copied reads ++ suffix) t
  | scalarLend : ScalarShape g root owner init body → Graph.nodeAt g owner = .var k →
      env[k]? = some (.owner x) →
      Reads g s.nextLease x (.borrow x :: env) init (opened s x) copied reads →
      Eval g (.owner x :: .scalar copied :: env) body (restored s) value suffix t →
      Eval g env root s value (scalarEvents s x reads ++ suffix) t

theorem Reads.deterministic (a : Reads g token owner env root s v es)
    (b : Reads g token owner env root s v' es') : v = v' ∧ es = es' := by
  induction a generalizing v' es' with
  | scalar shape =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; cases eq
          exact ⟨rfl, rfl⟩
      | read shape' operand' bound' =>
          have eq := shape.symm.trans shape'; contradiction
      | strict shape' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' domain' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' left' right' bound' branch' =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' left' right' bound' branch' =>
          have eq := shape.symm.trans shape'; contradiction
  | read shape operand bound =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | read shape' operand' bound' =>
          have eq := shape.symm.trans shape'; cases eq
          exact ⟨rfl, rfl⟩
      | strict shape' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' domain' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' left' right' bound' branch' =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' left' right' bound' branch' =>
          have eq := shape.symm.trans shape'; contradiction
  | strict shape first second ihf ihs =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | read shape' operand' bound' =>
          have eq := shape.symm.trans shape'; contradiction
      | strict shape' first' second' =>
          have eq := shape.symm.trans shape'; cases eq
          obtain ⟨rfl, rfl⟩ := ihf first'
          obtain ⟨rfl, rfl⟩ := ihs second'
          exact ⟨rfl, rfl⟩
      | app shape' function' domain' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' left' right' bound' branch' =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' left' right' bound' branch' =>
          have eq := shape.symm.trans shape'; contradiction
  | app shape function domain first second ihf ihs =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | read shape' operand' bound' =>
          have eq := shape.symm.trans shape'; contradiction
      | strict shape' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' domain' first' second' =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := function.symm.trans function'; cases eq
          obtain ⟨rfl, rfl⟩ := ihf first'
          obtain ⟨rfl, rfl⟩ := ihs second'
          exact ⟨rfl, rfl⟩
      | yes shape' left' right' bound' branch' =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' left' right' bound' branch' =>
          have eq := shape.symm.trans shape'; contradiction
  | yes shape left right bound branch ih =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | read shape' operand' bound' =>
          have eq := shape.symm.trans shape'; contradiction
      | strict shape' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' domain' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' left' right' bound' branch' =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := left.symm.trans left'; cases eq
          have eq := right.symm.trans right'; cases eq
          exact ih branch'
      | no shape' left' right' bound' branch' =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := left.symm.trans left'; cases eq
          have eq := right.symm.trans right'; cases eq
          omega
  | no shape left right bound branch ih =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | read shape' operand' bound' =>
          have eq := shape.symm.trans shape'; contradiction
      | strict shape' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' domain' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' left' right' bound' branch' =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := left.symm.trans left'; cases eq
          have eq := right.symm.trans right'; cases eq
          omega
      | no shape' left' right' bound' branch' =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := left.symm.trans left'; cases eq
          have eq := right.symm.trans right'; cases eq
          exact ih branch'

/-- Determinism of concrete lexical execution is independent of any resource
plan or typing derivation, including concrete allocation and lease identities. -/
theorem Eval.deterministic (a : Eval g env root s v es t)
    (b : Eval g env root s v' es' t') : v = v' ∧ es = es' ∧ t = t' := by
  induction a generalizing v' es' t' with
  | scalar shape =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; cases eq
          exact ⟨rfl, rfl, rfl⟩
      | var shape' lookup' =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' length' init' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' variableShape' lookup' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' variableShape' lookup' read' suffix' =>
          obtain ⟨_, _, otherHead⟩ := shape'.head
          have eq := shape.symm.trans otherHead; contradiction
      | scalarLend shape' variableShape' lookup' read' suffix' =>
          obtain ⟨_, _, otherHead⟩ := shape'.head
          have eq := shape.symm.trans otherHead; contradiction
  | var shape lookup =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup' =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := lookup.symm.trans lookup'; cases eq
          exact ⟨rfl, rfl, rfl⟩
      | allocate shape' length' init' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' variableShape' lookup' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' variableShape' lookup' read' suffix' =>
          obtain ⟨_, _, otherHead⟩ := shape'.head
          have eq := shape.symm.trans otherHead; contradiction
      | scalarLend shape' variableShape' lookup' read' suffix' =>
          obtain ⟨_, _, otherHead⟩ := shape'.head
          have eq := shape.symm.trans otherHead; contradiction
  | allocate shape length init =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup' =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' length' init' =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := init.symm.trans init'; cases eq
          exact ⟨rfl, rfl, rfl⟩
      | app shape' function' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' variableShape' lookup' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' variableShape' lookup' read' suffix' =>
          obtain ⟨_, _, otherHead⟩ := shape'.head
          have eq := shape.symm.trans otherHead; contradiction
      | scalarLend shape' variableShape' lookup' read' suffix' =>
          obtain ⟨_, _, otherHead⟩ := shape'.head
          have eq := shape.symm.trans otherHead; contradiction
  | app shape function first second ihf ihs =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup' =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' length' init' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' first' second' =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := function.symm.trans function'; cases eq
          obtain ⟨rfl, rfl, rfl⟩ := ihf first'
          obtain ⟨rfl, rfl, rfl⟩ := ihs second'
          exact ⟨rfl, rfl, rfl⟩
      | free shape' variableShape' lookup' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' variableShape' lookup' read' suffix' =>
          obtain ⟨_, _, otherHead⟩ := shape'.head
          have eq := shape.symm.trans otherHead; contradiction
      | scalarLend shape' variableShape' lookup' read' suffix' =>
          obtain ⟨_, _, otherHead⟩ := shape'.head
          have eq := shape.symm.trans otherHead; contradiction
  | free shape variableShape lookup suffix ih =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup' =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' length' init' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' variableShape' lookup' suffix' =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := variableShape.symm.trans variableShape'; cases eq
          have eq := lookup.symm.trans lookup'; cases eq
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩
      | lend shape' variableShape' lookup' read' suffix' =>
          obtain ⟨_, _, otherHead⟩ := shape'.head
          have eq := shape.symm.trans otherHead; contradiction
      | scalarLend shape' variableShape' lookup' read' suffix' =>
          obtain ⟨_, _, otherHead⟩ := shape'.head
          have eq := shape.symm.trans otherHead; contradiction
  | lend shape variableShape lookup read suffix ih =>
      obtain ⟨_, _, head⟩ := shape.head
      cases b with
      | scalar shape' =>
          have eq := head.symm.trans shape'; contradiction
      | var shape' lookup' =>
          have eq := head.symm.trans shape'; contradiction
      | allocate shape' length' init' =>
          have eq := head.symm.trans shape'; contradiction
      | app shape' function' first' second' =>
          have eq := head.symm.trans shape'; contradiction
      | free shape' variableShape' lookup' suffix' =>
          have eq := head.symm.trans shape'; contradiction
      | lend shape' variableShape' lookup' read' suffix' =>
          obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := variableShape.symm.trans variableShape'; cases eq
          have eq := lookup.symm.trans lookup'; cases eq
          obtain ⟨rfl, rfl⟩ := read.deterministic read'
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩
      | scalarLend shape' variableShape' lookup' read' suffix' =>
          exact False.elim (shape'.not_owned shape)
  | scalarLend shape variableShape lookup read suffix ih =>
      obtain ⟨_, _, head⟩ := shape.head
      cases b with
      | scalar shape' =>
          have eq := head.symm.trans shape'; contradiction
      | var shape' lookup' =>
          have eq := head.symm.trans shape'; contradiction
      | allocate shape' length' init' =>
          have eq := head.symm.trans shape'; contradiction
      | app shape' function' first' second' =>
          have eq := head.symm.trans shape'; contradiction
      | free shape' variableShape' lookup' suffix' =>
          have eq := head.symm.trans shape'; contradiction
      | lend shape' variableShape' lookup' read' suffix' =>
          exact False.elim (shape.not_owned shape')
      | scalarLend shape' variableShape' lookup' read' suffix' =>
          obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := variableShape.symm.trans variableShape'; cases eq
          have eq := lookup.symm.trans lookup'; cases eq
          obtain ⟨rfl, rfl⟩ := read.deterministic read'
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩

end Jihoo.CoreLexicalExecution
