import Jihoo.ScopedLendGraph
import Jihoo.CoreBridgeBetaTyping

/-! Open natural indices retain lexical positions: absent/non-natural runtime
bindings are unavailable, not removed. Buffer/Ref are interpreted outside Raw;
only their U64 index expressions use the existing Raw beta/substitution theory. -/
namespace Jihoo.DependentBufferIndices
open ScopedLend
open CoreBridge (Raw)

abbrev Env := Nat → Option Nat

def push (n : Nat) (env : Env) : Env
  | 0 => some n
  | k+1 => env k

def ValidEnv (env : Env) : Prop := ∀ k n, env k = some n → n < 2^64

inductive Expr where
  | literal (value : Nat)
  | var (slot : Nat)
  | letE (argument body : Expr)
  deriving DecidableEq, Repr

namespace Expr

variable {a b : Expr}

def eval (env : Env) : Expr → Option Nat
  | .literal n => some n
  | .var k => env k
  | .letE arg body => do let n ← arg.eval env; body.eval (push n env)

def rename (ρ : Nat → Nat) : Expr → Expr
  | .literal n => .literal n
  | .var k => .var (ρ k)
  | .letE a b => .letE (a.rename ρ) (b.rename (Indexed.liftRenaming ρ))

def liftSub (σ : Nat → Expr) : Nat → Expr
  | 0 => .var 0
  | k+1 => (σ k).rename Nat.succ

def subst (σ : Nat → Expr) : Expr → Expr
  | .literal n => .literal n
  | .var k => σ k
  | .letE a b => .letE (a.subst σ) (b.subst (liftSub σ))

def single (a : Expr) : Nat → Expr
  | 0 => a
  | k+1 => .var k

def encode : Expr → Raw
  | .literal n => .natural n
  | .var k => .var k
  | .letE a b => .app (.lam false .u64 b.encode) a.encode

theorem eval_rename (e : Expr) (agree : ∀ k, target (ρ k) = source k) :
    (e.rename ρ).eval target = e.eval source := by
  induction e generalizing source target ρ with
  | literal => rfl
  | var k => exact agree k
  | letE a b ia ib =>
      simp only [rename, eval, ia agree]
      cases ha : a.eval source with
      | none => rfl
      | some n =>
          apply ib
          intro k; cases k <;> simp [Indexed.liftRenaming, push, agree]

theorem eval_subst (e : Expr) (agree : ∀ k, (σ k).eval target = source k) :
    (e.subst σ).eval target = e.eval source := by
  induction e generalizing source target σ with
  | literal => rfl
  | var k => exact agree k
  | letE a b ia ib =>
      simp only [subst, eval, ia agree]
      cases ha : a.eval source with
      | none => rfl
      | some n =>
          apply ib
          intro k; cases k with
          | zero => rfl
          | succ k => exact (eval_rename (σ k) (by intro j; rfl)).trans (agree k)

theorem eval_beta (argument : a.eval env = some n) :
    (b.subst (single a)).eval env = b.eval (push n env) := by
  apply eval_subst
  intro k; cases k with
  | zero => exact argument
  | succ k => rfl

theorem encode_rename (e : Expr) : (e.rename ρ).encode = e.encode.rename ρ := by
  induction e generalizing ρ with
  | literal | var => simp [rename, encode, Raw.rename]
  | letE a b ia ib => simp only [rename, encode, Raw.rename, ia, ib]

theorem encode_subst (e : Expr) : (e.subst σ).encode = e.encode.subst (fun k => (σ k).encode) := by
  induction e generalizing σ with
  | literal | var => simp [subst, encode, Raw.subst]
  | letE a b ia ib =>
      simp only [subst, encode, Raw.subst, ia, ib]
      congr 2
      apply congrArg (fun σ => Raw.subst σ b.encode)
      funext k; cases k <;> simp [liftSub, Raw.liftSub, encode, encode_rename]

theorem encode_beta :
    (b.subst (single a)).encode = b.encode.subst (Raw.single a.encode) := by
  rw [encode_subst]
  congr 1
  funext k; cases k <;> rfl

/-- Reuse the existing declarative U64 substitution theorem, not a new
postulated Buffer typing rule. -/
theorem raw_beta_typing (body : Raw.Beta.HasType (Γ.extend .u64) b.encode .u64)
    (argument : Raw.Beta.HasType Γ a.encode .u64) :
    Raw.Beta.HasType Γ (b.subst (single a)).encode .u64 := by
  rw [encode_beta]
  simpa only [Raw.subst] using Raw.Beta.HasType.instantiate body argument

end Expr

inductive Represents (g : Graph.Graph) : Nat → Expr → Prop where
  | literal : Graph.nodeAt g root = .natural n → n < 2^64 → Represents g root (.literal n)
  | var : Graph.nodeAt g root = .var k → Represents g root (.var k)
  | letE : Graph.nodeAt g root = .app f arg → Graph.nodeAt g f = .lam false ty body →
      Graph.nodeAt g ty = .u64 → Represents g arg a → Represents g body b →
      Represents g root (.letE a b)

/-- Graph evaluation uses a slot-preserving closing environment, never the
compact ownership inventory or the scalar-only inventory. -/
def Eval (g : Graph.Graph) (env : Env) (root n : Nat) : Prop :=
  ∃ e, Represents g root e ∧ e.eval env = some n

theorem Eval.literal (shape : Graph.nodeAt g root = .natural n) (bound : n < 2^64) :
    Eval g env root n := ⟨_, .literal shape bound, rfl⟩

theorem Eval.var (shape : Graph.nodeAt g root = .var k) (value : env k = some n) :
    Eval g env root n := ⟨_, .var shape, value⟩

theorem Eval.letE (shape : Graph.nodeAt g root = .app f arg)
    (lam : Graph.nodeAt g f = .lam false ty body) (u64 : Graph.nodeAt g ty = .u64)
    (argument : Eval g env arg a) (rest : Eval g (push a env) body n) : Eval g env root n := by
  obtain ⟨ea, ra, ha⟩ := argument
  obtain ⟨eb, rb, hb⟩ := rest
  exact ⟨_, .letE shape lam u64 ra rb, by simp [Expr.eval, ha, hb]⟩

theorem Represents.unique (a : Represents g root e) (b : Represents g root e') : e = e' := by
  induction a generalizing e' with
  | literal shape bound =>
      cases b with
      | literal shape' _ => have eq := shape.symm.trans shape'; cases eq; rfl
      | var shape' => have := shape.symm.trans shape'; contradiction
      | letE shape' _ _ _ _ => have := shape.symm.trans shape'; contradiction
  | var shape =>
      cases b with
      | literal shape' _ => have := shape.symm.trans shape'; contradiction
      | var shape' => have eq := shape.symm.trans shape'; cases eq; rfl
      | letE shape' _ _ _ _ => have := shape.symm.trans shape'; contradiction
  | letE shape lam ty a rest ia ib =>
      cases b with
      | literal shape' _ => have := shape.symm.trans shape'; contradiction
      | var shape' => have := shape.symm.trans shape'; contradiction
      | letE shape' lam' _ a' b' =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := lam.symm.trans lam'; cases eq
          obtain rfl := ia a'; obtain rfl := ib b'; rfl

theorem Eval.deterministic (a : Eval g env root n) (b : Eval g env root n') : n = n' := by
  obtain ⟨e, shape, value⟩ := a
  obtain ⟨e', shape', value'⟩ := b
  obtain rfl := shape.unique shape'
  exact Option.some.inj (value.symm.trans value')

theorem valid_push (valid : ValidEnv env) (bound : n < 2^64) : ValidEnv (push n env) := by
  intro k v lookup
  cases k with
  | zero => simp [push] at lookup; subst v; exact bound
  | succ k => exact valid k v lookup

theorem Represents.eval_bound (represented : Represents g root e)
    (valid : ValidEnv env) (value : e.eval env = some n) : n < 2^64 := by
  induction represented generalizing env n with
  | literal shape bound => simp [Expr.eval] at value; subst n; exact bound
  | var shape => exact valid _ _ value
  | @letE rt f arg ty body ea eb shape lam u64 a b ia ib =>
      simp only [Expr.eval] at value
      cases evaluated : Expr.eval env ea with
      | none => simp [evaluated] at value
      | some v =>
          simp [evaluated] at value
          exact ib (valid_push valid (ia valid evaluated)) value

theorem Eval.bound (run : Eval g env root n) (valid : ValidEnv env) : n < 2^64 := by
  obtain ⟨e, represented, value⟩ := run
  exact represented.eval_bound valid value

def extendSlots (slots : Nat → Prop) : Nat → Prop
  | 0 => True
  | k+1 => slots k

inductive Available : (Nat → Prop) → Expr → Prop where
  | literal : Available slots (.literal n)
  | var : slots k → Available slots (.var k)
  | letE : Available slots a → Available (extendSlots slots) b → Available slots (.letE a b)

/-- Natural availability is a static lexical condition. A missing, scalar,
owner or erased proof slot cannot be silently promoted to a natural. -/
theorem Available.total (available : Available slots e)
    (closing : ∀ k, slots k → ∃ n, env k = some n) : ∃ n, e.eval env = some n := by
  induction available generalizing env with
  | literal => exact ⟨_, rfl⟩
  | var present => exact closing _ present
  | @letE slots aExpr bExpr a b ia ib =>
      obtain ⟨n, hn⟩ := ia closing
      have closeBody : ∀ k, extendSlots slots k → ∃ v, push n env k = some v := by
        intro k present
        cases k with
        | zero => exact ⟨n, rfl⟩
        | succ k => exact closing k present
      obtain ⟨v, hv⟩ := ib closeBody
      exact ⟨v, by simp [Expr.eval, hn, hv]⟩

theorem Represents.total (represented : Represents g root e) (available : Available slots e)
    (closing : ∀ k, slots k → ∃ n, env k = some n) : ∃ n, Eval g env root n := by
  obtain ⟨n, value⟩ := available.total closing
  exact ⟨n, e, represented, value⟩

theorem Represents.raw_typed (represented : Represents g root e) (available : Available slots e)
    (types : ∀ k, slots k → Γ k = some Raw.u64) : Raw.Beta.HasType Γ e.encode .u64 := by
  induction represented generalizing Γ slots with
  | literal shape bound => exact .natural bound
  | var shape => cases available with | var present => exact .var (types _ present)
  | letE shape lam u64 arg body ia ib =>
      cases available with
      | letE a b =>
          have bodyTyped : Raw.Beta.HasType (Γ.extend .u64) _ .u64 := ib b (by
            intro k present
            cases k with
            | zero => simp [Raw.Context.extend, Raw.rename]
            | succ k => simp [Raw.Context.extend, types k present, Raw.rename])
          have fn := Raw.Beta.HasType.lam Raw.Beta.IsType.u64 (by rfl) bodyTyped
          simpa [Expr.encode, Raw.subst, Raw.proposition] using Raw.Beta.HasType.app fn (ia a types)

/-- Interpret actual Buffer n and Ref(Buffer n) annotations in the current
lexical environment. No constant-length or closed-index premise is imposed. -/
def BufferLength (g : Graph.Graph) (env : Env) (ty n : Nat) : Prop :=
  ∃ index, Graph.nodeAt g ty = .buffer index ∧ Eval g env index n

def RefLength (g : Graph.Graph) (env : Env) (ty n : Nat) : Prop :=
  ∃ buffer, Graph.nodeAt g ty = .ref buffer ∧ BufferLength g env buffer n

theorem BufferLength.unique (a : BufferLength g env ty n) (b : BufferLength g env ty m) : n = m := by
  obtain ⟨i, shape, run⟩ := a
  obtain ⟨j, shape', run'⟩ := b
  have eq := shape.symm.trans shape'; cases eq
  exact run.deterministic run'

theorem RefLength.unique (a : RefLength g env ty n) (b : RefLength g env ty m) : n = m := by
  obtain ⟨i, shape, run⟩ := a
  obtain ⟨j, shape', run'⟩ := b
  have eq := shape.symm.trans shape'; cases eq
  exact run.unique run'

/-- Logical index substitution between explicitly represented graph roots.
This does not assert correctness of a native graph-rewriting implementation. -/
theorem Eval.substitution (represented : Represents g index e)
    (targetSyntax : Represents targetGraph targetIndex (e.subst σ))
    (run : Eval g source index n)
    (closing : ∀ k, (σ k).eval target = source k) :
    Eval targetGraph target targetIndex n := by
  obtain ⟨actual, actualSyntax, value⟩ := run
  obtain rfl := represented.unique actualSyntax
  exact ⟨_, targetSyntax, (e.eval_subst closing).trans value⟩

/-- The target Buffer annotation contains the substituted index syntax, not
an independently assumed successful target length evaluation. -/
theorem BufferLength.substitution
    (sourceShape : Graph.nodeAt g ty = .buffer index)
    (represented : Represents g index e)
    (targetShape : Graph.nodeAt targetGraph targetTy = .buffer targetIndex)
    (targetSyntax : Represents targetGraph targetIndex (e.subst σ))
    (length : BufferLength g source ty n)
    (closing : ∀ k, (σ k).eval target = source k) :
    BufferLength targetGraph target targetTy n := by
  obtain ⟨actual, shape, run⟩ := length
  have eq := sourceShape.symm.trans shape; cases eq
  exact ⟨targetIndex, targetShape, run.substitution represented targetSyntax closing⟩

/-- Ref(Buffer n) transports the same logically substituted open index while
retaining the actual Ref and Buffer graph annotation structure. -/
theorem RefLength.substitution
    (sourceRef : Graph.nodeAt g refTy = .ref bufferTy)
    (sourceBuffer : Graph.nodeAt g bufferTy = .buffer index)
    (represented : Represents g index e)
    (targetRef : Graph.nodeAt targetGraph targetRefTy = .ref targetBufferTy)
    (targetBuffer : Graph.nodeAt targetGraph targetBufferTy = .buffer targetIndex)
    (targetSyntax : Represents targetGraph targetIndex (e.subst σ))
    (length : RefLength g source refTy n)
    (closing : ∀ k, (σ k).eval target = source k) :
    RefLength targetGraph target targetRefTy n := by
  obtain ⟨actual, shape, run⟩ := length
  have eq := sourceRef.symm.trans shape; cases eq
  exact ⟨targetBufferTy, targetRef,
    run.substitution sourceBuffer represented targetBuffer targetSyntax closing⟩

structure BoundFact where
  index : Nat
  length : Nat
  valid : index < length
abbrev ProofEnv := Nat → Option BoundFact

/-- Closed Decide follows the compiler's literal-bound rule. Open comparisons
use a lexical ghost witness introduced by a successful IfLt branch instead. -/
inductive BoundEvidence (g : Graph.Graph) (proofs : ProofEnv) : Nat → Nat → Nat → Prop where
  | decide : Graph.nodeAt g proof = .decide left right →
      Graph.nodeAt g left = .natural i → Graph.nodeAt g right = .natural n →
      i < 2^64 → n < 2^64 → decide (i < n) = true → BoundEvidence g proofs proof i n
  | var : Graph.nodeAt g proof = .var k → proofs k = some fact →
      BoundEvidence g proofs proof fact.index fact.length

theorem BoundEvidence.sound (h : BoundEvidence g proofs proof i n) : i < n := by
  cases h with
  | decide _ _ _ _ _ truth => exact of_decide_eq_true truth
  | var _ _ => exact BoundFact.valid _

/-- Both the array length and runtime index are evaluated; the ghost witness
must match those concrete values, so an unrelated less-than fact is useless. -/
def CheckedIndex (g : Graph.Graph) (env : Env) (proofs : ProofEnv)
    (index length proof i n : Nat) : Prop :=
  Eval g env index i ∧ Eval g env length n ∧ BoundEvidence g proofs proof i n

theorem CheckedIndex.safe (checked : CheckedIndex g env proofs index length proof i n) : i < n :=
  checked.2.2.sound

theorem CheckedIndex.nonempty (checked : CheckedIndex g env proofs index length proof i n) : 0 < n := by
  have := checked.safe; omega

theorem zero_length_no_read : ¬ CheckedIndex g env proofs index length proof i 0 := by
  intro checked; have := checked.safe; omega

theorem Expr.eval_transport (e : Expr) (value : e.eval source = some n)
    (agree : ∀ k v, source k = some v → target k = some v) : e.eval target = some n := by
  induction e generalizing source target n with
  | literal v => exact value
  | var k => exact agree k n value
  | letE a b ia ib =>
      simp only [Expr.eval] at value ⊢
      cases ha : a.eval source with
      | none => simp [ha] at value
      | some v =>
          have hb : b.eval (push v source) = some n := by simpa [ha] using value
          rw [ia ha agree]
          apply ib hb
          intro k w lookup
          cases k with
          | zero => exact lookup
          | succ k => exact agree k w lookup

theorem Eval.transport (run : Eval g source root n)
    (agree : ∀ k v, source k = some v → target k = some v) : Eval g target root n := by
  obtain ⟨e, shape, value⟩ := run
  exact ⟨e, shape, e.eval_transport value agree⟩

theorem Eval.congr (run : Eval g env root n) (equal : ∀ k, env k = env' k) : Eval g env' root n := by
  have eq : env = env' := funext equal
  subst env'; exact run

theorem BufferLength.congr (run : BufferLength g env ty n) (equal : ∀ k, env k = env' k) :
    BufferLength g env' ty n := by
  obtain ⟨index, shape, value⟩ := run
  exact ⟨index, shape, value.congr equal⟩

def unavailable (env : Env) : Env
  | 0 => none
  | k+1 => env k

theorem shifted_index (e : Expr) : (e.rename Nat.succ).eval (unavailable env) = e.eval env :=
  e.eval_rename (by intro k; rfl)

theorem unavailable_zero : unavailable env 0 = none := rfl

theorem unavailable_succ : unavailable env (k+1) = env k := rfl

end Jihoo.DependentBufferIndices
