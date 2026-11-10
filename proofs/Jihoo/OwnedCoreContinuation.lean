import Jihoo.OwnedScalarContext
import Jihoo.PureOwnedScalar
import Jihoo.OwnedArgumentBinding

/-! Declarative ownership and scalar-binding rules on original Core graph
nodes. Scalar and owned returns, free, allocation, actual pure scalar lets,
linear owned-argument bindings and both scalar/owned-result Lends share one
result-indexed judgment and execution relation. Typed/Runs retain the scalar
specialization; OwnedTyped/OwnedRuns retain the single returned capability.
Owner and scalar environments
are distinct; no accepted-callee or safe-trace premise is assumed. Numeric reader
bounds need a separate heap/literal invariant: this module alone does not claim
full I64/dependent typing or whole-Core semantics. -/
namespace Jihoo.OwnedCoreContinuation
open HeapLeases ScopedLend LinearHeapPrograms
open OwnedScalarContext
abbrev Shape := OwnedLendContext.Shape

inductive Allocation (g : Graph.Graph) (root value body : Nat) : Prop where
  | intro (function argument domain length payload : Nat) :
      Graph.nodeAt g root = .app function argument →
      Graph.nodeAt g function = .lam false domain body →
      Graph.bufferOne g domain = true →
      Graph.nodeAt g argument = .alloc length payload →
      Graph.nodeAt g length = .natural 1 →
      Graph.nodeAt g payload = .integer value → Allocation g root value body

theorem Allocation.unique (a : Allocation g root v b) (a' : Allocation g root v' b') :
    v = v' ∧ b = b' := by
  obtain ⟨f, arg, d, l, p, h, hf, hd, ha, hl, hp⟩ := a
  obtain ⟨f', arg', d', l', p', h', hf', hd', ha', hl', hp'⟩ := a'
  have eq := h.symm.trans h'; cases eq
  have eq := hf.symm.trans hf'; cases eq
  have eq := ha.symm.trans ha'; cases eq
  have eq := hp.symm.trans hp'; cases eq
  exact ⟨rfl, rfl⟩

theorem Allocation.not_pure (a : Allocation g root v body)
    (p : PureOwnedScalar.Shape g root arg rest) : False := by
  cases a with
  | intro f x domain len payload app lam buf _ _ _ =>
      cases p with
      | intro f' domain' app' lam' i64 =>
          have eq := app.symm.trans app'; cases eq
          have eq := lam.symm.trans lam'; cases eq
          simp [Graph.bufferOne, i64] at buf

theorem Allocation.not_owned_binding (a : Allocation g root v body)
    (shape : OwnedArgumentBinding.Shape g root arg rest)
    (resolved : ownerSlot g ctx arg = some slot) : False := by
  cases a with
  | intro f x domain len payload app lam buf alloc _ _ =>
      cases shape with
      | intro f' domain' app' lam' buf' =>
          have eq := app.symm.trans app'; cases eq
          simp [ownerSlot, ScalarCoreCallers.ownerSlot, alloc] at resolved

theorem Allocation.not_variable_argument (a : Allocation g root v body)
    (shape : OwnedArgumentBinding.Shape g root arg rest)
    (variableShape : Graph.nodeAt g arg = .var k) : False := by
  cases a with
  | intro f x domain len payload app lam buf alloc _ _ =>
      cases shape with
      | intro f' domain' app' lam' buf' =>
          have eq := app.symm.trans app'; cases eq
          have eq := alloc.symm.trans variableShape
          contradiction

abbrev LiteralBound := OwnedScalarContext.LiteralBound

inductive ResultKind where
  | scalar
  | owned
  deriving DecidableEq, Repr

inductive Types (g : Graph.Graph) : ResultKind → Context → Nat → Nat → Nat → Prop where
  | finish : resultAt g ctx root = some result → result.check m = true → LiteralBound result → Types g .scalar ctx 0 m root
  | returnOwner : ownerSlot g ctx root = some 0 → Types g .owned ctx 1 m root
  | free : Graph.nodeAt g root = .free owner body → ownerSlot g ctx owner = some slot →
      slot < n → Types g kind (consumed slot ctx) (n - 1) m body → Types g kind ctx n m root
  | allocate : Allocation g root value body → value < 2^63 →
      Types g kind (fresh ctx) (n + 1) m body → Types g kind ctx n m root

  | lend : Shape g root owner init body → ownerSlot g ctx owner = some slot → slot < n →
      Graph.Represents g (readerRoles ctx slot) init reader →
      Types g kind (ownedReturned ctx slot) (n + 1) m body → Types g kind ctx n m root

  | scalarLend : ScalarShape g root owner init body → ownerSlot g ctx owner = some slot → slot < n →
      Graph.Represents g (readerRoles ctx slot) init reader →
      Types g kind (scalarReturned ctx slot) n (m + 1) body → Types g kind ctx n m root

  | scalarLet : PureOwnedScalar.Shape g root arg body →
      PureOwnedScalar.Represents g ctx m arg raw →
      Types g kind (PureOwnedScalar.bindScalar ctx) n (m + 1) body → Types g kind ctx n m root

  | ownedLet : OwnedArgumentBinding.Shape g root argument body →
      ownerSlot g ctx argument = some slot → slot < n →
      Types g kind (OwnedArgumentBinding.transferred ctx slot) n m body → Types g kind ctx n m root

abbrev Typed (g : Graph.Graph) := Types g .scalar
abbrev OwnedTyped (g : Graph.Graph) := Types g .owned

def freedState (s : State) (x : Nat) : State := { s with live := put s.live x false }

inductive Exec (g : Graph.Graph) : ResultKind → Context → Nat → List Nat → List Nat → State → Nat → List Event → State → Prop where
  | finish : resultAt g ctx root = some result → result.eval values = some value → Exec g .scalar ctx root owners values s value [] s
  | returnOwner : ownerSlot g ctx root = some slot → Select owners slot x rest →
      Exec g .owned ctx root owners values s x [] s
  | free : Graph.nodeAt g root = .free owner body → ownerSlot g ctx owner = some slot →
      Select owners slot x rest → Exec g kind (consumed slot ctx) body rest values (freedState s x) value events t →
      Exec g kind ctx root owners values s value (.free x :: events) t
  | allocate : Allocation g root payload body →
      Exec g kind (fresh ctx) body (s.nextObject :: owners) values (allocatedState s payload) value events t →
      Exec g kind ctx root owners values s value (.alloc s.nextObject payload :: events) t

  | lend : Shape g root owner init body → ownerSlot g ctx owner = some slot →
      Select owners slot x rest →
      Graph.CoreReads g (opened s x) s.nextLease x (readerRoles ctx slot) init copied reads →
      Exec g kind (ownedReturned ctx slot) body (s.nextObject :: owners) values
        (OwnedLendTransfer.final s copied) value suffix t →
      Exec g kind ctx root owners values s value (OwnedLendTransfer.events s x copied reads ++ suffix) t

  | scalarLend : ScalarShape g root owner init body → ownerSlot g ctx owner = some slot →
      Select owners slot x rest →
      Graph.CoreReads g (opened s x) s.nextLease x (readerRoles ctx slot) init copied reads →
      Exec g kind (scalarReturned ctx slot) body owners (copied :: values)
        (restored s) value suffix t →
      Exec g kind ctx root owners values s value (scalarEvents s x reads ++ suffix) t

  | scalarLet : PureOwnedScalar.Shape g root arg body →
      PureOwnedScalar.Eval g ctx arg values computed →
      Exec g kind (PureOwnedScalar.bindScalar ctx) body owners (computed :: values) s value events t →
      Exec g kind ctx root owners values s value events t

  | ownedLet : OwnedArgumentBinding.Shape g root argument body →
      ownerSlot g ctx argument = some slot → Select owners slot x rest →
      Exec g kind (OwnedArgumentBinding.transferred ctx slot) body owners values s value events t →
      Exec g kind ctx root owners values s value events t

abbrev Runs (g : Graph.Graph) := Exec g .scalar
abbrev OwnedRuns (g : Graph.Graph) := Exec g .owned

namespace Typed
export Types (finish free allocate lend scalarLend scalarLet ownedLet)
end Typed
namespace Runs
export Exec (finish free allocate lend scalarLend scalarLet ownedLet)
end Runs

/-- Scalar-specialized induction excludes the owned terminal by its result index. -/
@[elab_as_elim] theorem Typed.induct
    {motive : ∀ ctx n m root, Typed g ctx n m root → Prop}
    (finish : ∀ {ctx m root result} (a : resultAt g ctx root = some result) (b : result.check m = true) (c : LiteralBound result), motive ctx 0 m root (.finish a b c))
    (free : ∀ {ctx n m root owner body slot} (a : Graph.nodeAt g root = .free owner body) (b : ownerSlot g ctx owner = some slot) (c : slot < n) (d : Typed g (consumed slot ctx) (n-1) m body), motive (consumed slot ctx) (n-1) m body d → motive ctx n m root (.free a b c d))
    (allocate : ∀ {ctx n m root value body} (a : Allocation g root value body) (b : value < 2^63) (c : Typed g (fresh ctx) (n+1) m body), motive (fresh ctx) (n+1) m body c → motive ctx n m root (.allocate a b c))
    (lend : ∀ {ctx n m root owner init body slot reader} (a : Shape g root owner init body) (b : ownerSlot g ctx owner = some slot) (c : slot < n) (d : Graph.Represents g (readerRoles ctx slot) init reader) (e : Typed g (ownedReturned ctx slot) (n+1) m body), motive (ownedReturned ctx slot) (n+1) m body e → motive ctx n m root (.lend a b c d e))
    (scalarLend : ∀ {ctx n m root owner init body slot reader} (a : ScalarShape g root owner init body) (b : ownerSlot g ctx owner = some slot) (c : slot < n) (d : Graph.Represents g (readerRoles ctx slot) init reader) (e : Typed g (scalarReturned ctx slot) n (m+1) body), motive (scalarReturned ctx slot) n (m+1) body e → motive ctx n m root (.scalarLend a b c d e))
    (scalarLet : ∀ {ctx n m root arg body raw} (a : PureOwnedScalar.Shape g root arg body) (b : PureOwnedScalar.Represents g ctx m arg raw) (c : Typed g (PureOwnedScalar.bindScalar ctx) n (m+1) body), motive (PureOwnedScalar.bindScalar ctx) n (m+1) body c → motive ctx n m root (.scalarLet a b c))
    (ownedLet : ∀ {ctx n m root argument body slot} (a : OwnedArgumentBinding.Shape g root argument body) (b : ownerSlot g ctx argument = some slot) (c : slot < n) (d : Typed g (OwnedArgumentBinding.transferred ctx slot) n m body), motive (OwnedArgumentBinding.transferred ctx slot) n m body d → motive ctx n m root (.ownedLet a b c d))
    (h : Typed g ctx n m root) : motive ctx n m root h := by
  have go : ∀ k ctx n m root (h : Types g k ctx n m root) (eq : k = .scalar), motive ctx n m root (Eq.mp (congrArg (fun k => Types g k ctx n m root) eq) h) := by
    intro k ctx n m root h
    induction h with
    | returnOwner _ => intro eq; cases eq
    | finish a b c => intro eq; cases eq; exact finish a b c
    | free a b c d ih => intro eq; cases eq; exact free a b c d (ih rfl)
    | allocate a b c ih => intro eq; cases eq; exact allocate a b c (ih rfl)
    | lend a b c d e ih => intro eq; cases eq; exact lend a b c d e (ih rfl)
    | scalarLend a b c d e ih => intro eq; cases eq; exact scalarLend a b c d e (ih rfl)
    | scalarLet a b c ih => intro eq; cases eq; exact scalarLet a b c (ih rfl)
    | ownedLet a b c d ih => intro eq; cases eq; exact ownedLet a b c d (ih rfl)
  exact go _ _ _ _ _ h rfl

@[elab_as_elim] theorem Runs.induct
    {motive : ∀ ctx root owners values s value events t, Runs g ctx root owners values s value events t → Prop}
    (finish : ∀ {ctx root owners values s result value} (a : resultAt g ctx root = some result) (b : result.eval values = some value), motive ctx root owners values s value [] s (.finish a b))
    (free : ∀ {ctx root owners values s value events t owner body slot x rest} (a : Graph.nodeAt g root = .free owner body) (b : ownerSlot g ctx owner = some slot) (c : Select owners slot x rest) (d : Runs g (consumed slot ctx) body rest values (freedState s x) value events t), motive (consumed slot ctx) body rest values (freedState s x) value events t d → motive ctx root owners values s value (.free x::events) t (.free a b c d))
    (allocate : ∀ {ctx root owners values s value events t payload body} (a : Allocation g root payload body) (b : Runs g (fresh ctx) body (s.nextObject::owners) values (allocatedState s payload) value events t), motive (fresh ctx) body (s.nextObject::owners) values (allocatedState s payload) value events t b → motive ctx root owners values s value (.alloc s.nextObject payload::events) t (.allocate a b))
    (lend : ∀ {ctx root owners values s value suffix t owner init body slot x rest copied reads} (a : Shape g root owner init body) (b : ownerSlot g ctx owner = some slot) (c : Select owners slot x rest) (d : Graph.CoreReads g (opened s x) s.nextLease x (readerRoles ctx slot) init copied reads) (e : Runs g (ownedReturned ctx slot) body (s.nextObject::owners) values (OwnedLendTransfer.final s copied) value suffix t), motive (ownedReturned ctx slot) body (s.nextObject::owners) values (OwnedLendTransfer.final s copied) value suffix t e → motive ctx root owners values s value (OwnedLendTransfer.events s x copied reads ++ suffix) t (.lend a b c d e))
    (scalarLend : ∀ {ctx root owners values s value suffix t owner init body slot x rest copied reads} (a : ScalarShape g root owner init body) (b : ownerSlot g ctx owner = some slot) (c : Select owners slot x rest) (d : Graph.CoreReads g (opened s x) s.nextLease x (readerRoles ctx slot) init copied reads) (e : Runs g (scalarReturned ctx slot) body owners (copied::values) (restored s) value suffix t), motive (scalarReturned ctx slot) body owners (copied::values) (restored s) value suffix t e → motive ctx root owners values s value (scalarEvents s x reads ++ suffix) t (.scalarLend a b c d e))
    (scalarLet : ∀ {ctx root owners values s value events t arg body computed} (a : PureOwnedScalar.Shape g root arg body) (b : PureOwnedScalar.Eval g ctx arg values computed) (c : Runs g (PureOwnedScalar.bindScalar ctx) body owners (computed::values) s value events t), motive (PureOwnedScalar.bindScalar ctx) body owners (computed::values) s value events t c → motive ctx root owners values s value events t (.scalarLet a b c))
    (ownedLet : ∀ {ctx root owners values s value events t argument body slot x rest} (a : OwnedArgumentBinding.Shape g root argument body) (b : ownerSlot g ctx argument = some slot) (c : Select owners slot x rest) (d : Runs g (OwnedArgumentBinding.transferred ctx slot) body owners values s value events t), motive (OwnedArgumentBinding.transferred ctx slot) body owners values s value events t d → motive ctx root owners values s value events t (.ownedLet a b c d))
    (h : Runs g ctx root owners values s value events t) : motive ctx root owners values s value events t h := by
  have go : ∀ k ctx root owners values s value events t (h : Exec g k ctx root owners values s value events t) (eq : k = .scalar), motive ctx root owners values s value events t (Eq.mp (congrArg (fun k => Exec g k ctx root owners values s value events t) eq) h) := by
    intro k ctx root owners values s value events t h
    induction h with
    | returnOwner _ _ => intro eq; cases eq
    | finish a b => intro eq; cases eq; exact finish a b
    | free a b c d ih => intro eq; cases eq; exact free a b c d (ih rfl)
    | allocate a b ih => intro eq; cases eq; exact allocate a b (ih rfl)
    | lend a b c d e ih => intro eq; cases eq; exact lend a b c d e (ih rfl)
    | scalarLend a b c d e ih => intro eq; cases eq; exact scalarLend a b c d e (ih rfl)
    | scalarLet a b c ih => intro eq; cases eq; exact scalarLet a b c (ih rfl)
    | ownedLet a b c d ih => intro eq; cases eq; exact ownedLet a b c d (ih rfl)
  exact go _ _ _ _ _ _ _ _ _ h rfl

theorem free_owns (owned : Owns s owners) (selected : Select owners slot x rest) :
    Owns (freedState s x) rest := by
  obtain ⟨distinct, absent⟩ := selected.unique owned.distinct
  refine ⟨distinct, ?_, ?_⟩
  · intro y hy
    have ne : y ≠ x := fun eq => absent (eq ▸ hy)
    simp [freedState, put, ne, owned.live y (selected.subset y hy)]
  · intro y hy
    exact owned.leaseFree y (selected.subset y hy)

theorem total (typed : Typed g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) :
    ∃ value events t, Runs g ctx root owners values s value events t := by
  induction typed using Typed.induct generalizing owners values s with
  | finish shape checked bound =>
      have : owners = [] := List.length_eq_zero_iff.mp length
      subst owners
      obtain ⟨v, hv⟩ := ScalarCoreCallers.Result.total checked scalarLength
      exact ⟨v, [], s, .finish shape hv⟩
  | free shape resolved bound typed ih =>
      have bound' := bound
      rw [← length] at bound'
      obtain ⟨x, rest, selected⟩ := select_total bound'
      have step : Step s (.free x) (freedState s x) :=
        .free (owned.live x selected.member) (owned.leaseFree x selected.member)
      obtain ⟨v, es, t, run⟩ := ih (by have := selected.length; omega) scalarLength
        (step_valid valid step) (free_owns owned selected)
      exact ⟨v, _, t, .free shape resolved selected run⟩
  | allocate shape bound typed ih =>
      obtain ⟨v, es, t, run⟩ := ih (by simp [length]) scalarLength
        (step_valid valid (Step.alloc (value := _))) (allocate_owns valid owned)
      exact ⟨v, _, t, .allocate shape run⟩
  | lend shape resolved bound reading typed ih =>
      have bound' := bound
      rw [← length] at bound'
      obtain ⟨x, rest, selected⟩ := select_total bound'
      have active : (opened s x).lease s.nextLease = some x := by simp [opened, put]
      have env : EnvValid (opened s x) [s.nextLease] := by
        intro l member
        have : l = s.nextLease := List.mem_singleton.mp member
        subst l
        exact ⟨x, active⟩
      obtain ⟨copied, reads, run⟩ := reader_total (env := [s.nextLease]) reading.scoped env
      obtain ⟨v, es, t, suffix⟩ := ih (by simp [length]) scalarLength
        (OwnedLendTransfer.prefix_valid valid (owned.live _ selected.member) run)
        (OwnedLendTransfer.transfer_owns valid owned)
      exact ⟨v, _, t, .lend shape resolved selected (reading.execution active run) suffix⟩
  | scalarLend shape resolved bound reading typed ih =>
      have bound' := bound
      rw [← length] at bound'
      obtain ⟨x, rest, selected⟩ := select_total bound'
      have active : (opened s x).lease s.nextLease = some x := by simp [opened, put]
      have env : EnvValid (opened s x) [s.nextLease] := by
        intro l member
        have : l = s.nextLease := List.mem_singleton.mp member
        subst l
        exact ⟨x, active⟩
      obtain ⟨copied, reads, run⟩ := reader_total (env := [s.nextLease]) reading.scoped env
      obtain ⟨v, es, t, suffix⟩ := ih (values := copied :: values) length (by simp [scalarLength])
        (steps_valid valid (scalar_steps valid (owned.live _ selected.member) run))
        (restored_owns owned)
      exact ⟨v, _, t, .scalarLend shape resolved selected (reading.execution active run) suffix⟩

  | scalarLet shape represented typed ih =>
      obtain ⟨computed, evaluated⟩ := PureOwnedScalar.total represented scalarLength
      obtain ⟨v, es, t, run⟩ := ih (values := computed :: values) length (by simp [scalarLength]) valid owned
      exact ⟨v, es, t, .scalarLet shape evaluated run⟩

  | ownedLet shape resolved bound typed ih =>
      have bound' := bound
      rw [← length] at bound'
      obtain ⟨x, rest, selected⟩ := select_total bound'
      obtain ⟨v, es, t, run⟩ := ih length scalarLength valid owned
      exact ⟨v, es, t, .ownedLet shape resolved selected run⟩

theorem Allocation.application (a : Allocation g root v b) :
    ∃ f x, Graph.nodeAt g root = .app f x := by
  cases a with | intro f x _ _ _ h _ _ _ _ _ => exact ⟨f, x, h⟩

theorem finish_head (h : resultAt g ctx root = some result) :
    (∃ v, Graph.nodeAt g root = .integer v) ∨ (∃ k, Graph.nodeAt g root = .var k) := by
  cases hg : Graph.nodeAt g root <;> simp [resultAt, ScalarCoreCallers.resultAt, hg] at h
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩

theorem finish_not_free (h : resultAt g ctx root = some result)
    (shape : Graph.nodeAt g root = .free owner body) : False := by
  simp [resultAt, ScalarCoreCallers.resultAt, shape] at h
theorem finish_not_app (h : resultAt g ctx root = some result)
    (shape : Graph.nodeAt g root = .app f a) : False := by
  simp [resultAt, ScalarCoreCallers.resultAt, shape] at h
theorem finish_not_lend (h : resultAt g ctx root = some result)
    (shape : Graph.nodeAt g root = .lend o r c) : False := by
  simp [resultAt, ScalarCoreCallers.resultAt, shape] at h

theorem execution_safe (typed : Typed g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) (run : Runs g ctx root owners values s v es t) :
    Steps s es t ∧ Valid t ∧ Owns t [] := by
  induction typed using Typed.induct generalizing owners values s v es t with
  | finish shape checked bound =>
      cases run with
      | finish _ _ => exact ⟨.nil, valid, ⟨by simp, by simp, by simp⟩⟩
      | free other _ _ _ => exact False.elim (finish_not_free shape other)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; exact False.elim (finish_not_app shape other)
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (finish_not_lend shape other)
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (finish_not_lend shape other)
      | scalarLet p _ _ => obtain ⟨f, h⟩ := p.head; exact False.elim (finish_not_app shape h)
      | ownedLet p _ _ _ => obtain ⟨f, h⟩ := p.head; exact False.elim (finish_not_app shape h)

  | free shape resolved bound typed ih =>
      cases run with
      | finish other _ => exact False.elim (finish_not_free other shape)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | free other resolved' selected restRun =>
          have eq := shape.symm.trans other; cases eq
          have eq := resolved.symm.trans resolved'; cases eq
          have step := Step.free (owned.live _ selected.member) (owned.leaseFree _ selected.member)
          obtain ⟨steps, vt, ot⟩ := ih (by have := selected.length; omega) scalarLength
            (step_valid valid step) (free_owns owned selected) restRun
          exact ⟨.cons step steps, vt, ot⟩
      | scalarLet p _ _ => obtain ⟨f, h⟩ := p.head; have := shape.symm.trans h; contradiction
      | ownedLet p _ _ _ => obtain ⟨f, h⟩ := p.head; have := shape.symm.trans h; contradiction

  | allocate a bound typed ih =>
      cases run with
      | finish other _ => obtain ⟨f, x, shape⟩ := a.application; exact False.elim (finish_not_app other shape)
      | free other _ _ _ => obtain ⟨f, x, shape⟩ := a.application; have := shape.symm.trans other; contradiction
      | lend b _ _ _ _ =>
          obtain ⟨f, x, shape⟩ := a.application
          obtain ⟨r, k, other⟩ := b.head
          have := shape.symm.trans other; contradiction
      | scalarLend b _ _ _ _ =>
          obtain ⟨f, x, shape⟩ := a.application
          obtain ⟨r, k, other⟩ := b.head
          have := shape.symm.trans other; contradiction
      | allocate a' restRun =>
          obtain ⟨rfl, rfl⟩ := a.unique a'
          obtain ⟨steps, vt, ot⟩ := ih (by simp [length]) scalarLength
            (step_valid valid (Step.alloc (value := _))) (allocate_owns valid owned) restRun
          exact ⟨.cons .alloc steps, vt, ot⟩
      | scalarLet p _ _ => exact False.elim (a.not_pure p)
      | ownedLet p resolved _ _ => exact False.elim (a.not_owned_binding p resolved)

  | lend shape resolved bound reading typed ih =>
      cases run with
      | finish other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (finish_not_lend other h)
      | free other _ _ _ => obtain ⟨f, x, h⟩ := shape.head; have := h.symm.trans other; contradiction
      | allocate a _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.application
          have := h.symm.trans other; contradiction
      | scalarLend shape' _ _ _ _ => exact False.elim (shape'.not_owned shape)
      | lend shape' resolved' selected read suffix =>
          obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          have reader := reading.reflect read
          have pre := OwnedLendTransfer.prefix_steps valid (owned.live _ selected.member) reader
          obtain ⟨steps, vt, ot⟩ := ih (by simp [length]) scalarLength (steps_valid valid pre)
            (OwnedLendTransfer.transfer_owns valid owned) suffix
          exact ⟨steps_append pre steps, vt, ot⟩
      | scalarLet p _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction
      | ownedLet p _ _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction

  | scalarLend shape resolved bound reading typed ih =>
      cases run with
      | finish other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (finish_not_lend other h)
      | free other _ _ _ => obtain ⟨f, x, h⟩ := shape.head; have := h.symm.trans other; contradiction
      | allocate a _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.application
          have := h.symm.trans other; contradiction
      | lend shape' _ _ _ _ => exact False.elim (shape.not_owned shape')
      | scalarLend shape' resolved' selected read suffix =>
          obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          have reader := reading.reflect read
          have pre := scalar_steps valid (owned.live _ selected.member) reader
          obtain ⟨steps, vt, ot⟩ := ih length (by simp [scalarLength]) (steps_valid valid pre)
            (restored_owns owned) suffix
          exact ⟨steps_append pre steps, vt, ot⟩
      | scalarLet p _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction
      | ownedLet p _ _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction

  | scalarLet shape represented typed ih =>
      cases run with
      | finish h _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (finish_not_app h other)
      | free h _ _ _ => obtain ⟨f, other⟩ := shape.head; have := other.symm.trans h; contradiction
      | allocate a _ => exact False.elim (a.not_pure shape)
      | lend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLet shape' evaluated suffix =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          exact ih length (by simp [scalarLength]) valid owned suffix
      | ownedLet p _ _ _ => exact False.elim (p.not_pure shape)

  | ownedLet shape resolved bound typed ih =>
      cases run with
      | finish h _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (finish_not_app h other)
      | free h _ _ _ => obtain ⟨f, other⟩ := shape.head; have := other.symm.trans h; contradiction
      | allocate a _ => exact False.elim (a.not_owned_binding shape resolved)
      | lend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLet p _ _ => exact False.elim (shape.not_pure p)
      | ownedLet shape' resolved' selected suffix =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          exact ih length scalarLength valid owned suffix

/-- Accounting follows the original graph execution, including allocations
inside the continuation, rather than a separately supplied usage trace. -/
theorem release_conservation (typed : Typed g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (run : Runs g ctx root owners values s v es t) (x : Nat) :
    (released es).count x = owners.count x + (allocations es).count x := by
  induction typed using Typed.induct generalizing owners values s v es t with
  | finish shape checked bound =>
      cases run with
      | finish _ _ =>
          have : owners = [] := List.length_eq_zero_iff.mp length
          subst owners
          simp [released, allocations]
      | free other _ _ _ => exact False.elim (finish_not_free shape other)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; exact False.elim (finish_not_app shape other)
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (finish_not_lend shape other)
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (finish_not_lend shape other)
      | scalarLet p _ _ => obtain ⟨f, h⟩ := p.head; exact False.elim (finish_not_app shape h)
      | ownedLet p _ _ _ => obtain ⟨f, h⟩ := p.head; exact False.elim (finish_not_app shape h)

  | free shape resolved bound typed ih =>
      cases run with
      | finish other _ => exact False.elim (finish_not_free other shape)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | free other resolved' selected restRun =>
          have eq := shape.symm.trans other; cases eq
          have eq := resolved.symm.trans resolved'; cases eq
          have h := selected.count x
          have hr := ih (by have := selected.length; omega) scalarLength restRun
          simp only [released, allocations, List.filterMap_cons, List.count_cons] at *
          simp only [beq_iff_eq] at *
          omega
      | scalarLet p _ _ => obtain ⟨f, h⟩ := p.head; have := shape.symm.trans h; contradiction
      | ownedLet p _ _ _ => obtain ⟨f, h⟩ := p.head; have := shape.symm.trans h; contradiction

  | allocate a bound typed ih =>
      cases run with
      | finish other _ => obtain ⟨f, x, shape⟩ := a.application; exact False.elim (finish_not_app other shape)
      | free other _ _ _ => obtain ⟨f, x, shape⟩ := a.application; have := shape.symm.trans other; contradiction
      | lend b _ _ _ _ =>
          obtain ⟨f, x, shape⟩ := a.application
          obtain ⟨r, k, other⟩ := b.head
          have := shape.symm.trans other; contradiction
      | scalarLend b _ _ _ _ =>
          obtain ⟨f, x, shape⟩ := a.application
          obtain ⟨r, k, other⟩ := b.head
          have := shape.symm.trans other; contradiction
      | allocate a' restRun =>
          obtain ⟨rfl, rfl⟩ := a.unique a'
          have hr := ih (by simp [length]) scalarLength restRun
          simp only [released, allocations, List.filterMap_cons, List.count_cons] at *
          omega
      | scalarLet p _ _ => exact False.elim (a.not_pure p)
      | ownedLet p resolved _ _ => exact False.elim (a.not_owned_binding p resolved)

  | lend shape resolved bound reading typed ih =>
      cases run with
      | finish other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (finish_not_lend other h)
      | free other _ _ _ => obtain ⟨f, x, h⟩ := shape.head; have := h.symm.trans other; contradiction
      | allocate a _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.application
          have := h.symm.trans other; contradiction
      | scalarLend shape' _ _ _ _ => exact False.elim (shape'.not_owned shape)
      | lend shape' resolved' selected read suffix =>
          obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          have reader := reading.reflect read
          have hr := ih (by simp [length]) scalarLength suffix
          have ha := reader_allocations reader
          have hf := reader_releases reader
          simp only [released, allocations] at ha hf
          simp [OwnedLendTransfer.events, released, allocations, List.filterMap_append,
            ha, hf, List.count_cons] at *
          omega
      | scalarLet p _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction
      | ownedLet p _ _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction

  | scalarLend shape resolved bound reading typed ih =>
      cases run with
      | finish other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (finish_not_lend other h)
      | free other _ _ _ => obtain ⟨f, x, h⟩ := shape.head; have := h.symm.trans other; contradiction
      | allocate a _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.application
          have := h.symm.trans other; contradiction
      | lend shape' _ _ _ _ => exact False.elim (shape.not_owned shape')
      | scalarLend shape' resolved' selected read suffix =>
          obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          have reader := reading.reflect read
          have hr := ih length (by simp [scalarLength]) suffix
          have ha := reader_allocations reader
          have hf := reader_releases reader
          simp only [released, allocations] at ha hf
          simp [scalarEvents, released, allocations, List.filterMap_append,
            ha, hf] at *
          omega
      | scalarLet p _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction
      | ownedLet p _ _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction

  | scalarLet shape represented typed ih =>
      cases run with
      | finish h _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (finish_not_app h other)
      | free h _ _ _ => obtain ⟨f, other⟩ := shape.head; have := other.symm.trans h; contradiction
      | allocate a _ => exact False.elim (a.not_pure shape)
      | lend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLet shape' evaluated suffix =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          exact ih length (by simp [scalarLength]) suffix
      | ownedLet p _ _ _ => exact False.elim (p.not_pure shape)

  | ownedLet shape resolved bound typed ih =>
      cases run with
      | finish h _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (finish_not_app h other)
      | free h _ _ _ => obtain ⟨f, other⟩ := shape.head; have := other.symm.trans h; contradiction
      | allocate a _ => exact False.elim (a.not_owned_binding shape resolved)
      | lend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLet p _ _ => exact False.elim (shape.not_pure p)
      | ownedLet shape' resolved' selected suffix =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          exact ih length scalarLength suffix

theorem no_tracked_leaks (typed : Typed g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) (run : Runs g ctx root owners values s v es t)
    (tracked : x ∈ owners ∨ x ∈ allocations es) :
    (released es).count x = 1 ∧ t.live x = false := by
  have steps := (execution_safe typed length scalarLength valid owned run).1
  have conserved := release_conservation typed length scalarLength run x
  have positive : 0 < (released es).count x := by
    rcases tracked with initial | allocated
    · have := List.count_pos_iff.mpr initial; omega
    · have := List.count_pos_iff.mpr allocated; omega
  have member := List.count_pos_iff.mp positive
  have count := (releases_distinct valid steps).count (a := x)
  exact ⟨by simpa [member] using count, released_dead valid steps (released_mem.mp member)⟩

/-- Number of lexical reader entries in the actual heap event trace. -/
def leaseStarts (events : List Event) : Nat :=
  (events.filterMap fun e => match e with | .beginLease _ _ => some () | _ => none).length

theorem leaseStarts_append : leaseStarts (xs ++ ys) = leaseStarts xs + leaseStarts ys := by
  simp [leaseStarts, List.filterMap_append]

private theorem CoreReads.no_lease_starts (run : Graph.CoreReads g s token owner ctx root v es) :
    leaseStarts es = 0 := by
  induction run <;> simp_all [leaseStarts, List.filterMap_append]

theorem lease_counter (run : Runs g ctx root owners values s v es t) :
    t.nextLease = s.nextLease + leaseStarts es := by
  induction run using Runs.induct with
  | scalarLet _ _ _ ih => exact ih
  | ownedLet _ _ _ _ ih => exact ih
  | finish => simp [leaseStarts]
  | free _ _ _ _ ih => simpa [leaseStarts, freedState] using ih
  | allocate _ _ ih => simpa [leaseStarts, allocatedState] using ih
  | lend _ _ _ read _ ih =>
      have hr := CoreReads.no_lease_starts read
      simp only [leaseStarts] at hr
      simp [OwnedLendTransfer.events, leaseStarts, List.filterMap_append, hr,
        OwnedLendTransfer.final, allocatedState, restored] at *
      omega

  | scalarLend _ _ _ read _ ih =>
      have hr := CoreReads.no_lease_starts read
      simp only [leaseStarts] at hr
      simp [scalarEvents, leaseStarts, List.filterMap_append, hr, restored] at *
      omega

/-- Completed nested lends restore every ambient lease; fresh token counters
may advance, but never move backwards. -/
theorem lease_frame (run : Runs g ctx root owners values s v es t) :
    t.lease = s.lease ∧ s.nextLease ≤ t.nextLease := by
  induction run using Runs.induct with
  | scalarLet _ _ _ ih => exact ih
  | ownedLet _ _ _ _ ih => exact ih
  | finish => exact ⟨rfl, Nat.le_refl _⟩
  | free _ _ _ _ ih => exact ih
  | allocate _ _ ih => exact ih
  | lend _ _ _ _ _ ih =>
      refine ⟨ih.1, ?_⟩
      have h := ih.2
      dsimp [OwnedLendTransfer.final, allocatedState, restored] at h
      omega

  | scalarLend _ _ _ _ _ ih =>
      refine ⟨ih.1, ?_⟩
      have h := ih.2
      dsimp [OwnedLendTransfer.final, allocatedState, restored] at h
      omega

/-- Every token created during this execution is expired at return. This
covers all recursively nested reader scopes, not just the outermost one. -/
theorem created_tokens_expired (valid : Valid s) (run : Runs g ctx root owners values s v es t)
    (fresh : s.nextLease ≤ token) : t.lease token = none := by
  rw [(lease_frame run).1]
  cases h : s.lease token with
  | none => rfl
  | some x => have := (valid.leased token x h).1; omega

/-- If the initial capability environment covers every live object, every
final object is dead. Ambient objects outside that environment are not owned. -/
theorem heap_empty (typed : Typed g ctx n m root) (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) (run : Runs g ctx root owners values s v es t)
    (coverage : ∀ x, s.live x = true → x ∈ owners) : ∀ x, t.live x = false := by
  intro x
  cases live : t.live x with
  | false => rfl
  | true =>
      have steps := (execution_safe typed length scalarLength valid owned run).1
      have origin := live_origin steps live
      have tracked : x ∈ owners ∨ x ∈ allocations es := by
        rcases origin with initial | allocated
        · exact Or.inl (coverage x initial)
        · exact Or.inr allocated
      have dead := (no_tracked_leaks typed length scalarLength valid owned run tracked).2
      rw [live] at dead
      contradiction

theorem Typed.free_inversion (typed : Typed g ctx n m root)
    (shape : Graph.nodeAt g root = .free owner body) :
    ∃ slot, ownerSlot g ctx owner = some slot ∧ slot < n ∧
      Typed g (consumed slot ctx) (n - 1) m body := by
  cases typed with
  | finish h _ _ => exact False.elim (finish_not_free h shape)
  | free other resolved bound rest =>
      have eq := shape.symm.trans other; cases eq
      exact ⟨_, resolved, bound, rest⟩
  | allocate a _ _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
  | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
  | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
  | scalarLet p _ _ => obtain ⟨f, other⟩ := p.head; have := shape.symm.trans other; contradiction

  | ownedLet p _ _ _ => obtain ⟨f, other⟩ := p.head; have := shape.symm.trans other; contradiction

theorem Typed.finish_inversion (typed : Typed g ctx n m root)
    (shape : Graph.nodeAt g root = .integer value) : n = 0 ∧ value < 2^63 := by
  cases typed with
  | finish h _ bound =>
      simp [resultAt, ScalarCoreCallers.resultAt, shape] at h
      subst h
      exact ⟨rfl, bound⟩
  | free other _ _ _ => have := shape.symm.trans other; contradiction
  | allocate a _ _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
  | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
  | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
  | scalarLet p _ _ => obtain ⟨f, other⟩ := p.head; have := shape.symm.trans other; contradiction

  | ownedLet p _ _ _ => obtain ⟨f, other⟩ := p.head; have := shape.symm.trans other; contradiction

theorem dead_owner_rejected (shape : Graph.nodeAt g root = .free owner body)
    (dead : ownerSlot g ctx owner = none) : ¬ Typed g ctx n m root := by
  intro typed
  obtain ⟨slot, resolved, _⟩ := typed.free_inversion shape
  rw [dead] at resolved
  contradiction

theorem Typed.lend_inversion (typed : Typed g ctx n m root)
    (shape : Shape g root owner init body) :
    ∃ slot reader, ownerSlot g ctx owner = some slot ∧ slot < n ∧
      Graph.Represents g (readerRoles ctx slot) init reader ∧
      Typed g (ownedReturned ctx slot) (n + 1) m body := by
  cases typed with
  | finish h _ _ => obtain ⟨f, x, other⟩ := shape.head; exact False.elim (finish_not_lend h other)
  | free other _ _ _ => obtain ⟨f, x, h⟩ := shape.head; have := h.symm.trans other; contradiction
  | allocate a _ _ =>
      obtain ⟨f, x, h⟩ := shape.head
      obtain ⟨r, k, other⟩ := a.application
      have := h.symm.trans other; contradiction
  | lend shape' resolved bound reading rest =>
      obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
      exact ⟨_, _, resolved, bound, reading, rest⟩
  | scalarLend shape' _ _ _ _ => exact False.elim (shape'.not_owned shape)
  | scalarLet p _ _ =>
      obtain ⟨f, x, h⟩ := shape.head
      obtain ⟨r, other⟩ := p.head
      have := h.symm.trans other; contradiction

  | ownedLet p _ _ _ =>
      obtain ⟨f, x, h⟩ := shape.head
      obtain ⟨r, other⟩ := p.head
      have := h.symm.trans other; contradiction

theorem Typed.scalarLend_inversion (typed : Typed g ctx n m root)
    (shape : ScalarShape g root owner init body) :
    ∃ slot reader, ownerSlot g ctx owner = some slot ∧ slot < n ∧
      Graph.Represents g (readerRoles ctx slot) init reader ∧
      Typed g (scalarReturned ctx slot) n (m + 1) body := by
  cases typed with
  | finish h _ _ => obtain ⟨f, x, other⟩ := shape.head; exact False.elim (finish_not_lend h other)
  | free other _ _ _ => obtain ⟨f, x, h⟩ := shape.head; have := h.symm.trans other; contradiction
  | allocate a _ _ =>
      obtain ⟨f, x, h⟩ := shape.head
      obtain ⟨r, k, other⟩ := a.application
      have := h.symm.trans other; contradiction
  | lend shape' _ _ _ _ => exact False.elim (shape.not_owned shape')
  | scalarLend shape' resolved bound reading rest =>
      obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
      exact ⟨_, _, resolved, bound, reading, rest⟩
  | scalarLet p _ _ =>
      obtain ⟨f, x, h⟩ := shape.head
      obtain ⟨r, other⟩ := p.head
      have := h.symm.trans other; contradiction

  | ownedLet p _ _ _ =>
      obtain ⟨f, x, h⟩ := shape.head
      obtain ⟨r, other⟩ := p.head
      have := h.symm.trans other; contradiction

theorem core_reads_deterministic (a : Graph.CoreReads g s token owner ctx root v es)
    (b : Graph.CoreReads g s token owner ctx root w fs) : v = w ∧ es = fs := by
  induction a generalizing w fs with
  | scalar shape => cases b <;> simp_all <;> first | exact ih (by assumption) | omega
  | read shape role bound lease => cases b <;> simp_all <;> first | exact ih (by assumption) | omega
  | strict shape _ _ ia ib =>
      cases b <;> simp_all
      obtain ⟨rfl, rfl⟩ := ia (by assumption)
      obtain ⟨rfl, rfl⟩ := ib (by assumption)
      exact ⟨rfl, rfl⟩
  | app shape lam ty _ _ ia ib =>
      cases b <;> simp_all
      obtain ⟨rfl, rfl⟩ := ia (by assumption)
      obtain ⟨rfl, rfl⟩ := ib (by assumption)
      exact ⟨rfl, rfl⟩
  | yes shape left right bound _ ih => cases b <;> simp_all <;> first | exact ih (by assumption) | omega
  | no shape left right bound _ ih => cases b <;> simp_all <;> first | exact ih (by assumption) | omega

/-- The graph semantics fixes the actual returned scalar, complete effect
trace and final heap, independently of any particular typing derivation. -/
theorem Runs.deterministic (a : Runs g ctx root owners values s v es t)
    (b : Runs g ctx root owners values s w fs u) : v = w ∧ es = fs ∧ t = u := by
  induction a using Runs.induct generalizing w fs u with
  | finish shape value =>
      cases b with
      | finish shape' value' =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := value.symm.trans value'; cases eq
          exact ⟨rfl, rfl, rfl⟩
      | free other _ _ _ => exact False.elim (finish_not_free shape other)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; exact False.elim (finish_not_app shape other)
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (finish_not_lend shape other)
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; exact False.elim (finish_not_lend shape other)
      | scalarLet p _ _ => obtain ⟨f, h⟩ := p.head; exact False.elim (finish_not_app shape h)
      | ownedLet p _ _ _ => obtain ⟨f, h⟩ := p.head; exact False.elim (finish_not_app shape h)

  | free shape resolved selected restRun ih =>
      cases b with
      | finish other _ => exact False.elim (finish_not_free other shape)
      | allocate a _ => obtain ⟨f, x, other⟩ := a.application; have := shape.symm.trans other; contradiction
      | lend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | scalarLend a _ _ _ _ => obtain ⟨f, x, other⟩ := a.head; have := shape.symm.trans other; contradiction
      | free other resolved' selected' restRun' =>
          have eq := shape.symm.trans other; cases eq
          have eq := resolved.symm.trans resolved'; cases eq
          obtain ⟨rfl, rfl⟩ := LeaseErasure.select_deterministic selected selected'
          obtain ⟨rfl, rfl, rfl⟩ := ih restRun'
          exact ⟨rfl, rfl, rfl⟩
      | scalarLet p _ _ => obtain ⟨f, h⟩ := p.head; have := shape.symm.trans h; contradiction
      | ownedLet p _ _ _ => obtain ⟨f, h⟩ := p.head; have := shape.symm.trans h; contradiction

  | allocate a restRun ih =>
      cases b with
      | finish other _ => obtain ⟨f, x, shape⟩ := a.application; exact False.elim (finish_not_app other shape)
      | free other _ _ _ => obtain ⟨f, x, shape⟩ := a.application; have := shape.symm.trans other; contradiction
      | lend b _ _ _ _ =>
          obtain ⟨f, x, shape⟩ := a.application
          obtain ⟨r, k, other⟩ := b.head
          have := shape.symm.trans other; contradiction
      | scalarLend b _ _ _ _ =>
          obtain ⟨f, x, shape⟩ := a.application
          obtain ⟨r, k, other⟩ := b.head
          have := shape.symm.trans other; contradiction
      | allocate a' restRun' =>
          obtain ⟨rfl, rfl⟩ := a.unique a'
          obtain ⟨rfl, rfl, rfl⟩ := ih restRun'
          exact ⟨rfl, rfl, rfl⟩
      | scalarLet p _ _ => exact False.elim (a.not_pure p)
      | ownedLet p resolved _ _ => exact False.elim (a.not_owned_binding p resolved)

  | lend shape resolved selected read suffix ih =>
      cases b with
      | finish other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (finish_not_lend other h)
      | free other _ _ _ => obtain ⟨f, x, h⟩ := shape.head; have := h.symm.trans other; contradiction
      | allocate a _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.application
          have := h.symm.trans other; contradiction
      | scalarLend shape' _ _ _ _ => exact False.elim (shape'.not_owned shape)
      | lend shape' resolved' selected' read' suffix' =>
          obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          obtain ⟨rfl, rfl⟩ := LeaseErasure.select_deterministic selected selected'
          obtain ⟨rfl, rfl⟩ := core_reads_deterministic read read'
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩
      | scalarLet p _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction
      | ownedLet p _ _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction

  | scalarLend shape resolved selected read suffix ih =>
      cases b with
      | finish other _ => obtain ⟨f, x, h⟩ := shape.head; exact False.elim (finish_not_lend other h)
      | free other _ _ _ => obtain ⟨f, x, h⟩ := shape.head; have := h.symm.trans other; contradiction
      | allocate a _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.application
          have := h.symm.trans other; contradiction
      | lend shape' _ _ _ _ => exact False.elim (shape.not_owned shape')
      | scalarLend shape' resolved' selected' read' suffix' =>
          obtain ⟨rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          obtain ⟨rfl, rfl⟩ := LeaseErasure.select_deterministic selected selected'
          obtain ⟨rfl, rfl⟩ := core_reads_deterministic read read'
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩
      | scalarLet p _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction
      | ownedLet p _ _ _ =>
          obtain ⟨f, x, h⟩ := shape.head
          obtain ⟨k, other⟩ := p.head
          have := h.symm.trans other; contradiction

  | scalarLet shape evaluated suffix ih =>
      cases b with
      | finish h _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (finish_not_app h other)
      | free h _ _ _ => obtain ⟨f, other⟩ := shape.head; have := other.symm.trans h; contradiction
      | allocate a _ => exact False.elim (a.not_pure shape)
      | lend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLet shape' evaluated' suffix' =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have eq := PureOwnedScalar.Eval.deterministic evaluated evaluated'
          subst eq
          exact ih suffix'
      | ownedLet p _ _ _ => exact False.elim (p.not_pure shape)

  | ownedLet shape resolved selected suffix ih =>
      cases b with
      | finish h _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (finish_not_app h other)
      | free h _ _ _ => obtain ⟨f, other⟩ := shape.head; have := other.symm.trans h; contradiction
      | allocate a _ => exact False.elim (a.not_owned_binding shape resolved)
      | lend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLend a _ _ _ _ =>
          obtain ⟨f, h⟩ := shape.head
          obtain ⟨r, k, other⟩ := a.head
          have := h.symm.trans other; contradiction
      | scalarLet p _ _ => exact False.elim (shape.not_pure p)
      | ownedLet shape' resolved' selected' suffix' =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have eq := resolved.symm.trans resolved'; cases eq
          exact ih suffix'

theorem Typed.scalarLet_inversion (typed : Typed g ctx n m root)
    (shape : PureOwnedScalar.Shape g root arg body) :
    ∃ raw, PureOwnedScalar.Represents g ctx m arg raw ∧
      Typed g (PureOwnedScalar.bindScalar ctx) n (m + 1) body := by
  cases typed with
  | finish h _ _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (finish_not_app h other)
  | free other _ _ _ => obtain ⟨f, h⟩ := shape.head; have := h.symm.trans other; contradiction
  | allocate a _ _ => exact False.elim (a.not_pure shape)
  | lend a _ _ _ _ =>
      obtain ⟨f, h⟩ := shape.head
      obtain ⟨r, k, other⟩ := a.head
      have := h.symm.trans other; contradiction
  | scalarLend a _ _ _ _ =>
      obtain ⟨f, h⟩ := shape.head
      obtain ⟨r, k, other⟩ := a.head
      have := h.symm.trans other; contradiction
  | scalarLet shape' represented rest =>
      obtain ⟨rfl, rfl⟩ := shape.unique shape'
      exact ⟨_, represented, rest⟩

  | ownedLet p _ _ _ => exact False.elim (p.not_pure shape)

/-- A scalar binding's operational result is the value actually passed to
its continuation, not a producer-supplied scalar observation. -/

theorem Runs.scalarLet_inversion (run : Runs g ctx root owners values s v es t)
    (shape : PureOwnedScalar.Shape g root arg body) :
    ∃ computed, PureOwnedScalar.Eval g ctx arg values computed ∧
      Runs g (PureOwnedScalar.bindScalar ctx) body owners (computed :: values) s v es t := by
  cases run with
  | finish h _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (finish_not_app h other)
  | free other _ _ _ => obtain ⟨f, h⟩ := shape.head; have := h.symm.trans other; contradiction
  | allocate a _ => exact False.elim (a.not_pure shape)
  | lend a _ _ _ _ =>
      obtain ⟨f, h⟩ := shape.head
      obtain ⟨r, k, other⟩ := a.head
      have := h.symm.trans other; contradiction
  | scalarLend a _ _ _ _ =>
      obtain ⟨f, h⟩ := shape.head
      obtain ⟨r, k, other⟩ := a.head
      have := h.symm.trans other; contradiction
  | scalarLet shape' evaluated rest =>
      obtain ⟨rfl, rfl⟩ := shape.unique shape'
      exact ⟨_, evaluated, rest⟩
  | ownedLet p _ _ _ => exact False.elim (p.not_pure shape)

theorem Typed.ownedLet_inversion (typed : Typed g ctx n m root)
    (shape : OwnedArgumentBinding.Shape g root argument body)
    (resolved : ownerSlot g ctx argument = some slot) :
    slot < n ∧ Typed g (OwnedArgumentBinding.transferred ctx slot) n m body := by
  cases typed with
  | finish h _ _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (finish_not_app h other)
  | free other _ _ _ => obtain ⟨f, h⟩ := shape.head; have := h.symm.trans other; contradiction
  | allocate a _ _ => exact False.elim (a.not_owned_binding shape resolved)
  | lend a _ _ _ _ =>
      obtain ⟨f, h⟩ := shape.head
      obtain ⟨r, k, other⟩ := a.head
      have := h.symm.trans other; contradiction
  | scalarLend a _ _ _ _ =>
      obtain ⟨f, h⟩ := shape.head
      obtain ⟨r, k, other⟩ := a.head
      have := h.symm.trans other; contradiction
  | scalarLet p _ _ => exact False.elim (shape.not_pure p)
  | ownedLet shape' resolved' selected suffix =>
      obtain ⟨rfl, rfl⟩ := shape.unique shape'
      have eq := resolved.symm.trans resolved'; cases eq
      exact ⟨selected, suffix⟩

/-- Owned application transfers the selected identity into the parameter's
lexical context without allocating, freeing, or duplicating the capability. -/
theorem Runs.ownedLet_inversion (run : Runs g ctx root owners values s v es t)
    (shape : OwnedArgumentBinding.Shape g root argument body)
    (resolved : ownerSlot g ctx argument = some slot) :
    ∃ x rest, Select owners slot x rest ∧
      Runs g (OwnedArgumentBinding.transferred ctx slot) body owners values s v es t := by
  cases run with
  | finish h _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (finish_not_app h other)
  | free other _ _ _ => obtain ⟨f, h⟩ := shape.head; have := h.symm.trans other; contradiction
  | allocate a _ => exact False.elim (a.not_owned_binding shape resolved)
  | lend a _ _ _ _ =>
      obtain ⟨f, h⟩ := shape.head
      obtain ⟨r, k, other⟩ := a.head
      have := h.symm.trans other; contradiction
  | scalarLend a _ _ _ _ =>
      obtain ⟨f, h⟩ := shape.head
      obtain ⟨r, k, other⟩ := a.head
      have := h.symm.trans other; contradiction
  | scalarLet p _ _ => exact False.elim (shape.not_pure p)
  | ownedLet shape' resolved' selected suffix =>
      obtain ⟨rfl, rfl⟩ := shape.unique shape'
      have eq := resolved.symm.trans resolved'; cases eq
      exact ⟨_, _, selected, suffix⟩

/-- The application spine alone also describes allocation binding. Its
variable-argument shape distinguishes linear transfer and derives resolution
from typing, rather than assuming an owner lookup supplied by a producer. -/
theorem Typed.ownedVar_inversion (typed : Typed g ctx n m root)
    (shape : OwnedArgumentBinding.Shape g root argument body)
    (variableShape : Graph.nodeAt g argument = .var k) :
    ∃ slot, ownerSlot g ctx argument = some slot ∧ slot < n ∧
      Typed g (OwnedArgumentBinding.transferred ctx slot) n m body := by
  cases typed with
  | finish h _ _ => obtain ⟨f, other⟩ := shape.head; exact False.elim (finish_not_app h other)
  | free other _ _ _ => obtain ⟨f, h⟩ := shape.head; have := h.symm.trans other; contradiction
  | allocate a _ _ => exact False.elim (a.not_variable_argument shape variableShape)
  | lend a _ _ _ _ =>
      obtain ⟨f, h⟩ := shape.head
      obtain ⟨r, k, other⟩ := a.head
      have := h.symm.trans other; contradiction
  | scalarLend a _ _ _ _ =>
      obtain ⟨f, h⟩ := shape.head
      obtain ⟨r, k, other⟩ := a.head
      have := h.symm.trans other; contradiction
  | scalarLet p _ _ => exact False.elim (shape.not_pure p)
  | ownedLet shape' resolved bound suffix =>
      obtain ⟨rfl, rfl⟩ := shape.unique shape'
      exact ⟨_, resolved, bound, suffix⟩

end Jihoo.OwnedCoreContinuation
