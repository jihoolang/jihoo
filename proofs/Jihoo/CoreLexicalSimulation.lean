import Jihoo.CoreLexicalExecution
import Jihoo.FramedOwnedApplications

/-! The constructor/call typing fragment executes in a lexical runtime whose
rules do not carry a resource partition plan or a static ownership context.
Static tombstones revoke typing authority, not physical lexical captures.
Simulation and runtime determinism give coherence across plans; existing
constructive totality and trace safety then apply to every lexical execution.
The scope remains the specified Buffer1 fragment, not arbitrary dependent Core. -/
namespace Jihoo.CoreLexicalSimulation
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext OwnedCoreContinuation
open CoreLexicalContext CoreLexicalExecution FramedOwnedApplications
open OwnedCoreApplications (resultOwners)

def resultValue : ResultKind → Nat → Value
  | .scalar, v => .scalar v
  | .owned, v => .owner v

theorem resultValue_injective (h : resultValue kind v = resultValue kind w) : v = w := by
  cases kind <;> cases h <;> rfl

theorem pure_simulation (run : PureOwnedScalar.Eval g ctx root values v)
    (agree : Agrees ctx owners values env) :
    Eval g env root s (.scalar v) [] s := by
  induction run generalizing env s with
  | integer shape => exact .scalar shape
  | scalar shape lookup value => exact .var shape (agree.scalar _ _ _ lookup value)
  | app shape arg body ia ib =>
      obtain ⟨f, ty, head, lam, _⟩ := shape
      exact .app head lam (ia agree) (ib (bind_scalar agree))


theorem borrow_simulation (operand : Graph.borrowOperand g roles root = true)
    (agree : ReaderAgrees roles env x) : BorrowOperand g env root x := by
  cases shape : Graph.nodeAt g root <;> simp [Graph.borrowOperand, shape] at operand
  case var k => exact .reference shape (agree.1 k (by simpa using operand))
  case borrow a =>
    cases variableShape : Graph.nodeAt g a <;> simp [variableShape] at operand
    case var k => exact .borrowed shape variableShape (agree.2 k (by simpa using operand))

theorem reader_simulation (run : Graph.CoreReads g s token x roles root v es)
    (agree : ReaderAgrees roles env x) : CoreLexicalExecution.Reads g token x env root s v es := by
  induction run generalizing env with
  | scalar shape => exact .scalar shape
  | read shape operand bound active => exact .read shape (borrow_simulation operand agree) bound
  | strict shape a b ia ib => exact .strict shape (ia agree) (ib agree)
  | app shape lam ty a b ia ib => exact .app shape lam ty (ia agree) (ib (reader_scalar agree))
  | yes shape left right bound run ih => exact .yes shape left right bound (ih (reader_ghost agree))
  | no shape left right bound run ih => exact .no shape left right bound (ih agree)

theorem core_simulation (run : Exec g kind ctx root owners values s v es t)
    (agree : Agrees ctx owners values env) :
    Eval g env root s (resultValue kind v) es t := by
  induction run generalizing env with
  | finish resolved value =>
      rcases scalar_lookup agree resolved value with shape | ⟨k, shape, lookup⟩
      · exact .scalar shape
      · exact .var shape lookup
  | returnOwner resolved selected =>
      obtain ⟨k, shape, lookup⟩ := owner_lookup agree resolved selected
      exact .var shape lookup
  | free shape resolved selected run ih =>
      obtain ⟨k, variableShape, value⟩ := owner_lookup agree resolved selected
      exact .free shape variableShape value (ih (CoreLexicalContext.consumed agree selected))
  | allocate shape run ih =>
      obtain ⟨f, arg, domain, len, payload, app, lam, _, alloc, length, init⟩ := shape
      exact .app app lam (.allocate alloc length init) (ih (CoreLexicalContext.fresh agree))
  | lend shape resolved selected read run ih =>
      obtain ⟨k, variableShape, value⟩ := owner_lookup agree resolved selected
      exact .lend shape variableShape value (reader_simulation read (reader_roles agree selected))
        (ih (owned_returned agree selected))
  | scalarLend shape resolved selected read run ih =>
      obtain ⟨k, variableShape, value⟩ := owner_lookup agree resolved selected
      exact .scalarLend shape variableShape value (reader_simulation read (reader_roles agree selected))
        (ih (scalar_returned agree selected))
  | scalarLet shape computed run ih =>
      obtain ⟨f, ty, head, lam, _⟩ := shape
      exact .app head lam (pure_simulation computed agree) (ih (bind_scalar agree))
  | ownedLet shape resolved selected run ih =>
      obtain ⟨f, ty, head, lam, _⟩ := shape
      obtain ⟨k, variableShape, value⟩ := owner_lookup agree resolved selected
      exact .app head lam (.var variableShape value) (ih (transferred agree selected))

theorem framed_simulation (run : Evaluation g plan kind ctx root owners values s v es t)
    (agree : Agrees ctx owners values env) :
    Eval g env root s (resultValue kind v) es t := by
  induction run generalizing env with
  | core run => exact core_simulation run agree
  | apply shape arg body ia ib =>
      obtain ⟨f, ty, producerRoot, argRoot, head, lam, _, _⟩ := shape
      exact .app head lam (ia (producer agree)) (ib (CoreLexicalContext.body agree))
  | free shape resolved selected run ih =>
      obtain ⟨k, variableShape, value⟩ := owner_lookup agree resolved selected
      exact .free shape variableShape value (ih (CoreLexicalContext.consumed agree selected))
  | allocate shape run ih =>
      obtain ⟨f, arg, domain, len, payload, app, lam, _, alloc, length, init⟩ := shape
      exact .app app lam (.allocate alloc length init) (ih (CoreLexicalContext.fresh agree))
  | lend shape resolved selected read run ih =>
      obtain ⟨k, variableShape, value⟩ := owner_lookup agree resolved selected
      exact .lend shape variableShape value (reader_simulation read (reader_roles agree selected))
        (ih (owned_returned agree selected))
  | scalarLend shape resolved selected read run ih =>
      obtain ⟨k, variableShape, value⟩ := owner_lookup agree resolved selected
      exact .scalarLend shape variableShape value (reader_simulation read (reader_roles agree selected))
        (ih (scalar_returned agree selected))
  | scalarLet shape computed run ih =>
      obtain ⟨f, ty, head, lam, _⟩ := shape
      exact .app head lam (pure_simulation computed agree) (ih (bind_scalar agree))
  | ownedLet shape resolved selected run ih =>
      obtain ⟨f, ty, head, lam, _⟩ := shape
      obtain ⟨k, variableShape, value⟩ := owner_lookup agree resolved selected
      exact .app head lam (.var variableShape value) (ih (transferred agree selected))

/-- No agreement between plans is assumed: both produce the same lexical run. -/
theorem cross_plan_coherence
    (a : Evaluation g pa kind ctx root owners values s v es t)
    (b : Evaluation g pb kind ctx root owners values s w fs u) :
    v = w ∧ es = fs ∧ t = u := by
  obtain ⟨value, trace, state⟩ := Eval.deterministic
    (framed_simulation a materialize_agrees) (framed_simulation b materialize_agrees)
  exact ⟨resultValue_injective value, trace, state⟩

/-- A well-typed plan constructs a plan-free execution; success is not a premise. -/
theorem total (typed : Typing g plan kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) (agree : Agrees ctx owners values env) :
    ∃ v es t, Eval g env root s (resultValue kind v) es t := by
  obtain ⟨v, es, t, run⟩ := FramedOwnedApplications.total typed length scalarLength valid owned
  exact ⟨v, es, t, framed_simulation run agree⟩

/-- Every independent lexical execution is the constructed typed execution. -/
theorem reflects_execution (typed : Typing g plan kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) (agree : Agrees ctx owners values env)
    (run : Eval g env root s result es t) :
    ∃ v, result = resultValue kind v ∧ Evaluation g plan kind ctx root owners values s v es t := by
  obtain ⟨v, fs, u, execution⟩ := FramedOwnedApplications.total typed length scalarLength valid owned
  obtain ⟨rfl, rfl, rfl⟩ := Eval.deterministic run (framed_simulation execution agree)
  exact ⟨v, rfl, execution⟩

/-- Runtime bindings without static authority cannot affect a typed program. -/
theorem agreeing_environments_coherent (typed : Typing g plan kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners)
    (agree : Agrees ctx owners values env) (agree' : Agrees ctx owners values env')
    (a : Eval g env root s result es t) (b : Eval g env' root s result' es' t') :
    result = result' ∧ es = es' ∧ t = t' := by
  obtain ⟨v, fs, u, execution⟩ := FramedOwnedApplications.total typed length scalarLength valid owned
  obtain ⟨rfl, rfl, rfl⟩ := Eval.deterministic a (framed_simulation execution agree)
  obtain ⟨rfl, rfl, rfl⟩ := Eval.deterministic b (framed_simulation execution agree')
  exact ⟨rfl, rfl, rfl⟩

theorem every_run_safe (typed : Typing g plan kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) (agree : Agrees ctx owners values env)
    (run : Eval g env root s result es t) :
    Steps s es t ∧ Valid t ∧ ∃ v, result = resultValue kind v ∧ Owns t (resultOwners kind v) := by
  obtain ⟨v, value, execution⟩ := reflects_execution typed length scalarLength valid owned agree run
  obtain ⟨steps, finalValid, finalOwns⟩ := execution_safe typed length scalarLength valid owned execution
  exact ⟨steps, finalValid, v, value, finalOwns⟩

theorem every_run_heap_accounted (typed : Typing g plan kind ctx n m root)
    (length : owners.length = n) (scalarLength : values.length = m)
    (valid : Valid s) (owned : Owns s owners) (agree : Agrees ctx owners values env)
    (run : Eval g env root s result es t) (coverage : ∀ x, s.live x = true → x ∈ owners) :
    ∃ v, result = resultValue kind v ∧ (∀ x, t.live x = true ↔ x ∈ resultOwners kind v) := by
  obtain ⟨v, value, execution⟩ := reflects_execution typed length scalarLength valid owned agree run
  exact ⟨v, value, heap_accounted typed length scalarLength valid owned execution coverage⟩

theorem closed_total_accounted (typed : Typing g plan kind [] 0 0 root) :
    ∃ v es t, Eval g [] root empty (resultValue kind v) es t ∧
      Steps empty es t ∧ Valid t ∧ (∀ x, t.live x = true ↔ x ∈ resultOwners kind v) := by
  obtain ⟨v, es, t, run, steps, valid, accounted⟩ := FramedOwnedApplications.closed_total_accounted typed
  exact ⟨v, es, t, framed_simulation run materialize_agrees, steps, valid, accounted⟩

theorem closed_scalar_release (typed : Typing g plan .scalar [] 0 0 root)
    (run : Eval g [] root empty result es t) (allocated : x ∈ allocations es) :
    (released es).count x = 1 ∧ t.live x = false := by
  obtain ⟨v, _, execution⟩ := reflects_execution typed rfl rfl empty_valid empty_owns
    (show Agrees [] [] [] [] from materialize_agrees) run
  exact FramedOwnedApplications.closed_scalar_release typed execution allocated

end Jihoo.CoreLexicalSimulation
