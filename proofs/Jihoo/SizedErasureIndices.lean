import Jihoo.SizedErasedRuntime
import Jihoo.SizedCorePure

/-! Static lexical compaction of natural and scalar graph expressions. A false
mask entry has no target slot; retained variable references count only earlier
runtime entries. This is not a value-dependent substitution. -/
namespace Jihoo.SizedErasure
open ScopedLend

inductive EraseNat : Mask → DependentBufferIndices.Expr → NatTerm → Prop where
  | literal : EraseNat mask (.literal n) (.literal n)
  | var : mask[k]? = some true → EraseNat mask (.var k) (.var (rank mask k))
  | letE : EraseNat mask a ea → EraseNat (true :: mask) b eb →
      EraseNat mask (.letE a b) (.letE ea eb)

def NatErases (g : Graph.Graph) (mask : Mask) (root : Nat) (term : NatTerm) : Prop :=
  ∃ e, DependentBufferIndices.Represents g root e ∧ EraseNat mask e term

inductive ScalarErases (g : Graph.Graph) (mask : Mask) : Nat → ScalarTerm → Prop where
  | literal : Graph.nodeAt g root = .integer v → ScalarErases g mask root (.literal v)
  | var : Graph.nodeAt g root = .var k → mask[k]? = some true →
      ScalarErases g mask root (.var (rank mask k))

private theorem runtimeNats_cons :
    SizedBufferContext.runtimeNats (SizedBufferContext.Value.nat n :: env) =
      DependentBufferIndices.push n (SizedBufferContext.runtimeNats env) := by
  funext k
  cases k <;> simp [SizedBufferContext.runtimeNats, DependentBufferIndices.push]

theorem EraseNat.forward (erased : EraseNat mask source target)
    (related : EnvRel mask env runtime)
    (run : source.eval (SizedBufferContext.runtimeNats env) = some n) :
    NatEval runtime target n := by
  induction erased generalizing env runtime n with
  | literal =>
      simp only [DependentBufferIndices.Expr.eval, Option.some.injEq] at run
      subst n
      exact .literal
  | @var mask k retained =>
      have lookup : env[k]? = some (SizedBufferContext.Value.nat n) := by
        cases h : env[k]? with
        | none => simp [SizedBufferContext.runtimeNats, DependentBufferIndices.Expr.eval, h] at run
        | some v => cases v <;> simp_all [SizedBufferContext.runtimeNats, DependentBufferIndices.Expr.eval]
      exact .var ((related.retained_lookup_iff retained).mp lookup)
  | @letE mask a ea b eb first last ihf ihl =>
      simp only [DependentBufferIndices.Expr.eval] at run
      cases h : DependentBufferIndices.Expr.eval (SizedBufferContext.runtimeNats env) a with
      | none => simp [h] at run
      | some v =>
          simp [h] at run
          exact .letE (ihf related h)
            (ihl (related.consKeep _) (by simpa only [Value.embed, runtimeNats_cons] using run))

theorem EraseNat.backward (erased : EraseNat mask source target)
    (related : EnvRel mask env runtime) (run : NatEval runtime target n) :
    source.eval (SizedBufferContext.runtimeNats env) = some n := by
  induction erased generalizing env runtime n with
  | literal => cases run; rfl
  | @var mask k retained =>
      cases run with
      | var lookup =>
          have original := (related.retained_lookup_iff retained).mpr lookup
          simp [DependentBufferIndices.Expr.eval, SizedBufferContext.runtimeNats, original, Value.embed]
  | letE first last ihf ihl =>
      cases run with
      | letE argument body =>
          have firstRun := ihf related argument
          have lastRun := ihl (related.consKeep _) body
          simpa [DependentBufferIndices.Expr.eval, firstRun, Value.embed, runtimeNats_cons] using lastRun

theorem NatErases.forward (erased : NatErases g mask root target)
    (related : EnvRel mask env runtime)
    (run : DependentBufferIndices.Eval g (SizedBufferContext.runtimeNats env) root n) :
    NatEval runtime target n := by
  obtain ⟨e, shape, compaction⟩ := erased
  obtain ⟨e', shape', value⟩ := run
  obtain rfl := shape.unique shape'
  exact compaction.forward related value

theorem NatErases.backward (erased : NatErases g mask root target)
    (related : EnvRel mask env runtime) (run : NatEval runtime target n) :
    DependentBufferIndices.Eval g (SizedBufferContext.runtimeNats env) root n := by
  obtain ⟨e, shape, compaction⟩ := erased
  exact ⟨e, shape, compaction.backward related run⟩

theorem ScalarErases.forward (erased : ScalarErases g mask root target)
    (related : EnvRel mask env runtime) (run : SizedCoreExecution.Scalar g env root v) :
    ScalarEval runtime target v := by
  cases erased with
  | literal shape =>
      cases run with
      | literal other => have eq := shape.symm.trans other; cases eq; exact .literal
      | var other _ => have eq := shape.symm.trans other; contradiction
  | var shape retained =>
      cases run with
      | literal other => have eq := shape.symm.trans other; contradiction
      | var other lookup =>
          have eq := shape.symm.trans other; cases eq
          exact .var ((related.retained_lookup_iff retained).mp lookup)

theorem ScalarErases.backward (erased : ScalarErases g mask root target)
    (related : EnvRel mask env runtime) (run : ScalarEval runtime target v) :
    SizedCoreExecution.Scalar g env root v := by
  cases erased with
  | literal shape => cases run; exact .literal shape
  | var shape retained =>
      cases run with
      | var lookup => exact .var shape ((related.retained_lookup_iff retained).mpr lookup)

end Jihoo.SizedErasure
