import Jihoo.SizedCoreExecution

/-! The executable U64 index fragment is genuine ordinary graph evaluation:
its successful mathematical index interpretation produces the same natural
value without allocating, reading, freeing, or changing the sized heap. -/
namespace Jihoo.SizedCoreExecution
open ScopedLend SizedBufferContext
open DependentBufferIndices (Represents)

theorem runtimeNats_lookup (value : runtimeNats env k = some n) : env[k]? = some (.nat n) := by
  cases h : env[k]? with
  | none => simp [runtimeNats, h] at value
  | some v =>
      cases v <;> simp [runtimeNats, h] at value
      subst n; rfl

theorem runtimeNats_push : runtimeNats (.nat n :: env) = DependentBufferIndices.push n (runtimeNats env) := by
  funext k; cases k <;> rfl

theorem index_simulation (run : DependentBufferIndices.Eval g (runtimeNats env) root n) :
    Eval g env root s (.nat n) [] s := by
  obtain ⟨e, represented, value⟩ := run
  induction represented generalizing env n s with
  | literal shape bound =>
      simp [DependentBufferIndices.Expr.eval] at value
      subst n
      exact .natural shape
  | var shape =>
      apply Eval.var shape
      exact runtimeNats_lookup value
  | @letE rt f arg ty body ea eb shape lam u64 a b ia ib =>
      simp only [DependentBufferIndices.Expr.eval] at value
      cases evaluated : ea.eval (runtimeNats env) with
      | none => simp [evaluated] at value
      | some v =>
          have rest : eb.eval (runtimeNats (.nat v :: env)) = some n := by
            simpa [evaluated, runtimeNats_push] using value
          exact .app shape lam (ia evaluated) (ib rest)

end Jihoo.SizedCoreExecution
