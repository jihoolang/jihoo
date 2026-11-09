import Jihoo.MixedTelescope

namespace Jihoo.Indexed.Mixed.Examples
open Arithmetic (Expr)

/-- n, p : n=n, m, q : m<n+1. Here p must shift across m. -/
def ctx : Telescope := .proof
  (.natural (.proof (.natural .empty) (.eq (.var 0) (.var 0))))
  (.lt (.var 0) (.add (.var 1) (.lit 1)))

theorem ctx_wellFormed : WellFormed ctx := by
  apply WellFormed.proof
  · exact .natural (.proof (.natural .empty) .eq ⟨by dsimp only [Term.Scoped, Expr.Scoped]; decide, by dsimp only [Term.Scoped, Expr.Scoped]; decide⟩)
  · exact .lt
  · exact ⟨by dsimp only [Term.Scoped, Expr.Scoped]; decide, ⟨by dsimp only [Term.Scoped, Expr.Scoped]; decide, trivial⟩⟩

/-- p still denotes the earlier n, not the intervening m. -/
theorem earlier_proof : Derives ctx (.param 1) (.eq (.var 1) (.var 1)) := by
  refine ⟨ctx_wellFormed, .eq, ctx_wellFormed.scoped, ?_, ?_, ?_⟩
  · dsimp only [Term.Scoped, Expr.Scoped]; decide
  · exact ⟨by dsimp only [Term.Scoped, Expr.Scoped]; decide, by dsimp only [Term.Scoped, Expr.Scoped]; decide⟩
  · exact .param _ 1

theorem valid_ctx (n m : Nat) (hm : m < n + 1) :
    Valid ctx (extendEnv (extendEnv (fun _ => 0) n) m) := by
  apply Valid.proof
  · apply Valid.natural
    exact .proof (.natural (.empty _)) ⟨⟨rfl⟩⟩
  · exact ⟨⟨hm⟩⟩

/-- An unbound proof cannot exploit the total context's default U64 entry. -/
theorem no_missing_proof : ¬ Derives .empty (.param 0) A := by
  intro h
  exact no_closed_parameter h.2.2

/-- The later natural m is unavailable when p is first introduced. -/
theorem no_forward_index :
    ¬ WellFormed (.proof (.natural .empty) (.eq (.var 1) (.var 1))) := by
  intro h
  cases h with
  | proof _ _ hs => exact Nat.lt_irrefl 1 hs.1

/-- Index shifting under the natural lambda prevents capture of the inserted
proof's free index, independently of the ambient proof namespace. -/
theorem proof_capture_avoiding :
    (Term.lam (.param 0)).valueSubst (singleValue (.refl (.var 0))) =
      .lam (.refl (.var 1)) := rfl

/-- Scalar replacement under a lambda preserves the new variable zero. -/
theorem scalar_capture_avoiding :
    (Term.lam (.refl (.add (.var 0) (.var 1)))).subst (single (.lit 7)) =
      .lam (.refl (.add (.var 0) (.lit 7))) := rfl

/-- Discharge a proof inserted between two natural binders. -/
theorem discharge_between_indices :
    Derives (.natural .empty)
      (.lam (.refl (.var 1))) (.pi (.eq (.var 1) (.var 1))) := by
  let Γ : Telescope := .natural .empty
  let P : Ty := .eq (.var 0) (.var 0)
  have wf : WellFormed Γ := .natural .empty
  have hp : ScopedTyping Γ.naturals Γ.proofs (.refl (.var 0)) P :=
    ⟨wf.scoped, by dsimp only [Term.Scoped, Expr.Scoped]; decide, ⟨by dsimp only [Term.Scoped, Expr.Scoped]; decide, by dsimp only [Term.Scoped, Expr.Scoped]; decide⟩, .refl _ _⟩
  have source : Derives (.proof Γ P) (.lam (.param 0))
      (.pi (.eq (.var 1) (.var 1))) := by
    refine ⟨.proof wf .eq ⟨by dsimp only [Term.Scoped, Expr.Scoped]; decide, by dsimp only [Term.Scoped, Expr.Scoped]; decide⟩, .all .eq, ?_, ?_, ?_, ?_⟩
    · exact (WellFormed.proof wf Proposition.eq ⟨by dsimp only [Term.Scoped, Expr.Scoped]; decide, by dsimp only [Term.Scoped, Expr.Scoped]; decide⟩).scoped
    · dsimp only [Term.Scoped, Expr.Scoped]; decide
    · exact ⟨by dsimp only [Term.Scoped, Expr.Scoped]; decide, by dsimp only [Term.Scoped, Expr.Scoped]; decide⟩
    · exact .lam (.param _ 0)
  exact source.substitution (proof_instantiation wf hp)

/-- Discharge n after the proof substitution, retaining m and its scope. -/
theorem discharge_both :
    Derives .empty (.lam (.refl (.lit 7))) (.pi (.eq (.lit 7) (.lit 7))) :=
  discharge_between_indices.substitution
    (natural_instantiation WellFormed.empty (a := .lit 7) trivial)

end Jihoo.Indexed.Mixed.Examples
