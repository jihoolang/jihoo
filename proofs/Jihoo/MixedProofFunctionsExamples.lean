import Jihoo.MixedProofFunctions

namespace Jihoo.MixedProofFunctions.Examples
open Arithmetic (Expr)

def same : Formula := .eq (.var 0) (.var 0)
def retain : Term := .naturalLam (.proofLam same (.naturalLam (.hyp 0)))

theorem retain_typed : Derives 0 [] retain
    (.all (.arrow same (.all (.eq (.var 1) (.var 1))))) := by
  apply Derives.naturalLam
  apply Derives.proofLam (A := same) (n := 1) ⟨by dsimp [Expr.Scoped]; decide, by dsimp [Expr.Scoped]; decide⟩
  apply Derives.naturalLam
  exact .hyp rfl ⟨by dsimp [Expr.Scoped]; decide, by dsimp [Expr.Scoped]; decide⟩

def higher : Term := .naturalLam (.proofLam (.arrow same same)
  (.proofLam same (.proofApp (.hyp 1) (.hyp 0))))

theorem higher_typed : Derives 0 [] higher (.all (.arrow (.arrow same same) (.arrow same same))) := by
  have hs : same.Scoped 1 := ⟨by dsimp [Expr.Scoped]; decide, by dsimp [Expr.Scoped]; decide⟩
  exact .naturalLam (.proofLam ⟨hs, hs⟩ (.proofLam hs (.proofApp (.hyp rfl ⟨hs, hs⟩) (.hyp rfl hs))))

theorem proof_beta_capture_safe :
    Derives 1 [] (.naturalLam (.refl (.var 1))) (.all (.eq (.var 1) (.var 1))) := by
  have body : Derives 1 [same] (.naturalLam (.hyp 0)) (.all (.eq (.var 1) (.var 1))) :=
    .naturalLam (.hyp rfl ⟨by dsimp [Expr.Scoped]; decide, by dsimp [Expr.Scoped]; decide⟩)
  exact proof_beta body (.refl (a := .var 0) (by dsimp [Expr.Scoped]; decide)) (by simp)

theorem scalar_beta_capture_safe :
    Derives 0 [] (.naturalLam (.refl (.lit 7))) (.all (.eq (.lit 7) (.lit 7))) :=
  natural_beta (n := 0) (Γ := []) proof_beta_capture_safe (a := .lit 7) trivial

theorem nested_proof_capture_safe :
    (Term.proofLam same (.proofApp (.hyp 1) (.hyp 0))).proofSubst
      (singleProof (.hyp 0)) = .proofLam same (.proofApp (.hyp 1) (.hyp 0)) := rfl

theorem universal_argument : Derives 0 []
    (.proofLam (.all same) (.naturalLam (.naturalApp (.hyp 0) (.var 0))))
    (.arrow (.all same) (.all same)) := by
  apply Derives.proofLam
  · exact ⟨by dsimp [Expr.Scoped]; decide, by dsimp [Expr.Scoped]; decide⟩
  · apply Derives.naturalLam
    apply Derives.naturalApp (B := same)
    · exact .hyp rfl ⟨by dsimp [Expr.Scoped]; decide, by dsimp [Expr.Scoped]; decide⟩
    · dsimp [Expr.Scoped]; decide

theorem retain_true : Formula.Holds (fun _ => 0)
    (.all (.arrow same (.all (.eq (.var 1) (.var 1))))) :=
  retain_typed.sound (by intro x P hx; simp at hx)

theorem no_missing_hypothesis : ¬ Derives 0 [] (.hyp 0) A := by
  intro h
  cases h with
  | hyp hx _ => simp at hx

theorem no_forward_scalar : ¬ Derives 0 [] (.proofLam same (.hyp 0)) (.arrow same same) := by
  intro h
  cases h with
  | proofLam hs _ => exact Nat.lt_irrefl 0 hs.1

end Jihoo.MixedProofFunctions.Examples
