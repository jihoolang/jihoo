import Jihoo.NativeAffineSum
import Jihoo.NativeInversion
import Jihoo.NativeModeSafety

/-! Typing preservation for the independent affine canonicalizer. This
uses the existing native judgment and conversion, with no new conversion rule.
Runtime overflow/evaluation boundaries are outside this theorem. -/
namespace Jihoo.NativeKernel.AffineSum

/-- All variable occurrences of a well-typed affine U64 expression are themselves
U64 in the same context, even when conversions occur inside its derivation. -/
theorem Expr.variable_typing {Γ : Context} {mode : Bool} {e : Expr}
    (h : HasType Γ mode e.toTerm .u64) :
    ∀ x ∈ e.variables, HasType Γ mode (.var x) .u64 := by
  induction e with
  | var i =>
      intro x hx
      simp only [Expr.variables, List.mem_singleton] at hx
      subst x
      exact h
  | literal n => simp [Expr.variables]
  | add a b ia ib =>
      obtain ⟨ha, hb, _⟩ := h.uaddView
      intro x hx
      simp only [Expr.variables, List.mem_append] at hx
      exact hx.elim (ia ha x) (ib hb x)

/-- Formation for the affine grammar uses ordinary UAdd and valid literal
leaves. It does not need a postulated affine conversion rule. -/
theorem Expr.hasType {Γ : Context} {mode : Bool} {e : Expr} (valid : e.Valid)
    (variables : ∀ x ∈ e.variables, HasType Γ mode (.var x) .u64) :
    HasType Γ mode e.toTerm .u64 := by
  induction e with
  | var x => exact variables x (by simp [Expr.variables])
  | literal n => exact .natural valid
  | add a b ia ib =>
      exact .uadd (ia valid.1 (fun x hx => variables x (by simp [Expr.variables, hx])))
        (ib valid.2 (fun x hx => variables x (by simp [Expr.variables, hx])))

private theorem naturalSum_hasType (Γ : Context) (mode : Bool) (n : Nat) :
    HasType Γ mode (naturalSum n).toTerm .u64 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      unfold naturalSum
      split
      · exact .natural (by assumption)
      · have positive : 2 ≤ wordLimit := by decide
        exact .uadd (ih (n/2) (by omega)) (ih (n-n/2) (by omega))

private theorem variable_fold_hasType {Γ : Context} {mode : Bool} (xs : List Nat) (acc : Expr)
    (ha : HasType Γ mode acc.toTerm .u64)
    (hx : ∀ x ∈ xs, HasType Γ mode (.var x) .u64) :
    HasType Γ mode (xs.foldl (fun t x => Expr.add t (.var x)) acc).toTerm .u64 := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x xs ih =>
      exact ih _ (.uadd ha (hx x (by simp))) (fun y hy => hx y (by simp [hy]))

theorem Form.emit_hasType {Γ : Context} {mode : Bool} (f : Form)
    (variables : ∀ x ∈ f.variables, HasType Γ mode (.var x) .u64) :
    HasType Γ mode f.emit .u64 := by
  cases f with
  | mk xs c =>
      cases xs with
      | nil => exact naturalSum_hasType Γ mode c
      | cons x xs =>
          have hv := variable_fold_hasType xs (.var x) (variables x (by simp))
            (fun y hy => variables y (by simp [hy]))
          change HasType Γ mode (if c = 0 then Form.variableTree x xs
            else Expr.add (Form.variableTree x xs) (naturalSum c)).toTerm .u64
          split
          · exact hv
          · exact .uadd hv (naturalSum_hasType Γ mode c)

/-- Canonicalization preserves the original type and mode, including arbitrary
trailing conversions. For code this is a typing theorem, not a claim about
runtime overflow behavior after reassociation. -/
theorem normalize_preservation {Γ : Context} {mode : Bool} {e : Expr} {T : Term}
    (valid : e.Valid) (h : HasType Γ mode e.toTerm T) :
    HasType Γ mode (normalize e).emit T := by
  cases e with
  | var x =>
      simpa [normalize, Expr.variables, Expr.constant, sortVariables, Form.emit,
        Form.emitExpr, Form.variableTree, Expr.toTerm] using h
  | literal n =>
      simp only [normalize, Expr.variables, Expr.constant, sortVariables, List.mergeSort_nil,
        Form.emit, Form.emitExpr]
      change n < wordLimit at valid
      rw [naturalSum]
      simp only [valid, ↓reduceIte, Expr.toTerm]
      exact h
  | add a b =>
      obtain ⟨ha, hb, target⟩ := h.uaddView
      apply HasType.convert _ target
      apply Form.emit_hasType
      intro x hx
      have mem := (sortVariables_perm (a.add b).variables).mem_iff.mp hx
      simp only [Expr.variables, List.mem_append] at mem
      exact mem.elim (Expr.variable_typing ha x) (Expr.variable_typing hb x)

/-- The executable native-tree adapter has actual type preservation, independent
of its mathematical evaluation theorem and the differential observations. -/
theorem canonical_preservation {Γ : Context} {mode : Bool} {t T : Term} {f : Form}
    (accepted : canonical t = some f) (typed : HasType Γ mode t T) :
    HasType Γ mode f.emit T := by
  obtain ⟨e, _, he, valid, rfl⟩ := canonical_spec accepted
  rw [← he] at typed
  exact normalize_preservation valid typed

/-- Mode-forgetting form used by the general native ghost metatheory. -/
theorem canonical_ghost_preservation {Γ : Context} {mode : Bool} {t T : Term} {f : Form}
    (accepted : canonical t = some f) (typed : HasType Γ mode t T) :
    HasType Γ true f.emit T := (canonical_preservation accepted typed).ghost

end Jihoo.NativeKernel.AffineSum
