import Jihoo.MixedProofFunctions
import Jihoo.CoreBridgeBetaTyping

/-! A forward bridge for mixed proof functions. Bounds/no-subtraction admission
is explicit; the target is the independent ghost Raw.Beta typing judgment. -/
namespace Jihoo.MixedProofFunctions.Bridge
open Arithmetic (Expr)
open CoreBridge (Raw wordBound)
open Indexed (liftRenaming shift lift single)

def index (ix : Nat → Nat) : Expr → Raw
  | .var x => .var (ix x)
  | .lit n => .natural n
  | .add a b => .uadd (index ix a) (index ix b)
  | .sub a b => .usub (index ix a) (index ix b)
      (.decide (index ix b) (.uadd (index ix a) (.natural 1)))

/-- The total encoding's subtraction branch has no typing guarantee. Every
admitted expression excludes it; no arithmetic premise is manufactured. -/
def IndexAdmitted : Expr → Prop
  | .var _ => True
  | .lit n => n < wordBound
  | .add a b => IndexAdmitted a ∧ IndexAdmitted b
  | .sub _ _ => False

def formula (ix : Nat → Nat) : Formula → Raw
  | .eq a b => .eq (index ix a) (index ix b)
  | .lt a b => .lt (index ix a) (index ix b)
  | .all B => .pi false .u64 (formula (liftRenaming ix) B)
  | .arrow A B => .pi true (formula ix A) (formula (fun x => ix x + 1) B)

def FormulaAdmitted : Formula → Prop
  | .eq a b | .lt a b => IndexAdmitted a ∧ IndexAdmitted b
  | .all B => FormulaAdmitted B
  | .arrow A B => FormulaAdmitted A ∧ FormulaAdmitted B

def term (ix px : Nat → Nat) : Term → Raw
  | .hyp x => .var (px x)
  | .refl a => .refl (index ix a)
  | .decide m n => .decide (.natural m) (.natural n)
  | .zeroLe a => .zeroLe (index ix a)
  | .naturalLam t => .lam false .u64 (term (liftRenaming ix) (fun x => px x + 1) t)
  | .naturalApp f a => .app (term ix px f) (index ix a)
  | .proofLam A t => .lam true (formula ix A)
      (term (fun x => ix x + 1) (liftRenaming px) t)
  | .proofApp f a => .app (term ix px f) (term ix px a)

def TermAdmitted : Term → Prop
  | .hyp _ => True
  | .refl a | .zeroLe a => IndexAdmitted a
  | .decide m n => m < wordBound ∧ n < wordBound
  | .naturalLam t => TermAdmitted t
  | .naturalApp f a => TermAdmitted f ∧ IndexAdmitted a
  | .proofLam A t => FormulaAdmitted A ∧ TermAdmitted t
  | .proofApp f a => TermAdmitted f ∧ TermAdmitted a

theorem index_rename (a : Expr) (ix ρ : Nat → Nat) :
    (index ix a).rename ρ = index (fun x => ρ (ix x)) a := by
  induction a <;> simp_all [index, Raw.rename]

theorem formula_rename (A : Formula) (ix ρ : Nat → Nat) :
    (formula ix A).rename ρ = formula (fun x => ρ (ix x)) A := by
  induction A generalizing ix ρ with
  | eq => simp [formula, Raw.rename, index_rename]
  | lt => simp [formula, Raw.rename, index_rename]
  | all B ih =>
      simp only [formula, Raw.rename, ih]
      congr 2
      funext x
      cases x <;> rfl
  | arrow A B ha hb => simp [formula, Raw.rename, ha, hb, liftRenaming]

theorem index_subst (a : Expr) (σ : Indexed.Substitution) (ix jx : Nat → Nat)
    (τ : Nat → Raw) (hs : ∀ x, index ix (σ x) = τ (jx x)) :
    index ix (a.subst σ) = (index jx a).subst τ := by
  induction a <;> simp_all [index, Expr.subst, Raw.subst]

theorem index_shift (a : Expr) (ix : Nat → Nat) :
    index (liftRenaming ix) (a.subst shift) = (index ix a).rename Nat.succ := by
  induction a <;> simp_all [Expr.subst, shift, index, Raw.rename, liftRenaming]

theorem formula_subst (A : Formula) (σ : Indexed.Substitution) (ix jx : Nat → Nat)
    (τ : Nat → Raw) (hs : ∀ x, index ix (σ x) = τ (jx x)) :
    formula ix (A.subst σ) = (formula jx A).subst τ := by
  induction A generalizing σ ix jx τ with
  | eq => simp [Formula.subst, formula, Raw.subst, index_subst _ _ _ _ _ hs]
  | lt => simp [Formula.subst, formula, Raw.subst, index_subst _ _ _ _ _ hs]
  | all B ih =>
      simp only [Formula.subst, formula, Raw.subst]
      congr 1
      apply ih
      intro x
      cases x with
      | zero => rfl
      | succ x => simpa only [lift, liftRenaming, Raw.liftSub, index_shift] using
          congrArg (fun r : Raw => r.rename Nat.succ) (hs x)
  | arrow A B ha hb =>
      simp only [Formula.subst, formula, Raw.subst]
      congr 1
      · exact ha σ ix jx τ hs
      · apply hb
        intro x
        simpa only [index_rename, Raw.liftSub] using
          congrArg (fun r : Raw => r.rename Nat.succ) (hs x)

theorem formula_shift (A : Formula) (ix : Nat → Nat) :
    formula (liftRenaming ix) (A.subst shift) = (formula ix A).rename Nat.succ := by
  rw [formula_subst A shift (liftRenaming ix) ix (fun x => .var (x + 1)) (by intro x; rfl)]
  simpa only [Raw.subst_id, Raw.rename] using
    (Raw.rename_subst (formula ix A) Raw.var Nat.succ).symm

theorem formula_instantiate (A : Formula) (a : Expr) (ix : Nat → Nat) :
    formula ix (A.subst (single a)) =
      (formula (liftRenaming ix) A).subst (Raw.single (index ix a)) := by
  apply formula_subst
  intro x
  cases x <;> rfl

theorem formula_drop_proof (A : Formula) (v : Raw) (ix : Nat → Nat) :
    (formula (fun x => ix x + 1) A).subst (Raw.single v) = formula ix A := by
  rw [← formula_rename A ix Nat.succ]
  exact Raw.subst_shift _ _

theorem formula_proposition (A : Formula) (ix : Nat → Nat) :
    (formula ix A).proposition = true := by
  induction A generalizing ix <;> simp_all [formula, Raw.proposition]

/-- Lookup correspondence only; this premise never assumes target typing. -/
def ContextMatch (n : Nat) (Γ : List Formula) (Δ : Raw.Context) (ix px : Nat → Nat) : Prop :=
  (∀ x, x < n → Δ (ix x) = some .u64) ∧
  (∀ x A, Γ[x]? = some A → Δ (px x) = some (formula ix A))

theorem ContextMatch.natural (h : ContextMatch n Γ Δ ix px) :
    ContextMatch (n + 1) (Γ.map (fun A => A.subst shift)) (Δ.extend .u64)
      (liftRenaming ix) (fun x => px x + 1) := by
  constructor
  · intro x hx
    cases x with
    | zero => simp [liftRenaming, Raw.Context.extend, Raw.rename]
    | succ x => simp [liftRenaming, Raw.Context.extend, h.1 x (by omega), Raw.rename]
  · intro x A hx
    simp only [List.getElem?_map] at hx
    cases he : Γ[x]? with
    | none => simp [he] at hx
    | some B =>
        simp only [he, Option.map_some, Option.some.injEq] at hx
        subst A
        simp [Raw.Context.extend, h.2 x B he, formula_shift]

theorem ContextMatch.proof (h : ContextMatch n Γ Δ ix px) (A : Formula) :
    ContextMatch n (A :: Γ) (Δ.extend (formula ix A))
      (fun x => ix x + 1) (liftRenaming px) := by
  constructor
  · intro x hx
    simp [Raw.Context.extend, h.1 x hx, Raw.rename]
  · intro x B hx
    cases x with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst B
        simp [liftRenaming, Raw.Context.extend, formula_rename]
    | succ x => simp [liftRenaming, Raw.Context.extend, h.2 x B hx, formula_rename]

theorem index_typed (a : Expr) (hs : a.Scoped n) (ha : IndexAdmitted a)
    (hi : ∀ x, x < n → Δ (ix x) = some .u64) : Raw.Beta.HasType Δ (index ix a) .u64 := by
  induction a with
  | var x => exact .var (hi x hs)
  | lit k => exact .natural ha
  | add a b h₁ h₂ => exact .uadd (h₁ hs.1 ha.1) (h₂ hs.2 ha.2)
  | sub => exact False.elim ha

theorem formula_formed (A : Formula) (hs : A.Scoped n) (ha : FormulaAdmitted A)
    (hi : ∀ x, x < n → Δ (ix x) = some .u64) : Raw.Beta.IsType Δ (formula ix A) := by
  induction A generalizing n Δ ix with
  | eq a b => exact .eq (index_typed a hs.1 ha.1 hi) (index_typed b hs.2 ha.2 hi)
  | lt a b => exact .lt (index_typed a hs.1 ha.1 hi) (index_typed b hs.2 ha.2 hi)
  | all B ih =>
      apply Raw.Beta.IsType.pi .u64 rfl
      apply ih hs ha
      intro x hx
      cases x with
      | zero => simp [liftRenaming, Raw.Context.extend, Raw.rename]
      | succ x => simp [liftRenaming, Raw.Context.extend, hi x (by omega), Raw.rename]
  | arrow A B ha' hb =>
      apply Raw.Beta.IsType.pi (ha' hs.1 ha.1 hi) (formula_proposition A ix).symm
      apply hb hs.2 ha.2
      intro x hx
      simp [Raw.Context.extend, hi x hx, Raw.rename]

theorem translate (h : Derives n Γ t A) (ht : TermAdmitted t)
    (hc : ContextMatch n Γ Δ ix px) : Raw.Beta.HasType Δ (term ix px t) (formula ix A) := by
  induction h generalizing Δ ix px with
  | hyp hx _ => exact .var (hc.2 _ _ hx)
  | refl hs => exact .refl (index_typed _ hs ht hc.1)
  | decide bound => exact .decide ht.1 ht.2 bound
  | zeroLe hs => exact .zeroLe (index_typed _ hs ht hc.1)
  | naturalLam _ ih => exact .lam .u64 rfl (ih ht hc.natural)
  | @naturalApp n Γ f B a hf hs ih =>
      rw [formula_instantiate]
      exact .app (ih ht.1 hc) (index_typed a hs ht.2 hc.1)
  | @proofLam n A Γ body B hs hb ih =>
      exact .lam (formula_formed A hs ht.1 hc.1) (formula_proposition A ix).symm
        (ih ht.2 (hc.proof A))
  | @proofApp n Γ f A B a hf ha ihf iha =>
      have h := Raw.Beta.HasType.app (ihf ht.1 hc) (iha ht.2 hc)
      simpa only [formula, formula_drop_proof, term] using h

theorem translate_closed (h : Derives 0 [] t A) (ht : TermAdmitted t) :
    Raw.Beta.HasType (fun _ => none) (term id id t) (formula id A) :=
  translate h ht ⟨by intro x hx; omega, by intro x P hx; simp at hx⟩

end Jihoo.MixedProofFunctions.Bridge
