import Jihoo.CheckedFirstOrderApplication

/-! Higher-order evidence over closed natural propositions. Context entries are
proofs, never natural indices or function-valued runtime data. This is a separate
semantic judgment, not a soundness assumption about unrestricted Beta.Conv. -/
namespace Jihoo.CoreBridge.PropositionalEvidence
open LinearNaturals LinearEvidence CorePrincipal

inductive Ty where
  | atom : Formula 0 → Ty
  | arrow : Ty → Ty → Ty

def Ty.encode : Ty → Raw
  | .atom p => p.encode
  | .arrow A B => .pi true A.encode B.encode

def Ty.Holds : Ty → Prop
  | .atom p => ∀ ρ, p.Holds ρ
  | .arrow A B => A.Holds → B.Holds

private theorem expr_subst_identity (e : Expr n) (σ : Nat → Raw)
    (h : ∀ x : Fin n, σ x.val = .var x.val) : e.encode.subst σ = e.encode := by
  induction e with
  | var x => simpa only [Expr.encode, Raw.subst] using h x
  | lit => simp only [Expr.encode, Raw.subst]
  | add _ _ ha hb => simp only [Expr.encode, Raw.subst, ha, hb]

private theorem formula_subst_identity (p : Formula n) (σ : Nat → Raw)
    (h : ∀ x : Fin n, σ x.val = .var x.val) : p.encode.subst σ = p.encode := by
  induction p generalizing σ with
  | equal a b => simp only [Formula.encode, Raw.subst, expr_subst_identity _ _ h]
  | less a b => simp only [Formula.encode, Raw.subst, expr_subst_identity _ _ h]
  | all p ih =>
      simp only [Formula.encode, Raw.subst]
      congr 1
      apply ih
      intro x
      refine Fin.cases ?_ (fun y => ?_) x
      · rfl
      · simp only [Fin.val_succ, Raw.liftSub, h, Raw.rename]

/-- Proof assumptions cannot occur as natural indices in any admitted type.
In particular the codomain of a proof arrow is unchanged by proof substitution. -/
theorem Ty.subst_closed (A : Ty) (σ : Nat → Raw) : A.encode.subst σ = A.encode := by
  induction A generalizing σ with
  | atom p => exact formula_subst_identity p σ (fun x => Fin.elim0 x)
  | arrow A B ha hb => simp only [encode, Raw.subst, ha, hb]

private theorem formula_proposition (p : Formula n) : p.encode.proposition = true := by
  induction p with
  | equal => rfl
  | less => rfl
  | all p ih => exact ih

theorem Ty.proposition (A : Ty) : A.encode.proposition = true := by
  induction A with
  | atom p => exact formula_proposition p
  | arrow _ _ _ ih => exact ih

/-- All admitted closed proposition types are formed in the pre-existing Beta
model, in any surrounding raw context. No term-typing/Conv soundness is inferred. -/
theorem Ty.formed (A : Ty) (Γ : Raw.Context) : Raw.Beta.IsType Γ A.encode := by
  induction A generalizing Γ with
  | atom p =>
      have h : Raw.Renaming (context 0) Γ id := by
        intro x B hx
        simp [context] at hx
      simpa only [Ty.encode, Raw.rename_id] using p.formed.renaming h
  | arrow A B ha hb =>
      exact .pi (ha Γ) (by rw [A.proposition]) (hb (Γ.extend A.encode))

inductive Converts : Ty → Ty → Prop where
  | atom : LinearEvidence.Converts p q → Converts (.atom p) (.atom q)
  | arrow : Converts A C → Converts B D → Converts (.arrow A B) (.arrow C D)

theorem Converts.sound (h : Converts A B) : A.Holds ↔ B.Holds := by
  induction h with
  | atom h => exact forall_congr' (fun ρ => h.sound ρ)
  | arrow _ _ ha hb => exact imp_congr ha hb

def conversion : (A B : Ty) → Option (PLift (Converts A B))
  | .atom p, .atom q => do
      let h ← LinearEvidence.conversion p q
      pure ⟨.atom h.down⟩
  | .arrow A B, .arrow C D => do
      let ha ← conversion A C
      let hb ← conversion B D
      pure ⟨.arrow ha.down hb.down⟩
  | _, _ => none

def parse : (A : Raw) → Option {p : Ty // p.encode = A}
  | .pi true A B => do
      let a ← parse A
      let b ← parse B
      pure ⟨.arrow a.val b.val, by simp only [Ty.encode, a.property, b.property]⟩
  | A => do
      let p ← parseFormula 0 A
      pure ⟨.atom p.val, p.property⟩

inductive Derives : List Ty → Raw → Ty → Prop where
  | base : Principal t p → Derives Γ t (.atom p)
  | hyp : Γ[k]? = some A → Derives Γ (.var k) A
  | lam : Derives (A :: Γ) t B → Derives Γ (.lam true A.encode t) (.arrow A B)
  | app : Derives Γ f (.arrow A B) → Derives Γ a A → Derives Γ (.app f a) B
  | index : Derives Γ f (.atom (.all p)) → (a : Expr 0) →
      Derives Γ (.app f a.encode) (.atom (p.instantiate a))
  | convert : Derives Γ t A → Converts A B → Derives Γ t B

def Valid (Γ : List Ty) : Prop := ∀ (k : Nat) (A : Ty), Γ[k]? = some A → A.Holds

theorem Derives.sound (h : Derives Γ t A) (valid : Valid Γ) : A.Holds := by
  induction h with
  | base h => exact h.derives.sound
  | hyp h => exact valid _ _ h
  | lam _ ih =>
      intro hA
      apply ih
      intro k B hk
      cases k with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst B; exact hA
      | succ k => exact valid k B hk
  | app _ _ hf ha => exact hf valid (ha valid)
  | index _ a hf =>
      intro ρ
      exact (Formula.holds_instantiate _ _ _).mpr (hf valid ρ (a.eval ρ))
  | convert _ hc ih => exact hc.sound.mp (ih valid)

theorem Derives.closed_sound (h : Derives [] t A) : A.Holds :=
  h.sound (by intro k A hk; simp at hk)

structure Result (Γ : List Ty) (t : Raw) (budget : Nat) where
  type : Ty
  remaining : Nat
  derives : Derives Γ t type
  remaining_le : remaining ≤ budget

/-- Fuel bounds recursion; budget counts visits and conservative substitution
work. The artifact endpoint also bounds all graph/tree expansion beforehand. -/
def infer : Nat → (budget : Nat) → (Γ : List Ty) → (t : Raw) → Option (Result Γ t budget)
  | 0, _, _, _ => none
  | _ + 1, 0, _, _ => none
  | _ + 1, budget + 1, Γ, .var k => do
      match h : Γ[k]? with
      | some A => pure ⟨A, budget, .hyp h, Nat.le_succ _⟩
      | none => none
  | fuel + 1, budget + 1, Γ, .lam true A t => do
      let a ← parse A
      let body ← infer fuel budget (a.val :: Γ) t
      if GraphCertificates.Typing.rawSize A +
          GraphCertificates.Typing.rawSize body.type.encode + 1 > 8192 then none else
        pure ⟨.arrow a.val body.type, body.remaining,
          by simpa only [a.property] using Derives.lam body.derives,
          Nat.le_trans body.remaining_le (Nat.le_succ _)⟩
  | fuel + 1, budget + 1, Γ, .app f a => do
      let function ← infer fuel budget Γ f
      match h : function.type with
      | .arrow A B => do
          let argument ← infer fuel function.remaining Γ a
          let hc ← conversion argument.type A
          pure ⟨B, argument.remaining, .app (by simpa only [h] using function.derives)
            (.convert argument.derives hc.down),
            Nat.le_trans argument.remaining_le (Nat.le_trans function.remaining_le (Nat.le_succ _))⟩
      | .atom (.all p) => do
          let argument ← extract 0 a
          let cost := (GraphCertificates.Typing.rawSize p.encode + 1) *
            (GraphCertificates.Typing.rawSize a + 1)
          if !(GraphCertificates.FirstOrderApplication.substitutionSafe p.encode a) ||
              cost > function.remaining then none else
            pure ⟨.atom (p.instantiate argument.val), function.remaining - cost,
              by simpa only [argument.property] using
                Derives.index (by simpa only [h] using function.derives) argument.val,
              Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans function.remaining_le (Nat.le_succ _))⟩
      | _ => none
  | _ + 1, budget + 1, Γ, t => do
      let p ← CorePrincipal.infer 0 t
      pure ⟨.atom p.val, budget, .base p.property, Nat.le_succ _⟩

end Jihoo.CoreBridge.PropositionalEvidence
