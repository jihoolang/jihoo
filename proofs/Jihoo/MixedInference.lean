import Jihoo.MixedTelescopeBridge

/-! A total, proof-producing checker for the existing restricted bridge syntax.
It does not invoke or certify compiler/core.jh, and does not perform conversion. -/
namespace Jihoo.CoreBridge.Checked

deriving instance DecidableEq for Index
deriving instance DecidableEq for Ty

instance indexScopeDecidable (n : Nat) (a : Index) : Decidable (a.Scoped n) :=
  match a with
  | .var x => inferInstanceAs (Decidable (x < n))
  | .lit _ => isTrue trivial
  | .closedSub _ _ _ _ => isTrue trivial
  | .add a b => @instDecidableAnd _ _ (indexScopeDecidable n a) (indexScopeDecidable n b)

instance typeScopeDecidable (n : Nat) (A : Ty) : Decidable (A.Scoped n) :=
  match A with
  | .u64 | .i64 => isTrue trivial
  | .array a => indexScopeDecidable n a
  | .lt a b | .eq a b => inferInstanceAs (Decidable (a.Scoped n ∧ b.Scoped n))
  | .pi B => typeScopeDecidable (n + 1) B

abbrev Result (n : Nat) (Γ : List Ty) (t : Term) := { A : Ty // SourceTyping n Γ t A }

/-- Structurally recursive inference. Failure admits no evidence. In particular
`zeroLe` is rejected because the selected SourceTyping judgment has no rule for it.
Input numeric certificates are carried by Index/Term constructors, not invented. -/
def infer (n : Nat) (Γ : List Ty) (t : Term) : Option (Result n Γ t) :=
  match t with
  | .var x =>
      match h : Γ[x]? with
      | none => none
      | some A => if hs : A.Scoped n then some ⟨A, .var h hs⟩ else none
  | .natural a => if hs : a.Scoped n then some ⟨.u64, .natural hs⟩ else none
  | .integer _ => some ⟨.i64, .integer⟩
  | .elements xs => if h : xs.length < wordBound then
      some ⟨.array (.lit ⟨xs.length, h⟩), .elements xs h⟩ else none
  | .decide a b _ => some ⟨.lt (.lit a) (.lit b), .decide⟩
  | .refl a => if hs : a.Scoped n then some ⟨.eq a a, .refl hs⟩ else none
  | .zeroLe _ => none
  | .index a i p => do
      let ⟨A, ha⟩ ← infer n Γ a
      match hA : A with
      | .array len =>
          if hi : i.Scoped n then
            let ⟨P, hp⟩ ← infer n Γ p
            if he : P = .lt i len then
              some ⟨.i64, .index (hA ▸ ha) hi (he ▸ hp)⟩
            else none
          else none
      | _ => none
  | .lam body => do
      let ⟨B, hb⟩ ← infer (n + 1) (Γ.map (fun A => A.subst Index.shift)) body
      some ⟨.pi B, .lam hb⟩
  | .app f a => do
      let ⟨F, hf⟩ ← infer n Γ f
      match hF : F with
      | .pi B => if ha : a.Scoped n then
          some ⟨B.subst (Index.single a), .app (hF ▸ hf) ha⟩ else none
      | _ => none
  | .letValue A v body =>
      if hs : A.Scoped n then do
        let ⟨V, hv⟩ ← infer n Γ v
        if he : V = A then
          let ⟨B, hb⟩ ← infer n (A :: Γ) body
          some ⟨B, .letValue hs (he ▸ hv) hb⟩
        else none
      else none

/-- Completeness for precisely SourceTyping (not for jihoo's richer checker).
Proof irrelevance identifies the generated derivation with any input witness. -/
theorem infer_complete (h : SourceTyping n Γ t A) : infer n Γ t = some ⟨A, h⟩ := by
  induction h with
  | @var Γ x A n hx hs =>
      unfold infer
      split
      next he => simp [hx] at he
      next B he =>
        have same : B = A := Option.some.inj (he.symm.trans hx)
        subst B
        simp [hs]
  | natural hs => simp [infer, hs]
  | integer => rfl
  | elements xs h => simp [infer, h]
  | decide => rfl
  | refl hs => simp [infer, hs]
  | index ha hi hp iha ihp => simp [infer, iha, ihp, hi]
  | lam hb ih => simp [infer, ih]
  | app hf ha ih => simp [infer, ih, ha]
  | letValue hs hv hb ihv ihb => simp [infer, hs, ihv, ihb]

/-- Inferred types are observable without exposing proof objects. -/
def inferType (n : Nat) (Γ : List Ty) (t : Term) : Option Ty :=
  (infer n Γ t).map Subtype.val

theorem inferType_sound (h : inferType n Γ t = some A) : SourceTyping n Γ t A := by
  unfold inferType at h
  cases hi : infer n Γ t with
  | none => simp [hi] at h
  | some result =>
      simp only [hi, Option.map_some, Option.some.injEq] at h
      exact h ▸ result.property

theorem inferType_iff : inferType n Γ t = some A ↔ SourceTyping n Γ t A := by
  constructor
  · exact inferType_sound
  · intro h
    simp [inferType, infer_complete h]

/-- Exact annotation checking; no conversion is silently added. -/
def check (n : Nat) (Γ : List Ty) (t : Term) (A : Ty) : Bool :=
  inferType n Γ t == some A

theorem check_iff : check n Γ t A = true ↔ SourceTyping n Γ t A := by
  simp only [check, beq_iff_eq, inferType_iff]

theorem rejected_iff : inferType n Γ t = none ↔ ∀ A, ¬ SourceTyping n Γ t A := by
  constructor
  · intro h A ht
    have accepted := inferType_iff.mpr ht
    rw [h] at accepted
    contradiction
  · intro h
    cases hi : inferType n Γ t with
    | none => rfl
    | some A => exact False.elim (h A (inferType_sound hi))

theorem source_type_unique (h : SourceTyping n Γ t A) (k : SourceTyping n Γ t B) : A = B := by
  have ha := inferType_iff.mpr h
  have hb := inferType_iff.mpr k
  rw [ha] at hb
  exact Option.some.inj hb

/-- Acceptance with a constructed mixed context implies independently specified
Raw typing, with no source derivation supplied by the caller. -/
theorem accepted_raw {Γ : MixedBridge.Telescope}
    (h : inferType Γ.naturals Γ.proofs t = some A) :
    Raw.HasType Γ.context (t.encode Γ.indices Γ.values) (A.encode Γ.indices) :=
  MixedBridge.translate (inferType_sound h)

theorem accepted_closed {Γ : MixedBridge.Telescope} (wf : MixedBridge.WellFormed Γ)
    (h : inferType Γ.naturals Γ.proofs t = some A) :
    Raw.HasType (fun _ => none) (Γ.closeTerm (t.encode Γ.indices Γ.values))
      (Γ.closeType (A.encode Γ.indices)) :=
  MixedBridge.closed_translation wf (inferType_sound h)

theorem accepted_true {Γ : MixedBridge.Telescope} (wf : MixedBridge.WellFormed Γ)
    (hp : Indexed.Mixed.Proposition A.erase)
    (h : inferType Γ.naturals Γ.proofs t = some A)
    (hv : Indexed.Mixed.Valid Γ.erase ρ) : Indexed.Mixed.Holds A.erase ρ :=
  MixedBridge.semantic_sound wf hp (inferType_sound h) hv

/-- Closed accepted literal propositions are true, without any environment or
source derivation premise supplied by the caller. -/
theorem accepted_closed_bound (a b : Word)
    (h : inferType 0 [] t = some (.lt (.lit a) (.lit b))) : a.val < b.val := by
  obtain ⟨proof⟩ := (inferType_sound h).erases.realize (fun _ => 0) (Indexed.empty_valuation _)
  exact proof.down

theorem accepted_closed_equality (a b : Word)
    (h : inferType 0 [] t = some (.eq (.lit a) (.lit b))) : a.val = b.val := by
  obtain ⟨proof⟩ := (inferType_sound h).erases.realize (fun _ => 0) (Indexed.empty_valuation _)
  exact proof.down

end Jihoo.CoreBridge.Checked
