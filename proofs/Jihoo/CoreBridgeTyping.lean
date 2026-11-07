import Jihoo.CoreBridgeLayout

/-! A restricted typed bridge. The target judgment is defined on unified `Raw`
syntax alone, independently of the source syntax and its translation. It is a
universe-free, ghost-mode declarative fragment, not the executable graph checker.
Source conversion and `zeroLe` are deliberately absent. -/
namespace Jihoo.CoreBridge

open Indexed (liftRenaming)

namespace Raw

/-- Both index and value binders use the same capture-avoiding substitution. -/
def liftSub (σ : Nat → Raw) : Nat → Raw
  | 0 => .var 0
  | n + 1 => (σ n).rename Nat.succ

def single (a : Raw) : Nat → Raw
  | 0 => a
  | n + 1 => .var n

def subst (σ : Nat → Raw) : Raw → Raw
  | .var x => σ x
  | .natural n => .natural n
  | .integer n => .integer n
  | .u64 => .u64
  | .i64 => .i64
  | .array n => .array (n.subst σ)
  | .lt a b => .lt (a.subst σ) (b.subst σ)
  | .eq a b => .eq (a.subst σ) (b.subst σ)
  | .pi e A B => .pi e (A.subst σ) (B.subst (liftSub σ))
  | .lam e A body => .lam e (A.subst σ) (body.subst (liftSub σ))
  | .app f a => .app (f.subst σ) (a.subst σ)
  | .elements xs => .elements (xs.map (fun x => x.subst σ))
  | .index a i p => .index (a.subst σ) (i.subst σ) (p.subst σ)
  | .refl a => .refl (a.subst σ)
  | .zeroLe a => .zeroLe (a.subst σ)
  | .decide a b => .decide (a.subst σ) (b.subst σ)
  | .uadd a b => .uadd (a.subst σ) (b.subst σ)
  | .usub a b p => .usub (a.subst σ) (b.subst σ) (p.subst σ)

def proposition : Raw → Bool
  | .lt _ _ | .eq _ _ => true
  | .pi _ _ B => B.proposition
  | _ => false

/-- Entries are expressed in the CURRENT scope. Every extension weakens both
old entries and the new annotation, which was written before its binder. -/
abbrev Context := Nat → Option Raw

def Context.extend (Γ : Context) (A : Raw) : Context
  | 0 => some (A.rename Nat.succ)
  | n + 1 => (Γ n).map (fun B => B.rename Nat.succ)

/-- A small independent conversion relation. Its sole computation rule is
non-overflowing numeral addition. No mathematical-natural identities for open
machine arithmetic, subtraction cancellation, or checker completeness are used. -/
inductive Conv : Raw → Raw → Prop where
  | refl (A) : Conv A A
  | symm : Conv A B → Conv B A
  | trans : Conv A B → Conv B C → Conv A C
  | add (a b : Nat) : a + b < wordBound →
      Conv (.uadd (.natural a) (.natural b)) (.natural (a + b))
  | lt : Conv a a' → Conv b b' → Conv (.lt a b) (.lt a' b')
  | eq : Conv a a' → Conv b b' → Conv (.eq a b) (.eq a' b')
  | array : Conv a b → Conv (.array a) (.array b)

mutual
  /-- Type formation without adding a universe constructor to the selected Raw
  syntax. The indices in types must themselves be well-typed U64 expressions. -/
  inductive IsType : Context → Raw → Prop where
    | u64 : IsType Γ .u64
    | i64 : IsType Γ .i64
    | array : HasType Γ n .u64 → IsType Γ (.array n)
    | lt : HasType Γ a .u64 → HasType Γ b .u64 → IsType Γ (.lt a b)
    | eq : HasType Γ a .u64 → HasType Γ b .u64 → IsType Γ (.eq a b)
    | pi : IsType Γ A → e = A.proposition →
        IsType (Γ.extend A) B → IsType Γ (.pi e A B)

  /-- Ordinary declarative rules over one variable namespace. These rules do
  not mention `Index`, `Ty`, `Term`, their encoders, or source typing. Ghost-mode
  lookup is unrestricted; executable runtime erasure checking is not modeled. -/
  inductive HasType : Context → Raw → Raw → Prop where
    | var : Γ x = some A → HasType Γ (.var x) A
    | natural : n < wordBound → HasType Γ (.natural n) .u64
    | integer : -signedBound ≤ n → n < signedBound → HasType Γ (.integer n) .i64
    | uadd : HasType Γ a .u64 → HasType Γ b .u64 → HasType Γ (.uadd a b) .u64
    | usub : HasType Γ a .u64 → HasType Γ b .u64 →
        HasType Γ p (.lt b (.uadd a (.natural 1))) → HasType Γ (.usub a b p) .u64
    | elements : (∀ x ∈ xs, HasType Γ x .i64) → xs.length < wordBound →
        HasType Γ (.elements xs) (.array (.natural xs.length))
    | decide : a < wordBound → b < wordBound → a < b →
        HasType Γ (.decide (.natural a) (.natural b)) (.lt (.natural a) (.natural b))
    | refl : HasType Γ a .u64 → HasType Γ (.refl a) (.eq a a)
    | index : HasType Γ a (.array n) → HasType Γ i .u64 →
        HasType Γ p (.lt i n) → HasType Γ (.index a i p) .i64
    | lam : IsType Γ A → e = A.proposition →
        HasType (Γ.extend A) body B → HasType Γ (.lam e A body) (.pi e A B)
    | app : HasType Γ f (.pi e A B) → HasType Γ a A →
        HasType Γ (.app f a) (B.subst (single a))
    | convert : HasType Γ t A → Conv A B → HasType Γ t B
end

end Raw

namespace Index

def rename (ρ : Nat → Nat) : Index → Index
  | .var x => .var (ρ x)
  | .lit n => .lit n
  | .add a b => .add (a.rename ρ) (b.rename ρ)
  | .closedSub a b h k => .closedSub a b h k

def subst (σ : Nat → Index) : Index → Index
  | .var x => σ x
  | .lit n => .lit n
  | .add a b => .add (a.subst σ) (b.subst σ)
  | .closedSub a b h k => .closedSub a b h k

def shift : Nat → Index := fun x => .var (x + 1)

def liftSub (σ : Nat → Index) : Nat → Index
  | 0 => .var 0
  | n + 1 => (σ n).rename Nat.succ

def single (a : Index) : Nat → Index
  | 0 => a
  | n + 1 => .var n

theorem rename_encode (a : Index) (ρ ix : Nat → Nat) :
    (a.rename ρ).encode ix = a.encode (fun x => ix (ρ x)) := by
  induction a <;> simp_all [rename, encode]

theorem encode_subst (a : Index) (σ : Nat → Index) (τ : Nat → Raw)
    (ix jx : Nat → Nat) (h : ∀ x, τ (ix x) = (σ x).encode jx) :
    (a.encode ix).subst τ = (a.subst σ).encode jx := by
  induction a <;> simp_all [encode, subst, Raw.subst]

theorem subst_shift (a : Index) : a.subst shift = a.rename Nat.succ := by
  induction a <;> simp_all [subst, shift, rename]

theorem scoped_subst {a : Index} (h : a.Scoped n)
    (hσ : ∀ x, x < n → (σ x).Scoped m) : (a.subst σ).Scoped m := by
  induction a <;> simp_all [subst, Scoped]

theorem scoped_rename {a : Index} (h : a.Scoped n) (hρ : Within n m ρ) :
    (a.rename ρ).Scoped m := by
  induction a <;> simp_all [rename, Scoped]

end Index

def Ty.subst (σ : Nat → Index) : Ty → Ty
  | .u64 => .u64
  | .i64 => .i64
  | .array a => .array (a.subst σ)
  | .lt a b => .lt (a.subst σ) (b.subst σ)
  | .eq a b => .eq (a.subst σ) (b.subst σ)
  | .pi B => .pi (B.subst (Index.liftSub σ))

theorem Ty.encode_subst (A : Ty) (σ : Nat → Index) (τ : Nat → Raw)
    (ix jx : Nat → Nat) (h : ∀ x, τ (ix x) = (σ x).encode jx) :
    (A.encode ix).subst τ = (A.subst σ).encode jx := by
  induction A generalizing σ τ ix jx with
  | u64 => simp [Ty.encode, Raw.subst, Ty.subst]
  | i64 => simp [Ty.encode, Raw.subst, Ty.subst]
  | array a => simp only [encode, Raw.subst, subst, Index.encode_subst a σ τ ix jx h]
  | lt a b => simp only [encode, Raw.subst, subst, Index.encode_subst a σ τ ix jx h,
      Index.encode_subst b σ τ ix jx h]
  | eq a b => simp only [encode, Raw.subst, subst, Index.encode_subst a σ τ ix jx h,
      Index.encode_subst b σ τ ix jx h]
  | pi B ih =>
      simp only [encode, Raw.subst, subst]
      congr 1
      apply ih
      intro x
      cases x with
      | zero => rfl
      | succ x =>
          simp only [liftRenaming, Raw.liftSub, Index.liftSub, h,
            Index.encode_rename, Index.rename_encode]

theorem Index.subst_var_encode (a : Index) (ρ ix : Nat → Nat) :
    (a.subst (fun x => .var (ρ x))).encode ix = a.encode (fun x => ix (ρ x)) := by
  induction a <;> simp_all [Index.subst, Index.encode]

theorem Index.liftSub_var (ρ : Nat → Nat) :
    Index.liftSub (fun x => .var (ρ x)) = (fun x => .var (liftRenaming ρ x)) := by
  funext x
  cases x <;> rfl

theorem Ty.encode_renamingSubst (A : Ty) (ρ ix : Nat → Nat) :
    (A.subst (fun x => .var (ρ x))).encode ix = A.encode (fun x => ix (ρ x)) := by
  induction A generalizing ρ ix <;>
    simp_all [Ty.subst, Ty.encode, Index.subst_var_encode, Index.liftSub_var, lift_comp]

theorem Ty.encode_shift (A : Ty) (ix : Nat → Nat) :
    (A.subst Index.shift).encode (liftRenaming ix) =
      (A.encode ix).rename Nat.succ := by
  rw [Ty.encode_rename]
  exact A.encode_renamingSubst Nat.succ (liftRenaming ix)

@[simp] theorem Index.subst_id (a : Index) : a.subst Index.var = a := by
  induction a <;> simp_all [Index.subst]

@[simp] theorem Ty.subst_id (A : Ty) : A.subst Index.var = A := by
  have lift_id : Index.liftSub Index.var = Index.var := by funext x; cases x <;> rfl
  induction A <;> simp_all [Ty.subst]

theorem Ty.encode_instantiate (A : Ty) (a : Index) (ix : Nat → Nat) :
    (A.encode (liftRenaming ix)).subst (Raw.single (a.encode ix)) =
      (A.subst (Index.single a)).encode ix := by
  apply A.encode_subst
  intro x
  cases x <;> rfl

/-- The result type of a value let cannot mention its value binder. Removing
that binder therefore restores the original type, even underneath further Pis. -/
theorem Ty.encode_drop_value (A : Ty) (a : Raw) (ix : Nat → Nat) :
    (A.encode (fun x => ix x + 1)).subst (Raw.single a) = A.encode ix := by
  have h := A.encode_subst Index.var (Raw.single a) (fun x => ix x + 1) ix
    (fun _ => rfl)
  simpa only [Ty.subst_id] using h

theorem Ty.scoped_subst {A : Ty} (h : A.Scoped n)
    (hσ : ∀ x, x < n → (σ x).Scoped m) : (A.subst σ).Scoped m := by
  induction A generalizing n m σ with
  | u64 => trivial
  | i64 => trivial
  | array => exact Index.scoped_subst h hσ
  | lt => exact ⟨Index.scoped_subst h.1 hσ, Index.scoped_subst h.2 hσ⟩
  | eq => exact ⟨Index.scoped_subst h.1 hσ, Index.scoped_subst h.2 hσ⟩
  | pi _ ih =>
      apply ih h
      intro x hx
      cases x with
      | zero => simp [Index.liftSub, Index.Scoped]
      | succ x =>
          apply Index.scoped_rename (hσ x (by omega))
          intro y hy
          simp only [Nat.succ_eq_add_one]
          omega

theorem Ty.encode_proposition (A : Ty) (ix : Nat → Nat) :
    (A.encode ix).proposition = A.proposition := by
  induction A generalizing ix <;> simp_all [Ty.encode, Raw.proposition, Ty.proposition]

/-- Source typing checks the actual annotated bridge syntax, not just its
annotation-erasing image. It uses finite contexts and exact type matching.
There is no rule for general arithmetic conversion or `Term.zeroLe`. -/
inductive SourceTyping : Nat → List Ty → Term → Ty → Prop where
  | var : Γ[x]? = some A → A.Scoped n → SourceTyping n Γ (.var x) A
  | natural : a.Scoped n → SourceTyping n Γ (.natural a) .u64
  | integer : SourceTyping n Γ (.integer a) .i64
  | elements (xs : List Signed) (h : xs.length < wordBound) :
      SourceTyping n Γ (.elements xs) (.array (.lit ⟨xs.length, h⟩))
  | decide : SourceTyping n Γ (.decide a b h) (.lt (.lit a) (.lit b))
  | refl : a.Scoped n → SourceTyping n Γ (.refl a) (.eq a a)
  | index : SourceTyping n Γ a (.array len) → i.Scoped n →
      SourceTyping n Γ p (.lt i len) → SourceTyping n Γ (.index a i p) .i64
  | lam : SourceTyping (n + 1) (Γ.map (fun A => A.subst Index.shift)) body B →
      SourceTyping n Γ (.lam body) (.pi B)
  | app : SourceTyping n Γ f (.pi B) → a.Scoped n →
      SourceTyping n Γ (.app f a) (B.subst (Index.single a))
  | letValue : A.Scoped n → SourceTyping n Γ v A → SourceTyping n (A :: Γ) body B →
      SourceTyping n Γ (.letValue A v body) B

/-- The context correspondence states only lookup facts, not target typing of
the translated term. It is preserved constructively under BOTH binder sorts. -/
def ContextMatch (n : Nat) (Γ : List Ty) (Δ : Raw.Context) (ix vx : Nat → Nat) : Prop :=
  (∀ x, x < n → Δ (ix x) = some .u64) ∧
  (∀ x A, Γ[x]? = some A → Δ (vx x) = some (A.encode ix))

theorem ContextMatch.index (h : ContextMatch n Γ Δ ix vx) :
    ContextMatch (n + 1) (Γ.map (fun A => A.subst Index.shift)) (Δ.extend .u64)
      (liftRenaming ix) (fun x => vx x + 1) := by
  constructor
  · intro x hx
    cases x with
    | zero => simp [liftRenaming, Raw.Context.extend, Raw.rename]
    | succ x => simp [liftRenaming, Raw.Context.extend, h.1 x (by omega), Raw.rename]
  · intro x A hx
    simp only [List.getElem?_map] at hx
    cases hg : Γ[x]? with
    | none => simp [hg] at hx
    | some B =>
        simp only [hg, Option.map_some, Option.some.injEq] at hx
        subst A
        simp [Raw.Context.extend, h.2 x B hg, Ty.encode_shift]

theorem ContextMatch.value (h : ContextMatch n Γ Δ ix vx) (A : Ty) :
    ContextMatch n (A :: Γ) (Δ.extend (A.encode ix))
      (fun x => ix x + 1) (liftRenaming vx) := by
  constructor
  · intro x hx
    simp [Raw.Context.extend, h.1 x hx, Raw.rename]
  · intro x B hx
    cases x with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst B
        simp [liftRenaming, Raw.Context.extend, Ty.encode_rename]
    | succ x =>
        simp only [List.getElem?_cons_succ] at hx
        simp [liftRenaming, Raw.Context.extend, h.2 x B hx, Ty.encode_rename]

theorem Index.encode_typed {a : Index} (h : a.Scoped n)
    (hi : ∀ x, x < n → Δ (ix x) = some .u64) : Raw.HasType Δ (a.encode ix) .u64 := by
  induction a with
  | var x => exact .var (hi x h)
  | lit a => exact .natural a.isLt
  | add a b iha ihb => exact .uadd (iha h.1) (ihb h.2)
  | closedSub a b endpoint bound =>
      apply Raw.HasType.usub (.natural (by omega)) (.natural (by omega))
      apply Raw.HasType.convert (.decide (by omega) endpoint (by omega))
      exact .lt (.refl _) (.symm (.add a 1 endpoint))

theorem Ty.encode_isType {A : Ty} (h : A.Scoped n)
    (hi : ∀ x, x < n → Δ (ix x) = some .u64) : Raw.IsType Δ (A.encode ix) := by
  induction A generalizing n Δ ix with
  | u64 => exact .u64
  | i64 => exact .i64
  | array => exact .array (Index.encode_typed h hi)
  | lt => exact .lt (Index.encode_typed h.1 hi) (Index.encode_typed h.2 hi)
  | eq => exact .eq (Index.encode_typed h.1 hi) (Index.encode_typed h.2 hi)
  | pi B ih =>
      apply Raw.IsType.pi .u64 rfl
      apply ih h
      intro x hx
      cases x with
      | zero => simp [liftRenaming, Raw.Context.extend, Raw.rename]
      | succ x => simp [liftRenaming, Raw.Context.extend, hi x (by omega), Raw.rename]

/-- The typed translation theorem. The target judgment is independently
specified above. In particular no premise assumes the conclusion, and the let
annotation is checked by the source derivation before its lambda encoding. -/
theorem SourceTyping.translate (h : SourceTyping n Γ t A)
    (hc : ContextMatch n Γ Δ ix vx) :
    Raw.HasType Δ (t.encode ix vx) (A.encode ix) := by
  induction h generalizing Δ ix vx with
  | var hx _ => exact .var (hc.2 _ _ hx)
  | natural ha => exact Index.encode_typed ha hc.1
  | @integer n Γ a => exact .integer a.property.1 a.property.2
  | elements xs h =>
      have he : ∀ x ∈ xs.map (fun a => Raw.integer a.val), Raw.HasType Δ x .i64 := by
        intro x hx
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
        exact .integer a.property.1 a.property.2
      simpa only [Term.encode, Ty.encode, Index.encode, List.length_map] using
        Raw.HasType.elements he (by simpa using h)
  | @decide n Γ a b h => exact .decide a.isLt b.isLt h
  | refl ha => exact .refl (Index.encode_typed ha hc.1)
  | index _ hi _ iha ihp => exact .index (iha hc) (Index.encode_typed hi hc.1) (ihp hc)
  | lam _ ih => exact .lam .u64 rfl (ih hc.index)
  | app _ ha ih =>
      rw [Term.encode, ← Ty.encode_instantiate]
      exact .app (ih hc) (Index.encode_typed ha hc.1)
  | @letValue n Γ v A body B ha _ _ ihv ihb =>
      have hlam : Raw.HasType Δ
          (.lam A.proposition (A.encode ix)
            (body.encode (fun x => ix x + 1) (liftRenaming vx)))
          (.pi A.proposition (A.encode ix) (B.encode (fun x => ix x + 1))) :=
        .lam (Ty.encode_isType ha hc.1) (Ty.encode_proposition _ _).symm
          (ihb (hc.value _))
      simpa only [Ty.encode_drop_value, Term.encode] using
        Raw.HasType.app hlam (ihv hc)

theorem SourceTyping.scoped (h : SourceTyping n Γ t A) :
    t.Scoped n Γ.length ∧ A.Scoped n := by
  induction h with
  | var hx ha =>
      constructor
      · obtain ⟨hx, _⟩ := List.getElem?_eq_some_iff.mp hx
        exact hx
      · exact ha
  | natural ha => exact ⟨ha, trivial⟩
  | integer => exact ⟨trivial, trivial⟩
  | elements => exact ⟨trivial, trivial⟩
  | decide => exact ⟨trivial, trivial, trivial⟩
  | refl ha => exact ⟨ha, ha, ha⟩
  | index _ hi _ iha ihp => exact ⟨⟨iha.1, hi, ihp.1⟩, trivial⟩
  | lam _ ih => simpa only [Term.Scoped, Ty.Scoped, List.length_map] using ih
  | app _ ha ih =>
      refine ⟨⟨ih.1, ha⟩, Ty.scoped_subst ih.2 ?_⟩
      intro x hx
      cases x with
      | zero => exact ha
      | succ x => simp only [Index.single, Index.Scoped]; omega
  | letValue ha _ _ ihv ihb =>
      exact ⟨⟨ha, ihv.1, by simpa using ihb.1⟩, ihb.2⟩

/-- An unconditional empty-target-context corollary for every derivation in the
selected closed source fragment. No layout or target typing evidence is assumed. -/
theorem SourceTyping.translate_closed (h : SourceTyping 0 [] t A) :
    Raw.HasType (fun _ => none) (t.encode id id) (A.encode id) := by
  apply h.translate
  constructor
  · intro x hx; omega
  · intro x B hx; simp at hx

theorem SourceTyping.closed_type_formed (h : SourceTyping 0 [] t A) :
    Raw.IsType (fun _ => none) (A.encode id) := by
  apply Ty.encode_isType h.scoped.2
  intro x hx
  omega

/-- The restriction really refines the earlier source calculus, while keeping
annotations that `Term.erase` discards. The converse is deliberately not true. -/
theorem Index.erase_rename (a : Index) (ρ : Nat → Nat) :
    (a.rename ρ).erase = a.erase.subst (fun x => .var (ρ x)) := by
  induction a <;> simp_all [Index.rename, Index.erase, Arithmetic.Expr.subst]

theorem Index.erase_subst (a : Index) (σ : Nat → Index) :
    (a.subst σ).erase = a.erase.subst (fun x => (σ x).erase) := by
  induction a <;> simp_all [Index.subst, Index.erase, Arithmetic.Expr.subst]

theorem Ty.erase_subst (A : Ty) (σ : Nat → Index) :
    (A.subst σ).erase = A.erase.subst (fun x => (σ x).erase) := by
  induction A generalizing σ with
  | u64 => rfl
  | i64 => rfl
  | array => simp [Ty.subst, Ty.erase, Indexed.Ty.subst, Index.erase_subst]
  | lt => simp [Ty.subst, Ty.erase, Indexed.Ty.subst, Index.erase_subst]
  | eq => simp [Ty.subst, Ty.erase, Indexed.Ty.subst, Index.erase_subst]
  | pi B ih =>
      simp only [Ty.subst, Ty.erase, Indexed.Ty.subst, ih]
      congr 2
      funext x
      cases x with
      | zero => rfl
      | succ x =>
          simp only [Index.liftSub, Indexed.lift, Index.erase_rename]
          rfl

theorem SourceTyping.erases (h : SourceTyping n Γ t A) :
    Indexed.HasType (Indexed.complete (Γ.map Ty.erase)) t.erase A.erase := by
  induction h with
  | @var Γ x A n hx _ =>
      have hv : Indexed.complete (Γ.map Ty.erase) x = A.erase := by
        simp [Indexed.complete, List.getElem?_map, hx]
      simpa only [Term.erase, hv] using Indexed.HasType.param (Indexed.complete (Γ.map Ty.erase)) x
  | natural => exact .natural _ _
  | integer => exact .integer _ _
  | @elements n Γ xs bound =>
      simpa only [Term.erase, Ty.erase, Index.erase, List.length_map] using
        Indexed.HasType.elements (Indexed.complete (Γ.map Ty.erase)) (xs.map Subtype.val)
  | decide => exact .decide _ _ _ (by assumption)
  | refl => exact .refl _ _
  | index _ _ _ iha ihp => exact .index iha ihp
  | @lam n body B Γ _ ih =>
      apply Indexed.HasType.lam
      have hc : (Γ.map (fun A => A.subst Index.shift)).map Ty.erase =
          (Γ.map Ty.erase).map (fun A => A.subst Indexed.shift) := by
        simp only [List.map_map]
        congr 1
        funext A
        exact Ty.erase_subst A Index.shift
      rw [hc, Indexed.complete_subst] at ih
      exact ih
  | @app n Γ f B a _ _ ih =>
      have hs : (fun x => (Index.single a x).erase) = Indexed.single a.erase := by
        funext x; cases x <;> rfl
      simpa only [Term.erase, Ty.erase_subst, hs] using Indexed.HasType.app (a := a.erase) ih
  | letValue _ _ _ ihv ihb =>
      apply Indexed.HasType.letValue ihv
      have hc (Γ : List Indexed.Ty) (A : Indexed.Ty) :
          Indexed.complete (A :: Γ) = (Indexed.complete Γ).extend A := by
        funext x; cases x <;> rfl
      simpa only [List.map_cons, hc] using ihb

theorem SourceTyping.erase_closed (h : SourceTyping 0 [] t A) :
    Indexed.ScopedTyping 0 [] t.erase A.erase := by
  refine ⟨by simp, ?_, Ty.erase_scoped h.scoped.2, ?_⟩
  · exact Term.erase_scoped h.scoped.1
  · exact h.erases

end Jihoo.CoreBridge
