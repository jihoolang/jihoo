import Jihoo.CoreBridge

namespace Jihoo.CoreBridge

/-- Checked conversion never wraps an out-of-range mathematical literal. -/
def word? (n : Nat) : Option Word := if h : n < wordBound then some ⟨n, h⟩ else none

theorem word?_value (h : word? n = some w) : w.val = n := by
  unfold word? at h
  split at h <;> cases h <;> rfl

def Index.erase : Index → Arithmetic.Expr
  | .var x => .var x
  | .lit n => .lit n.val
  | .add a b => .add a.erase b.erase
  | .closedSub a b _ _ => .sub (.lit a) (.lit b)

def Ty.erase : Ty → Indexed.Ty
  | .u64 => .u64
  | .i64 => .i64
  | .array n => .array n.erase
  | .lt a b => .lt a.erase b.erase
  | .eq a b => .eq a.erase b.erase
  | .pi B => .pi B.erase

def Term.erase : Term → Indexed.Term
  | .var x => .param x
  | .natural a => .natural a.erase
  | .integer n => .integer n.val
  | .elements xs => .elements (xs.map Subtype.val)
  | .decide a b _ => .decide a.val b.val
  | .refl a => .refl a.erase
  | .zeroLe a => .zeroLe a.erase
  | .index a i p => .index a.erase i.erase p.erase
  | .lam body => .lam body.erase
  | .app f a => .app f.erase a.erase
  | .letValue _ v body => .letValue v.erase body.erase

theorem Index.erase_scoped {t : Index} (h : t.Scoped n) : t.erase.Scoped n := by
  induction t with
  | var => exact h
  | lit => trivial
  | add _ _ iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | closedSub => exact ⟨trivial, trivial⟩

theorem Ty.erase_scoped {A : Ty} (h : A.Scoped n) : A.erase.Scoped n := by
  induction A generalizing n with
  | u64 => trivial
  | i64 => trivial
  | array => exact Index.erase_scoped h
  | lt => exact ⟨Index.erase_scoped h.1, Index.erase_scoped h.2⟩
  | eq => exact ⟨Index.erase_scoped h.1, Index.erase_scoped h.2⟩
  | pi _ ih => exact ih h

theorem Term.erase_scoped {t : Term} (h : t.Scoped n m) : t.erase.Scoped n m := by
  induction t generalizing n m with
  | var => exact h
  | natural => exact Index.erase_scoped h
  | integer => trivial
  | elements => trivial
  | decide => trivial
  | refl => exact Index.erase_scoped h
  | zeroLe => exact Index.erase_scoped h
  | index _ _ _ iha ihp => exact ⟨iha h.1, Index.erase_scoped h.2.1, ihp h.2.2⟩
  | lam _ ih => exact ih h
  | app _ _ ih => exact ⟨ih h.1, Index.erase_scoped h.2⟩
  | letValue _ _ _ ihv ihb => exact ⟨ihv h.2.1, ihb h.2.2⟩

/-- Only certified closed subtraction enters from the earlier idealized syntax.
Open subtraction, underflow and an unrepresentable Decide endpoint are rejected. -/
def Index.ofExpr : Arithmetic.Expr → Option Index
  | .var x => some (.var x)
  | .lit n => (word? n).map Index.lit
  | .add a b => do return .add (← ofExpr a) (← ofExpr b)
  | .sub (.lit a) (.lit b) =>
      if h : a + 1 < wordBound ∧ b ≤ a then some (.closedSub a b h.1 h.2) else none
  | .sub _ _ => none

theorem Index.ofExpr_erases (e : Arithmetic.Expr) (h : Index.ofExpr e = some t) :
    t.erase = e := by
  induction e generalizing t with
  | var x => cases h; rfl
  | lit n =>
      cases hw : word? n with
      | none => simp [Index.ofExpr, hw] at h
      | some w =>
          simp only [Index.ofExpr, hw, Option.map_some, Option.some.injEq] at h
          subst t
          simp only [Index.erase, word?_value hw]
  | add a b iha ihb =>
      cases ha : Index.ofExpr a <;> cases hb : Index.ofExpr b <;>
        simp [Index.ofExpr, ha, hb] at h
      case some.some a' b' =>
        subst t
        simp only [Index.erase, iha ha, ihb hb]
  | sub a b =>
      cases a <;> cases b <;> simp only [Index.ofExpr] at h
      all_goals try contradiction
      split at h <;> cases h <;> rfl

def Raw.LiteralsBounded : Raw → Prop
  | .var _ | .u64 | .i64 => True
  | .natural n => n < wordBound
  | .integer n => -signedBound ≤ n ∧ n < signedBound
  | .array n | .refl n | .zeroLe n => n.LiteralsBounded
  | .lt a b | .eq a b | .app a b | .decide a b | .uadd a b => a.LiteralsBounded ∧ b.LiteralsBounded
  | .pi _ A B | .lam _ A B => A.LiteralsBounded ∧ B.LiteralsBounded
  | .elements xs => ∀ x ∈ xs, x.LiteralsBounded
  | .index a b c | .usub a b c => a.LiteralsBounded ∧ b.LiteralsBounded ∧ c.LiteralsBounded

def Raw.CertifiedSubtractions : Raw → Prop
  | .var _ | .natural _ | .integer _ | .u64 | .i64 => True
  | .array n | .refl n | .zeroLe n => n.CertifiedSubtractions
  | .lt a b | .eq a b | .app a b | .decide a b | .uadd a b => a.CertifiedSubtractions ∧ b.CertifiedSubtractions
  | .pi _ A B | .lam _ A B => A.CertifiedSubtractions ∧ B.CertifiedSubtractions
  | .elements xs => ∀ x ∈ xs, x.CertifiedSubtractions
  | .index a b c => a.CertifiedSubtractions ∧ b.CertifiedSubtractions ∧ c.CertifiedSubtractions
  | .usub a b p => ∃ m n, a = .natural m ∧ b = .natural n ∧
      p = .decide (.natural n) (.natural (m + 1)) ∧ n ≤ m ∧ m + 1 < wordBound

theorem Index.encode_bounded (t : Index) (ix : Nat → Nat) : (t.encode ix).LiteralsBounded := by
  induction t <;> simp only [Index.encode, Raw.LiteralsBounded] at *
  case lit n => exact n.isLt
  case add _ _ iha ihb => exact ⟨iha, ihb⟩
  case closedSub a b endpoint bound => omega

theorem Index.encode_certified (t : Index) (ix : Nat → Nat) : (t.encode ix).CertifiedSubtractions := by
  induction t <;> simp only [Index.encode, Raw.CertifiedSubtractions] at *
  case add _ _ iha ihb => exact ⟨iha, ihb⟩
  case closedSub a b endpoint bound => exact ⟨a, b, rfl, rfl, rfl, bound, endpoint⟩

theorem Ty.encode_bounded (A : Ty) (ix : Nat → Nat) : (A.encode ix).LiteralsBounded := by
  induction A generalizing ix <;> simp only [Ty.encode, Raw.LiteralsBounded] at *
  case array a => exact a.encode_bounded ix
  case lt a b => exact ⟨a.encode_bounded ix, b.encode_bounded ix⟩
  case eq a b => exact ⟨a.encode_bounded ix, b.encode_bounded ix⟩
  case pi _ ih => exact ⟨trivial, ih _⟩

theorem Ty.encode_certified (A : Ty) (ix : Nat → Nat) : (A.encode ix).CertifiedSubtractions := by
  induction A generalizing ix <;> simp only [Ty.encode, Raw.CertifiedSubtractions] at *
  case array a => exact a.encode_certified ix
  case lt a b => exact ⟨a.encode_certified ix, b.encode_certified ix⟩
  case eq a b => exact ⟨a.encode_certified ix, b.encode_certified ix⟩
  case pi _ ih => exact ⟨trivial, ih _⟩

theorem Term.encode_bounded (t : Term) (ix vx : Nat → Nat) : (t.encode ix vx).LiteralsBounded := by
  induction t generalizing ix vx <;> simp only [Term.encode, Raw.LiteralsBounded] at *
  case natural a => exact a.encode_bounded ix
  case integer n => exact n.property
  case elements ns =>
    intro x hx
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hx
    simpa only [Raw.LiteralsBounded] using n.property
  case decide a b _ => exact ⟨a.isLt, b.isLt⟩
  case refl a => exact a.encode_bounded ix
  case zeroLe a => exact a.encode_bounded ix
  case index a i p iha ihp => exact ⟨iha _ _, i.encode_bounded ix, ihp _ _⟩
  case lam _ ih => exact ⟨trivial, ih _ _⟩
  case app f a ih => exact ⟨ih _ _, a.encode_bounded ix⟩
  case letValue A v body ihv ihb => exact ⟨⟨A.encode_bounded ix, ihb _ _⟩, ihv _ _⟩

theorem Term.encode_certified (t : Term) (ix vx : Nat → Nat) : (t.encode ix vx).CertifiedSubtractions := by
  induction t generalizing ix vx <;> simp only [Term.encode, Raw.CertifiedSubtractions] at *
  case natural a => exact a.encode_certified ix
  case elements ns =>
    intro x hx
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hx
    simp only [Raw.CertifiedSubtractions]
  case decide => exact ⟨trivial, trivial⟩
  case refl a => exact a.encode_certified ix
  case zeroLe a => exact a.encode_certified ix
  case index a i p iha ihp => exact ⟨iha _ _, i.encode_certified ix, ihp _ _⟩
  case lam _ ih => exact ⟨trivial, ih _ _⟩
  case app f a ih => exact ⟨ih _ _, a.encode_certified ix⟩
  case letValue A v body ihv ihb => exact ⟨⟨A.encode_certified ix, ihb _ _⟩, ihv _ _⟩

/-- Every emitted subtraction has genuine natural non-underflow evidence. -/
theorem certified_sub_no_underflow (h : (Raw.usub a b p).CertifiedSubtractions) :
    ∃ m n, a = .natural m ∧ b = .natural n ∧ n < m + 1 := by
  simp only [Raw.CertifiedSubtractions] at h
  obtain ⟨m, n, ha, hb, _, hn, _⟩ := h
  exact ⟨m, n, ha, hb, by omega⟩

end Jihoo.CoreBridge
