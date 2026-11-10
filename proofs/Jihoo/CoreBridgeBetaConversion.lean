import Jihoo.CoreBridgeMetatheory

/-! Untyped beta, bounded literal-arithmetic and local-array-read conversion on the unified target syntax. The
Church–Rosser argument below proves, rather than postulates, Pi injectivity. -/
namespace Jihoo.CoreBridge.Raw.Beta
open Jihoo.Indexed (liftRenaming)
set_option linter.unusedSimpArgs false

inductive ListRel (R : Raw → Raw → Prop) : List Raw → List Raw → Prop where
  | nil : ListRel R [] []
  | cons : R a b → ListRel R xs ys → ListRel R (a :: xs) (b :: ys)

inductive Conv : Raw → Raw → Prop where
  | refl (A) : Conv A A
  | symm : Conv A B → Conv B A
  | trans : Conv A B → Conv B C → Conv A C
  | beta (e A body a) : Conv (.app (.lam e A body) a) (body.subst (single a))
  | add (a b : Nat) : a + b < wordBound →
      Conv (.uadd (.natural a) (.natural b)) (.natural (a + b))
  | subLiteral (a b : Nat) (p : Raw) : b ≤ a → a < wordBound →
      Conv (.usub (.natural a) (.natural b) p) (.natural (a - b))
  | read (xs : List Raw) (k : Nat) (p v : Raw) : xs[k]? = some v →
      Conv (.index (.elements xs) (.natural k) p) v
  | array : Conv a b → Conv (.array a) (.array b)
  | lt : Conv a a' → Conv b b' → Conv (.lt a b) (.lt a' b')
  | eq : Conv a a' → Conv b b' → Conv (.eq a b) (.eq a' b')
  | pi : Conv A A' → Conv B B' → Conv (.pi e A B) (.pi e A' B')
  | lam : Conv A A' → Conv b b' → Conv (.lam e A b) (.lam e A' b')
  | app : Conv f f' → Conv a a' → Conv (.app f a) (.app f' a')
  | elements : ListRel Conv xs ys → Conv (.elements xs) (.elements ys)
  | index : Conv a a' → Conv i i' → Conv p p' → Conv (.index a i p) (.index a' i' p')
  | reflTerm : Conv a b → Conv (.refl a) (.refl b)
  | zeroLe : Conv a b → Conv (.zeroLe a) (.zeroLe b)
  | decide : Conv a a' → Conv b b' → Conv (.decide a b) (.decide a' b')
  | uadd : Conv a a' → Conv b b' → Conv (.uadd a b) (.uadd a' b')
  | usub : Conv a a' → Conv b b' → Conv p p' → Conv (.usub a b p) (.usub a' b' p')


theorem Conv.renaming (h : Conv A B) (ρ : Nat → Nat) :
    Conv (A.rename ρ) (B.rename ρ) := by
  induction h using Conv.rec
    (motive_2 := fun xs ys _ => ∀ ρ, ListRel Conv
      (xs.map (rename ρ)) (ys.map (rename ρ))) generalizing ρ with
  | refl => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .refl _
  | symm _ ih => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .symm (ih ρ)
  | trans _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .trans (ih₁ ρ) (ih₂ ρ)
  | beta e A b a =>
      simpa only [rename, rename_instantiate] using
        (Conv.beta e (A.rename ρ) (b.rename (liftRenaming ρ)) (a.rename ρ))
  | add a b h => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .add a b h
  | subLiteral a b p hb ha => simp only [rename, subst]; exact .subLiteral a b (p.rename ρ) hb ha
  | read xs k p v selected =>
      simp only [rename]
      exact .read _ k _ _ (by simp [List.getElem?_map, selected])
  | array _ ih => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .array (ih ρ)
  | lt _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .lt (ih₁ ρ) (ih₂ ρ)
  | eq _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .eq (ih₁ ρ) (ih₂ ρ)
  | pi _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .pi (ih₁ ρ) (ih₂ (liftRenaming ρ))
  | lam _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .lam (ih₁ ρ) (ih₂ (liftRenaming ρ))
  | app _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .app (ih₁ ρ) (ih₂ ρ)
  | elements _ ih => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .elements (ih ρ)
  | index _ _ _ ih₁ ih₂ ih₃ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .index (ih₁ ρ) (ih₂ ρ) (ih₃ ρ)
  | reflTerm _ ih => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .reflTerm (ih ρ)
  | zeroLe _ ih => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .zeroLe (ih ρ)
  | decide _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .decide (ih₁ ρ) (ih₂ ρ)
  | uadd _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .uadd (ih₁ ρ) (ih₂ ρ)
  | usub _ _ _ ih₁ ih₂ ih₃ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .usub (ih₁ ρ) (ih₂ ρ) (ih₃ ρ)
  | nil => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .nil
  | cons _ _ ih₁ ih₂ => rename_i ρ; exact .cons (ih₁ ρ) (ih₂ ρ)

theorem Conv.substitution (h : Conv A B) (σ : Nat → Raw) :
    Conv (A.subst σ) (B.subst σ) := by
  induction h using Conv.rec
    (motive_2 := fun xs ys _ => ∀ σ, ListRel Conv
      (xs.map (subst σ)) (ys.map (subst σ))) generalizing σ with
  | refl => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .refl _
  | symm _ ih => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .symm (ih σ)
  | trans _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .trans (ih₁ σ) (ih₂ σ)
  | beta e A b a =>
      simpa only [subst, subst_instantiate] using
        (Conv.beta e (A.subst σ) (b.subst (liftSub σ)) (a.subst σ))
  | add a b h => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .add a b h
  | subLiteral a b p hb ha => simp only [rename, subst]; exact .subLiteral a b (p.subst σ) hb ha
  | read xs k p v selected =>
      simp only [subst]
      exact .read _ k _ _ (by simp [List.getElem?_map, selected])
  | array _ ih => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .array (ih σ)
  | lt _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .lt (ih₁ σ) (ih₂ σ)
  | eq _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .eq (ih₁ σ) (ih₂ σ)
  | pi _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .pi (ih₁ σ) (ih₂ (liftSub σ))
  | lam _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .lam (ih₁ σ) (ih₂ (liftSub σ))
  | app _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .app (ih₁ σ) (ih₂ σ)
  | elements _ ih => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .elements (ih σ)
  | index _ _ _ ih₁ ih₂ ih₃ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .index (ih₁ σ) (ih₂ σ) (ih₃ σ)
  | reflTerm _ ih => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .reflTerm (ih σ)
  | zeroLe _ ih => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .zeroLe (ih σ)
  | decide _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .decide (ih₁ σ) (ih₂ σ)
  | uadd _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .uadd (ih₁ σ) (ih₂ σ)
  | usub _ _ _ ih₁ ih₂ ih₃ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .usub (ih₁ σ) (ih₂ σ) (ih₃ σ)
  | nil => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .nil
  | cons _ _ ih₁ ih₂ => rename_i σ; exact .cons (ih₁ σ) (ih₂ σ)

private theorem lift_conv (h : ∀ x, Conv (σ x) (τ x)) :
    ∀ x, Conv (liftSub σ x) (liftSub τ x) := by
  intro x; cases x with
  | zero => exact .refl _
  | succ x => exact (h x).renaming Nat.succ

theorem Conv.subst_congr (t : Raw) (h : ∀ x, Conv (σ x) (τ x)) :
    Conv (t.subst σ) (t.subst τ) := by
  induction t using Raw.rec
    (motive_2 := fun xs => ∀ σ τ, (∀ x, Conv (σ x) (τ x)) →
      ListRel Conv (xs.map (subst σ)) (xs.map (subst τ))) generalizing σ τ with
  | var x => (try simp only [subst]); exact h x
  | natural | integer | u64 | i64 => (try simp only [subst]); exact .refl _
  | array _ ih => (try simp only [subst]); exact .array (ih h)
  | lt _ _ ih₁ ih₂ => (try simp only [subst]); exact .lt (ih₁ h) (ih₂ h)
  | eq _ _ ih₁ ih₂ => (try simp only [subst]); exact .eq (ih₁ h) (ih₂ h)
  | pi _ _ _ ih₁ ih₂ => (try simp only [subst]); exact .pi (ih₁ h) (ih₂ (lift_conv h))
  | lam _ _ _ ih₁ ih₂ => (try simp only [subst]); exact .lam (ih₁ h) (ih₂ (lift_conv h))
  | app _ _ ih₁ ih₂ => (try simp only [subst]); exact .app (ih₁ h) (ih₂ h)
  | elements _ ih => (try simp only [subst]); exact .elements (ih _ _ h)
  | index _ _ _ ih₁ ih₂ ih₃ => (try simp only [subst]); exact .index (ih₁ h) (ih₂ h) (ih₃ h)
  | refl _ ih => (try simp only [subst]); exact .reflTerm (ih h)
  | zeroLe _ ih => (try simp only [subst]); exact .zeroLe (ih h)
  | decide _ _ ih₁ ih₂ => (try simp only [subst]); exact .decide (ih₁ h) (ih₂ h)
  | uadd _ _ ih₁ ih₂ => (try simp only [subst]); exact .uadd (ih₁ h) (ih₂ h)
  | usub _ _ _ ih₁ ih₂ ih₃ => (try simp only [subst]); exact .usub (ih₁ h) (ih₂ h) (ih₃ h)
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons (ih₁ ‹_›) (ih₂ _ _ ‹_›)

theorem Conv.instantiate_congr {B : Raw} (h : Conv a b) :
    Conv (B.subst (single a)) (B.subst (single b)) := by
  apply Conv.subst_congr
  intro x; cases x with
  | zero => exact h
  | succ x => exact .refl _

/-- Parallel beta reduction, including the nonoverflowing numeral rule. -/
inductive Par : Raw → Raw → Prop where
  | var (x) : Par (.var x) (.var x)
  | natural (n) : Par (.natural n) (.natural n)
  | integer (n) : Par (.integer n) (.integer n)
  | u64 : Par .u64 .u64
  | i64 : Par .i64 .i64
  | beta : Par body body' → Par a a' →
      Par (.app (.lam e A body) a) (body'.subst (single a'))
  | add (a b : Nat) : a + b < wordBound →
      Par (.uadd (.natural a) (.natural b)) (.natural (a + b))
  | subLiteral (a b : Nat) (p : Raw) : b ≤ a → a < wordBound →
      Par (.usub (.natural a) (.natural b) p) (.natural (a - b))
  | read (xs : List Raw) (k : Nat) (p v v' : Raw) : xs[k]? = some v → Par v v' →
      Par (.index (.elements xs) (.natural k) p) v'
  | array : Par a b → Par (.array a) (.array b)
  | lt : Par a a' → Par b b' → Par (.lt a b) (.lt a' b')
  | eq : Par a a' → Par b b' → Par (.eq a b) (.eq a' b')
  | pi : Par A A' → Par B B' → Par (.pi e A B) (.pi e A' B')
  | lam : Par A A' → Par b b' → Par (.lam e A b) (.lam e A' b')
  | app : Par f f' → Par a a' → Par (.app f a) (.app f' a')
  | elements : ListRel Par xs ys → Par (.elements xs) (.elements ys)
  | index : Par a a' → Par i i' → Par p p' → Par (.index a i p) (.index a' i' p')
  | reflTerm : Par a b → Par (.refl a) (.refl b)
  | zeroLe : Par a b → Par (.zeroLe a) (.zeroLe b)
  | decide : Par a a' → Par b b' → Par (.decide a b) (.decide a' b')
  | uadd : Par a a' → Par b b' → Par (.uadd a b) (.uadd a' b')
  | usub : Par a a' → Par b b' → Par p p' → Par (.usub a b p) (.usub a' b' p')



theorem Par.refl (t : Raw) : Par t t := by
  induction t using Raw.rec (motive_2 := fun xs => ListRel Par xs xs) with
  | var => exact .var _
  | natural => exact .natural _
  | integer => exact .integer _
  | u64 => exact .u64
  | i64 => exact .i64
  | array _ ih => exact .array ih
  | lt _ _ ih₁ ih₂ => exact .lt ih₁ ih₂
  | eq _ _ ih₁ ih₂ => exact .eq ih₁ ih₂
  | pi _ _ _ ih₁ ih₂ => exact .pi ih₁ ih₂
  | lam _ _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | elements _ ih => exact .elements ih
  | index _ _ _ ih₁ ih₂ ih₃ => exact .index ih₁ ih₂ ih₃
  | refl _ ih => exact .reflTerm ih
  | zeroLe _ ih => exact .zeroLe ih
  | decide _ _ ih₁ ih₂ => exact .decide ih₁ ih₂
  | uadd _ _ ih₁ ih₂ => exact .uadd ih₁ ih₂
  | usub _ _ _ ih₁ ih₂ ih₃ => exact .usub ih₁ ih₂ ih₃
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂

theorem Par.renaming (h : Par A B) (ρ : Nat → Nat) :
    Par (A.rename ρ) (B.rename ρ) := by
  induction h using Par.rec
    (motive_2 := fun xs ys _ => ∀ ρ, ListRel Par
      (xs.map (rename ρ)) (ys.map (rename ρ))) generalizing ρ with
  | var => simp only [rename]; exact .var _
  | natural => simp only [rename]; exact .natural _
  | integer => simp only [rename]; exact .integer _
  | u64 => simp only [rename]; exact .u64
  | i64 => simp only [rename]; exact .i64
  | beta hb ha ihb iha =>
      simp only [rename, rename_instantiate]
      exact .beta (ihb (liftRenaming ρ)) (iha ρ)
  | add a b h => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .add a b h
  | subLiteral a b p hb ha => simp only [rename, subst]; exact .subLiteral a b (p.rename ρ) hb ha
  | read xs k p v v' selected _ ih =>
      simp only [rename]
      exact .read _ k _ _ _ (by simp [List.getElem?_map, selected]) (ih ρ)
  | array _ ih => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .array (ih ρ)
  | lt _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .lt (ih₁ ρ) (ih₂ ρ)
  | eq _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .eq (ih₁ ρ) (ih₂ ρ)
  | pi _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .pi (ih₁ ρ) (ih₂ (liftRenaming ρ))
  | lam _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .lam (ih₁ ρ) (ih₂ (liftRenaming ρ))
  | app _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .app (ih₁ ρ) (ih₂ ρ)
  | elements _ ih => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .elements (ih ρ)
  | index _ _ _ ih₁ ih₂ ih₃ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .index (ih₁ ρ) (ih₂ ρ) (ih₃ ρ)
  | reflTerm _ ih => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .reflTerm (ih ρ)
  | zeroLe _ ih => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .zeroLe (ih ρ)
  | decide _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .decide (ih₁ ρ) (ih₂ ρ)
  | uadd _ _ ih₁ ih₂ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .uadd (ih₁ ρ) (ih₂ ρ)
  | usub _ _ _ ih₁ ih₂ ih₃ => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .usub (ih₁ ρ) (ih₂ ρ) (ih₃ ρ)
  | nil => (try simp only [rename, subst, List.map_nil, List.map_cons]); exact .nil
  | cons _ _ ih₁ ih₂ => rename_i ρ; exact .cons (ih₁ ρ) (ih₂ ρ)


private theorem lift_par (h : ∀ x, Par (σ x) (τ x)) :
    ∀ x, Par (liftSub σ x) (liftSub τ x) := by
  intro x; cases x with
  | zero => exact .var _
  | succ x => exact (h x).renaming Nat.succ

theorem Par.substitution (h : Par A B) (hσ : ∀ x, Par (σ x) (τ x)) :
    Par (A.subst σ) (B.subst τ) := by
  induction h using Par.rec
    (motive_2 := fun xs ys _ => ∀ σ τ, (∀ x, Par (σ x) (τ x)) →
      ListRel Par (xs.map (subst σ)) (ys.map (subst τ))) generalizing σ τ with
  | var x => simp only [subst]; exact hσ x
  | natural => simp only [subst]; exact .natural _
  | integer => simp only [subst]; exact .integer _
  | u64 => simp only [subst]; exact .u64
  | i64 => simp only [subst]; exact .i64
  | beta hb ha ihb iha =>
      simp only [subst, subst_instantiate]
      exact .beta (ihb (lift_par hσ)) (iha hσ)
  | add a b h => simp only [subst]; exact .add a b h
  | subLiteral a b p hb ha => simp only [subst]; exact .subLiteral a b _ hb ha
  | read xs k p v v' selected _ ih =>
      simp only [subst]
      exact .read _ k _ _ _ (by simp [List.getElem?_map, selected]) (ih hσ)
  | array _ ih => simp only [subst]; exact .array (ih hσ)
  | lt _ _ ih₁ ih₂ => simp only [subst]; exact .lt (ih₁ hσ) (ih₂ hσ)
  | eq _ _ ih₁ ih₂ => simp only [subst]; exact .eq (ih₁ hσ) (ih₂ hσ)
  | pi _ _ ih₁ ih₂ => simp only [subst]; exact .pi (ih₁ hσ) (ih₂ (lift_par hσ))
  | lam _ _ ih₁ ih₂ => simp only [subst]; exact .lam (ih₁ hσ) (ih₂ (lift_par hσ))
  | app _ _ ih₁ ih₂ => simp only [subst]; exact .app (ih₁ hσ) (ih₂ hσ)
  | elements _ ih => simp only [subst]; exact .elements (ih _ _ hσ)
  | index _ _ _ ih₁ ih₂ ih₃ => simp only [subst]; exact .index (ih₁ hσ) (ih₂ hσ) (ih₃ hσ)
  | reflTerm _ ih => simp only [subst]; exact .reflTerm (ih hσ)
  | zeroLe _ ih => simp only [subst]; exact .zeroLe (ih hσ)
  | decide _ _ ih₁ ih₂ => simp only [subst]; exact .decide (ih₁ hσ) (ih₂ hσ)
  | uadd _ _ ih₁ ih₂ => simp only [subst]; exact .uadd (ih₁ hσ) (ih₂ hσ)
  | usub _ _ _ ih₁ ih₂ ih₃ => simp only [subst]; exact .usub (ih₁ hσ) (ih₂ hσ) (ih₃ hσ)
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons (ih₁ ‹_›) (ih₂ _ _ ‹_›)

theorem Par.instantiate (hb : Par B B') (ha : Par a a') :
    Par (B.subst (single a)) (B'.subst (single a')) := by
  apply hb.substitution
  intro x; cases x with
  | zero => exact ha
  | succ x => exact .var _


/-- Contract each redex already present in the input, after developing its
children. New redexes exposed by development wait until the next round. -/
def develop : Raw → Raw
  | .var x => .var x
  | .natural n => .natural n
  | .integer n => .integer n
  | .u64 => .u64
  | .i64 => .i64
  | .array a => .array (develop a)
  | .lt a b => .lt (develop a) (develop b)
  | .eq a b => .eq (develop a) (develop b)
  | .pi e A B => .pi e (develop A) (develop B)
  | .lam e A b => .lam e (develop A) (develop b)
  | .app (.lam _ _ b) a => (develop b).subst (single (develop a))
  | .app f a => .app (develop f) (develop a)
  | .elements xs => .elements (xs.map develop)
  | .index (.elements xs) (.natural k) p =>
      match (xs.map develop)[k]? with
      | some v => v
      | none => .index (.elements (xs.map develop)) (.natural k) (develop p)
  | .index a i p => .index (develop a) (develop i) (develop p)
  | .refl a => .refl (develop a)
  | .zeroLe a => .zeroLe (develop a)
  | .decide a b => .decide (develop a) (develop b)
  | .uadd (.natural a) (.natural b) =>
      if a + b < wordBound then .natural (a + b) else .uadd (.natural a) (.natural b)
  | .uadd a b => .uadd (develop a) (develop b)
  | .usub (.natural a) (.natural b) p =>
      if b ≤ a ∧ a < wordBound then .natural (a - b)
      else .usub (.natural a) (.natural b) (develop p)
  | .usub a b p => .usub (develop a) (develop b) (develop p)

private theorem Par.lam_inv (h : Par (.lam e A b) t) :
    ∃ A' b', t = .lam e A' b' ∧ Par A A' ∧ Par b b' := by
  cases h with
  | lam hA hb => exact ⟨_, _, rfl, hA, hb⟩

private theorem Par.pi_inv (h : Par (.pi e A B) t) :
    ∃ A' B', t = .pi e A' B' ∧ Par A A' ∧ Par B B' := by
  cases h with
  | pi hA hB => exact ⟨_, _, rfl, hA, hB⟩

private theorem Par.natural_inv (h : Par (.natural n) t) : t = .natural n := by
  cases h; rfl

private theorem ListRel.lookup_left {k : Nat} (h : ListRel R xs ys) (selected : ys[k]? = some v) :
    ∃ w, xs[k]? = some w ∧ R w v := by
  induction h generalizing k with
  | nil => simp at selected
  | cons hr hs ih =>
      cases k with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
                subst v; exact ⟨_, rfl, hr⟩
      | succ k => exact ih selected

/-- Every parallel reduct reduces again to the same complete development. -/
theorem Par.to_develop (h : Par t u) : Par u (develop t) := by
  induction h using Par.rec
    (motive_2 := fun xs ys _ => ListRel Par ys (xs.map develop)) with
  | var => simpa only [develop] using (Par.var _)
  | natural => simpa only [develop] using (Par.natural _)
  | integer => simpa only [develop] using (Par.integer _)
  | u64 => simpa only [develop] using (Par.u64)
  | i64 => simpa only [develop] using (Par.i64)
  | beta _ _ ihb iha => simpa only [develop] using ihb.instantiate iha
  | add a b hab => simpa only [develop, ite_eq_left hab] using Par.natural (a + b)
  | subLiteral a b p hb ha => simpa [develop, hb, ha] using Par.natural (a - b)
  | read xs k p v v' selected _ ih =>
      simpa only [develop, List.getElem?_map, selected, Option.map_some] using ih
  | array _ ih => simpa only [develop] using (Par.array ih)
  | lt _ _ ih₁ ih₂ => simpa only [develop] using (Par.lt ih₁ ih₂)
  | eq _ _ ih₁ ih₂ => simpa only [develop] using (Par.eq ih₁ ih₂)
  | pi _ _ ih₁ ih₂ => simpa only [develop] using (Par.pi ih₁ ih₂)
  | lam _ _ ih₁ ih₂ => simpa only [develop] using (Par.lam ih₁ ih₂)
  | app hf ha ihf iha =>
      rename_i f f' a a'
      cases f <;> try (simpa only [develop] using (Par.app ihf iha))
      case lam e A b =>
        obtain ⟨A', b', rfl, _, _⟩ := hf.lam_inv
        obtain ⟨A'', b'', heq, _, hb⟩ := ihf.lam_inv
        simp only [develop, Raw.lam.injEq] at heq
        obtain ⟨_, rfl, rfl⟩ := heq
        simpa only [develop] using (Par.beta (e := e) (A := A') hb iha)
  | elements _ ih => simpa only [develop] using (Par.elements ih)
  | index ha hi hp iha ihi ihp =>
      rename_i a a' i i' p p'
      cases a <;> cases i <;> try (simpa only [develop] using (Par.index iha ihi ihp))
      case elements.natural xs k =>
        cases ha with
        | elements hxs =>
          cases hi
          simp only [develop] at iha
          cases iha with
          | elements hdev =>
            simp only [develop]
            cases selected : (xs.map develop)[k]? with
            | none => exact .index (.elements hdev) (.natural _) ihp
            | some v =>
              obtain ⟨w, hw, hv⟩ := hdev.lookup_left selected
              exact .read _ k p' w v hw hv
  | reflTerm _ ih => simpa only [develop] using (Par.reflTerm ih)
  | zeroLe _ ih => simpa only [develop] using (Par.zeroLe ih)
  | decide _ _ ih₁ ih₂ => simpa only [develop] using (Par.decide ih₁ ih₂)
  | uadd ha hb iha ihb =>
      rename_i a a' b b'
      cases a <;> cases b <;> try (simpa only [develop] using (Par.uadd iha ihb))
      case natural.natural a b =>
        have ea := ha.natural_inv
        have eb := hb.natural_inv
        subst a'; subst b'
        simp only [develop]
        split
        · exact .add _ _ ‹_›
        · exact .uadd (.natural _) (.natural _)
  | usub ha hb hp iha ihb ihp =>
      rename_i a a' b b' p p'
      cases a <;> cases b <;> try (simpa only [develop] using (Par.usub iha ihb ihp))
      case natural.natural a b =>
        have ea := ha.natural_inv
        have eb := hb.natural_inv
        subst a'; subst b'
        simp only [develop]
        split
        next h => exact .subLiteral a b p' h.1 h.2
        next => exact .usub (.natural _) (.natural _) ihp
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂

theorem Par.diamond (hu : Par t u) (hv : Par t v) :
    ∃ w, Par u w ∧ Par v w := ⟨develop t, hu.to_develop, hv.to_develop⟩


/-- Reflexive transitive closure. This does not postulate normalization. -/
inductive Closure {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl : Closure R a a
  | cons : R a b → Closure R b c → Closure R a c

namespace Closure
variable {α β : Type} {R : α → α → Prop} {S : β → β → Prop}

theorem single (h : R a b) : Closure R a b := .cons h .refl

theorem trans (h : Closure R a b) (h' : Closure R b c) : Closure R a c := by
  induction h with
  | refl => exact h'
  | cons hab _ ih => exact .cons hab (ih h')

theorem map (f : α → β) (hf : ∀ {a b}, R a b → S (f a) (f b))
    (h : Closure R a b) : Closure S (f a) (f b) := by
  induction h with
  | refl => exact .refl
  | cons hab _ ih => exact .cons (hf hab) ih
end Closure

abbrev Star := Closure Par

theorem Star.strip (hu : Star t u) (hv : Par t v) :
    ∃ w, Par u w ∧ Star v w := by
  induction hu generalizing v with
  | refl => exact ⟨v, hv, .refl⟩
  | cons ht hs ih =>
      obtain ⟨q, hbq, hvq⟩ := ht.diamond hv
      obtain ⟨w, huw, hqw⟩ := ih hbq
      exact ⟨w, huw, .cons hvq hqw⟩

/-- Confluence of arbitrarily long finite parallel reductions. -/
theorem Star.confluence (hu : Star t u) (hv : Star t v) :
    ∃ w, Star u w ∧ Star v w := by
  induction hu generalizing v with
  | refl => exact ⟨v, hv, .refl⟩
  | cons ht hs ih =>
      obtain ⟨q, hvq, hbq⟩ := hv.strip ht
      obtain ⟨w, huw, hqw⟩ := ih hbq
      exact ⟨w, huw, .cons hvq hqw⟩

private theorem Star.congr₂ (f : Raw → Raw → Raw)
    (hf : ∀ {a a' b b'}, Par a a' → Par b b' → Par (f a b) (f a' b'))
    (ha : Star a a') (hb : Star b b') : Star (f a b) (f a' b') := by
  exact (ha.map (fun x => f x b) (fun h => hf h (.refl _))).trans
    (hb.map (fun x => f a' x) (fun h => hf (.refl _) h))

private theorem Star.congr₃ (f : Raw → Raw → Raw → Raw)
    (hf : ∀ {a a' b b' c c'}, Par a a' → Par b b' → Par c c' →
      Par (f a b c) (f a' b' c'))
    (ha : Star a a') (hb : Star b b') (hc : Star c c') :
    Star (f a b c) (f a' b' c') := by
  exact (Star.congr₂ (fun x y => f x y c) (fun h₁ h₂ => hf h₁ h₂ (.refl _)) ha hb).trans
    (hc.map (fun x => f a' b' x) (fun h => hf (.refl _) (.refl _) h))

private theorem ListRel.refl_par (xs : List Raw) : ListRel Par xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (.refl _) ih

private theorem ListRel.stars (h : ListRel Star xs ys) : Closure (ListRel Par) xs ys := by
  induction h with
  | nil => exact .refl
  | @cons a b xs ys hab hxs ih =>
      exact (hab.map (fun x => x :: xs) (fun h => ListRel.cons h (ListRel.refl_par xs))).trans
        (ih.map (fun xs => b :: xs) (fun h => ListRel.cons (Par.refl b) h))

private theorem Star.elements (h : ListRel Star xs ys) :
    Star (.elements xs) (.elements ys) := h.stars.map Raw.elements Par.elements

def Join (t u : Raw) : Prop := ∃ w, Star t w ∧ Star u w

private theorem Join.refl (t : Raw) : Join t t := ⟨t, .refl, .refl⟩

private theorem Join.symm (h : Join t u) : Join u t := by
  obtain ⟨w, ht, hu⟩ := h
  exact ⟨w, hu, ht⟩

private theorem Join.trans (h : Join t u) (h' : Join u v) : Join t v := by
  obtain ⟨a, hta, hua⟩ := h
  obtain ⟨b, hub, hvb⟩ := h'
  obtain ⟨w, haw, hbw⟩ := hua.confluence hub
  exact ⟨w, hta.trans haw, hvb.trans hbw⟩

private theorem Join.map (f : Raw → Raw)
    (hf : ∀ {a b}, Par a b → Par (f a) (f b)) (h : Join a b) : Join (f a) (f b) := by
  obtain ⟨w, ha, hb⟩ := h
  exact ⟨f w, ha.map f hf, hb.map f hf⟩

private theorem Join.map₂ (f : Raw → Raw → Raw)
    (hf : ∀ {a a' b b'}, Par a a' → Par b b' → Par (f a b) (f a' b'))
    (ha : Join a a') (hb : Join b b') : Join (f a b) (f a' b') := by
  obtain ⟨wa, hwa, hwa'⟩ := ha
  obtain ⟨wb, hwb, hwb'⟩ := hb
  exact ⟨f wa wb, Star.congr₂ f hf hwa hwb, Star.congr₂ f hf hwa' hwb'⟩

private theorem Join.map₃ (f : Raw → Raw → Raw → Raw)
    (hf : ∀ {a a' b b' c c'}, Par a a' → Par b b' → Par c c' →
      Par (f a b c) (f a' b' c'))
    (ha : Join a a') (hb : Join b b') (hc : Join c c') :
    Join (f a b c) (f a' b' c') := by
  obtain ⟨wa, hwa, hwa'⟩ := ha
  obtain ⟨wb, hwb, hwb'⟩ := hb
  obtain ⟨wc, hwc, hwc'⟩ := hc
  exact ⟨f wa wb wc, Star.congr₃ f hf hwa hwb hwc, Star.congr₃ f hf hwa' hwb' hwc'⟩

private theorem ListRel.join (h : ListRel Join xs ys) :
    ∃ zs, ListRel Star xs zs ∧ ListRel Star ys zs := by
  induction h with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons h _ ih =>
      obtain ⟨a, ha, hb⟩ := h
      obtain ⟨zs, hxs, hys⟩ := ih
      exact ⟨a :: zs, .cons ha hxs, .cons hb hys⟩

/-- Conversion has the common-reduct property. In particular, inverse beta
steps cannot equate distinct inert constructors. -/
theorem Conv.church_rosser (h : Conv t u) : Join t u := by
  induction h using Conv.rec (motive_2 := fun xs ys _ => ListRel Join xs ys) with
  | refl t => exact Join.refl t
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | beta e A b a => exact ⟨_, .single (.beta (.refl b) (.refl a)), .refl⟩
  | add a b h => exact ⟨_, .single (.add a b h), .refl⟩
  | subLiteral a b p hb ha => exact ⟨_, .single (.subLiteral a b p hb ha), .refl⟩
  | read xs k p v selected => exact ⟨_, .single (.read xs k p v v selected (.refl v)), .refl⟩
  | array _ ih => exact Join.map Raw.array Par.array ih
  | lt _ _ ih₁ ih₂ => exact Join.map₂ Raw.lt Par.lt ih₁ ih₂
  | eq _ _ ih₁ ih₂ => exact Join.map₂ Raw.eq Par.eq ih₁ ih₂
  | pi _ _ ih₁ ih₂ => exact Join.map₂ (Raw.pi _) Par.pi ih₁ ih₂
  | lam _ _ ih₁ ih₂ => exact Join.map₂ (Raw.lam _) Par.lam ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact Join.map₂ Raw.app Par.app ih₁ ih₂
  | elements _ ih =>
      obtain ⟨zs, hxs, hys⟩ := ih.join
      exact ⟨.elements zs, Star.elements hxs, Star.elements hys⟩
  | index _ _ _ ih₁ ih₂ ih₃ => exact Join.map₃ Raw.index Par.index ih₁ ih₂ ih₃
  | reflTerm _ ih => exact Join.map Raw.refl Par.reflTerm ih
  | zeroLe _ ih => exact Join.map Raw.zeroLe Par.zeroLe ih
  | decide _ _ ih₁ ih₂ => exact Join.map₂ Raw.decide Par.decide ih₁ ih₂
  | uadd _ _ ih₁ ih₂ => exact Join.map₂ Raw.uadd Par.uadd ih₁ ih₂
  | usub _ _ _ ih₁ ih₂ ih₃ => exact Join.map₃ Raw.usub Par.usub ih₁ ih₂ ih₃
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂


theorem Par.conv (h : Par t u) : Conv t u := by
  induction h using Par.rec (motive_2 := fun xs ys _ => ListRel Conv xs ys) with
  | var | natural | integer | u64 | i64 => exact .refl _
  | beta _ _ ihb iha => exact .trans (.app (.lam (.refl _) ihb) iha) (.beta _ _ _ _)
  | add a b h => exact .add a b h
  | subLiteral a b p hb ha => exact .subLiteral a b p hb ha
  | read xs k p v v' selected _ ih => exact (Conv.read xs k p v selected).trans ih
  | array _ ih => exact .array ih
  | lt _ _ ih₁ ih₂ => exact .lt ih₁ ih₂
  | eq _ _ ih₁ ih₂ => exact .eq ih₁ ih₂
  | pi _ _ ih₁ ih₂ => exact .pi ih₁ ih₂
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | elements _ ih => exact .elements ih
  | index _ _ _ ih₁ ih₂ ih₃ => exact .index ih₁ ih₂ ih₃
  | reflTerm _ ih => exact .reflTerm ih
  | zeroLe _ ih => exact .zeroLe ih
  | decide _ _ ih₁ ih₂ => exact .decide ih₁ ih₂
  | uadd _ _ ih₁ ih₂ => exact .uadd ih₁ ih₂
  | usub _ _ _ ih₁ ih₂ ih₃ => exact .usub ih₁ ih₂ ih₃
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂

theorem Star.conv (h : Star t u) : Conv t u := by
  induction h with
  | refl => exact .refl _
  | cons hp _ ih => exact .trans hp.conv ih

private theorem Star.pi_shape (h : Star t u) : ∀ {e A B}, t = .pi e A B →
    ∃ A' B', u = .pi e A' B' ∧ Star A A' ∧ Star B B' := by
  induction h with
  | refl =>
      intro e A B ht
      exact ⟨A, B, ht, .refl, .refl⟩
  | cons hp hs ih =>
      intro e A B ht
      subst ht
      obtain ⟨A', B', heq, hA, hB⟩ := hp.pi_inv
      obtain ⟨A'', B'', hu, hA', hB'⟩ := ih heq
      exact ⟨A'', B'', hu, .cons hA hA', .cons hB hB'⟩

/-- Pi injectivity is a consequence of Church–Rosser and preservation of the
outer Pi constructor by reduction, not an additional conversion rule. -/
theorem Conv.pi_injective (h : Conv (.pi e A B) (.pi e' A' B')) :
    e = e' ∧ Conv A A' ∧ Conv B B' := by
  obtain ⟨w, hw, hw'⟩ := h.church_rosser
  obtain ⟨C, D, heq, hA, hB⟩ := hw.pi_shape rfl
  obtain ⟨C', D', heq', hA', hB'⟩ := hw'.pi_shape rfl
  have hi := heq.symm.trans heq'
  simp only [Raw.pi.injEq] at hi
  obtain ⟨hee, hC, hD⟩ := hi
  subst C'; subst D'
  exact ⟨hee, .trans hA.conv (.symm hA'.conv), .trans hB.conv (.symm hB'.conv)⟩

private theorem Star.u64_shape (h : Star t u) (ht : t = .u64) : u = .u64 := by
  induction h with
  | refl => exact ht
  | cons hp hs ih =>
      subst ht
      cases hp
      exact ih rfl

private theorem Star.i64_shape (h : Star t u) (ht : t = .i64) : u = .i64 := by
  induction h with
  | refl => exact ht
  | cons hp hs ih =>
      subst ht
      cases hp
      exact ih rfl

/-- Untyped beta conversion does not collapse the two integer types. -/
theorem Conv.u64_i64_separate : ¬ Conv .u64 .i64 := by
  intro h
  obtain ⟨w, hw, hw'⟩ := h.church_rosser
  have hu := hw.u64_shape rfl
  have hi := hw'.i64_shape rfl
  cases hu.symm.trans hi

end Jihoo.CoreBridge.Raw.Beta
