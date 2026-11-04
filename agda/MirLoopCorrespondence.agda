{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- An inductive invariant for the actual exported mir_loop graph. Every
-- returning execution gives an in-range accumulator whose next addition
-- overflows, and a numerical witness in the generated Horn loop relation.
-- No bound on iterations or termination premise is used.
------------------------------------------------------------------------
module MirLoopCorrespondence where

open import Schematic
open import Theory
open import Adequacy using (sig; module Adequate)
import Integers as Z
open Z using (ℤ; _≈_; ℤ-ring)
import ScalarExecution as S
import MirExecution as M
open import GeneratedMir
open import MirCorrespondence using (Represents; option-some; representation-ground)
open import ListExecution using (bind; g0)
open Σ
open Rule
open Rules sig rules
open Adequate ℤ-ring using (OD; closure; ⟦_⟧)

-- Match complete schemas and every occurring variable's sort, without
-- relying on rule names or positions. The loop-head symbol is checked
-- against the regenerated theory along with the entry/step/exit rules.
data Schema : Set where
  entry step exit : Schema

premises : Schema → List Tm
premises entry = #fn·mir‿loop′1 (var 0) (var 1) (var 2) (var 3) ∷ []
premises step = #fn·mir‿loop′1 (var 0) (var 1) (#add (var 2) (var 1)) (var 3) ∷ []
premises exit = []

conclusion : Schema → Tm
conclusion entry = #fn·mir‿loop (var 2) (var 1) (var 3)
conclusion step = #fn·mir‿loop′1 (#fuel1 (var 0)) (var 1) (var 2) (var 3)
conclusion exit = #fn·mir‿loop′1 (var 0) (var 1) (var 2) (#Option⟨i128⟩·Some (var 2))

last-sort : Schema → ℕ
last-sort entry = ˢOption⟨i128⟩
last-sort step = ˢOption⟨i128⟩
last-sort exit = ˢZ

Matches : Schema → Rule → Set
Matches k r = (prem r ≡ premises k) × (concl r ≡ conclusion k)
  × (rs r 0 ≡ ˢFuel) × (rs r 1 ≡ ˢZ) × (rs r 2 ≡ ˢZ) × (rs r 3 ≡ last-sort k)

matches? : (k : Schema) (r : Rule) → Dec (Matches k r)
matches? k r = (prem r ≟ₜs premises k) ×? ((concl r ≟ₜ conclusion k)
  ×? ((rs r 0 ≟ ˢFuel) ×? ((rs r 1 ≟ ˢZ) ×? ((rs r 2 ≟ ˢZ) ×? (rs r 3 ≟ last-sort k)))))

selected : ∀ k → Any (Matches k) rules
selected entry = witness (any? (matches? entry) rules) tt
selected step = witness (any? (matches? step) rules) tt
selected exit = witness (any? (matches? exit) rules) tt

allowed : ∀ k → All (λ y → y ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])) (varss (premises k) ++ vars (conclusion k))
allowed entry = witness (all? (λ y → any? (λ n → y ≟ n) (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])) _) tt
allowed step = witness (all? (λ y → any? (λ n → y ≟ n) (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])) _) tt
allowed exit = witness (all? (λ y → any? (λ n → y ≟ n) (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])) _) tt

instantiate : ∀ k {n b x t} → GroundWS n ˢFuel → GroundWS b ˢZ → GroundWS x ˢZ → GroundWS t (last-sort k)
             → (r : Rule) → r ∈ rules → Matches k r
             → All (λ p → OD (sub (bind (n ∷ b ∷ x ∷ t ∷ [])) p)) (premises k)
             → OD (sub (bind (n ∷ b ∷ x ∷ t ∷ [])) (conclusion k))
instantiate k {n} {b} {x} {t} gn gb gx gt (rule .(premises k) .(conclusion k) sorts)
  member (refl , refl , s0 , s1 , s2 , s3) derivations = closure member σ ok derivations
  where
    σ = bind (n ∷ b ∷ x ∷ t ∷ [])
    ground : ∀ y → y ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) → GroundWS (σ y) (sorts y)
    ground .0 (here refl) = transport (GroundWS n) (sym s0) gn
    ground .1 (there (here refl)) = transport (GroundWS b) (sym s1) gb
    ground .2 (there (there (here refl))) = transport (GroundWS x) (sym s2) gx
    ground .3 (there (there (there (here refl)))) = transport (GroundWS t) (sym s3) gt
    ground y (there (there (there (there ()))))

    ok : ∀ y → OccR y (rule (premises k) (conclusion k) sorts) → GroundWS (σ y) (sorts y)
    ok y (inl o) = ground y (all-∈ (allowed k) (any-++ˡ (occs-varss (premises k) o)))
    ok y (inr o) = ground y (all-∈ (allowed k) (any-++ʳ (varss (premises k)) (occ-vars (conclusion k) o)))

derive : ∀ k {n b x t} → GroundWS n ˢFuel → GroundWS b ˢZ → GroundWS x ˢZ → GroundWS t (last-sort k)
        → All (λ p → OD (sub (bind (n ∷ b ∷ x ∷ t ∷ [])) p)) (premises k)
        → OD (sub (bind (n ∷ b ∷ x ∷ t ∷ [])) (conclusion k))
derive k gn gb gx gt ds with S.locate (selected k)
... | r , member , matches = instantiate k gn gb gx gt r member matches ds

enter : ∀ {n b x t} → GroundWS n ˢFuel → GroundWS b ˢZ → GroundWS x ˢZ → GroundWS t ˢOption⟨i128⟩
       → OD (#fn·mir‿loop′1 n b x t) → OD (#fn·mir‿loop x b t)
enter gn gb gx gt d = derive entry gn gb gx gt (d ∷ [])

iterate : ∀ {n b x t} → GroundWS n ˢFuel → GroundWS b ˢZ → GroundWS x ˢZ → GroundWS t ˢOption⟨i128⟩
         → OD (#fn·mir‿loop′1 n b (#add x b) t) → OD (#fn·mir‿loop′1 (#fuel1 n) b x t)
iterate gn gb gx gt d = derive step gn gb gx gt (d ∷ [])

leave : ∀ {n b x} → GroundWS n ˢFuel → GroundWS b ˢZ → GroundWS x ˢZ
       → OD (#fn·mir‿loop′1 n b x (#Option⟨i128⟩·Some x))
leave gn gb gx = derive exit {t = #z0} gn gb gx (g0 refl refl) []

fuel-suc : ∀ {n} → GroundWS n ˢFuel → GroundWS (#fuel1 n) ˢFuel
fuel-suc (g , w) = (λ { x (arg (hd o)) → g x o ; x (arg (tl ())) }) , node refl (w ∷ [])

exit-action : ∀ s x → s 3 ≡ just (M.integer x)
             → M.advance loop-add 6 s ≡ M.finished (M.some (M.integer x))
exit-action s x r3 with s 3 | r3
... | .(just (M.integer x)) | refl = refl

header-action : ∀ s x b → s 2 ≡ just (M.integer b) → s 3 ≡ just (M.integer x)
               → M.advance loop-add 1 s ≡ M.invoke (M.overflowing S.addition)
                   (M.integer x ∷ M.integer b ∷ []) 4 4 (M.set s 4 nothing)
header-action s x b r2 r3 with s 3 | r3 | s 2 | r2
... | .(just (M.integer x)) | refl | .(just (M.integer b)) | refl = refl

-- Name the concrete frames to avoid solving metavariables through reads.
-- Their statement-by-statement shape is checked against GeneratedMir.
flag-frame : M.Store → ℤ → Bool → M.Store
flag-frame s r flag = M.set (M.set (M.set (M.set (M.set
  (M.set (M.set s 4 nothing) 4 (just (M.pair (M.integer r) (M.boolean flag))))
  5 nothing) 5 (just (M.integer r))) 6 nothing) 6 (just (M.boolean flag))) 4 nothing

backedge-frame : M.Store → ℤ → M.Store
backedge-frame s r = M.set (M.set (M.set (M.set (M.set (M.set (flag-frame s r false)
  8 nothing) 8 (just (M.integer r))) 3 (just (M.integer r))) 8 nothing) 6 nothing) 5 nothing

entry-frame : ℤ → ℤ → M.Store
entry-frame a b = M.set (M.set (M.initial (M.integer a ∷ M.integer b ∷ []))
  3 nothing) 3 (just (M.integer a))

module Proofs (bounds : S.Bounds) where
  open M.Semantics bounds

  data Last (b : ℤ) : M.Value → Set where
    last : ∀ {x} → S.Inside bounds x → ¬ S.Inside bounds (S.exact S.addition x b)
         → Last b (M.some (M.integer x))

  inside-result : ∀ {x r} → S.Overflowing bounds x r false → S.Inside bounds r
  inside-result {x} {r} (S.exact-result (lo , hi) e) =
    Z.≤-resp {S.Bounds.lower bounds} {x} {S.Bounds.lower bounds} {r} lo refl (sym e)
    , Z.≤-resp {x} {S.Bounds.upper bounds} {r} {S.Bounds.upper bounds} hi (sym e) refl

  module ForInputs (a b : ℤ) (ta tb : Tm) (ga : GroundWS ta ˢZ) (gb : GroundWS tb ˢZ)
                   (ea : ⟦ ta ⟧ ≈ a) (eb : ⟦ tb ⟧ ≈ b) where
    Post : M.Value → Set
    Post v = Last b v × Σ Tm (λ t → Represents v t × OD (#fn·mir‿loop ta tb t))

    -- A history transports a future loop-head derivation back to the
    -- original function entry. Each successful iteration adds fuel1.
    History : Tm → Set
    History tx = ∀ n t → GroundWS n ˢFuel → GroundWS t ˢOption⟨i128⟩
               → OD (#fn·mir‿loop′1 n tb tx t) → OD (#fn·mir‿loop ta tb t)

    data Inv : ℕ → M.Store → Set where
      at-head : ∀ {s x tx} → s 2 ≡ just (M.integer b) → s 3 ≡ just (M.integer x)
               → S.Inside bounds x → GroundWS tx ˢZ → ⟦ tx ⟧ ≈ x → History tx → Inv 1 s

    resume : ∀ s x tx → s 2 ≡ just (M.integer b) → s 3 ≡ just (M.integer x)
            → S.Inside bounds x → GroundWS tx ˢZ → ⟦ tx ⟧ ≈ x → History tx
            → ∀ v → Calls program (M.overflowing S.addition) (M.integer x ∷ M.integer b ∷ []) v
            → Paths program loop-add Inv Post (M.advance loop-add 4 (M.set (M.set s 4 nothing) 4 (just v)))
    resume s x tx r2 r3 inside gx ex history _ (overflow-call {r = r} {flag = false} ov@(S.exact-result ok e))
      = jump (jump (cut (at-head r2 refl (inside-result ov)
        (S.expression-ground S.addition gx gb)
        (Z.≈-trans {⟦ #add tx tb ⟧} {S.exact S.addition x b} {r}
          (S.expression-value S.addition {tx} {tb} {x} {b} ex eb) (sym e))
        (λ n t gn gt d → history (#fuel1 n) t (fuel-suc gn) gt (iterate gn gb gx gt d)))))
    resume s x tx r2 r3 inside gx ex history _ (overflow-call {r = r} {flag = true} (S.overflow-result bad ok))
      = jump (transport (Paths program loop-add Inv Post) (sym (exit-action (flag-frame s r true) x r3))
        (done (last inside bad , #Option⟨i128⟩·Some tx , rep
        , history #fuel0 (#Option⟨i128⟩·Some tx) (g0 refl refl) (representation-ground rep) (leave (g0 refl refl) gb gx))))
      where rep = option-some gx ex

    closed : ∀ bb s → Inv bb s → Paths program loop-add Inv Post (M.advance loop-add bb s)
    closed .1 s (at-head {x = x} {tx} r2 r3 inside gx ex history) =
      transport (Paths program loop-add Inv Post) (sym (header-action s x b r2 r3))
        (calling (resume s x tx r2 r3 inside gx ex history))

    start : M.Store
    start = M.initial (M.integer a ∷ M.integer b ∷ [])

    entry-path : S.Inside bounds a → Paths program loop-add Inv Post (M.advance loop-add 0 start)
    entry-path inside = cut (at-head refl refl inside ga ea (λ n t gn gt d → enter gn gb ga gt d))

    sound : S.Inside bounds a → ∀ {v} → Run program loop-add (M.advance loop-add 0 start) v → Post v
    sound inside = paths-sound program loop-add Inv Post closed (entry-path inside)

  -- Construct returning executions from any finite sequence of permitted
  -- intrinsic outcomes. This tests the back edge as well as the exit;
  -- neither the invariant nor its Horn history can hide a stuck graph.
  data Iterations (b : ℤ) (x : ℤ) : M.Value → Set where
    overflow : ∀ {r} → S.Overflowing bounds (S.exact S.addition x b) r true
             → Iterations b x (M.some (M.integer x))
    again : ∀ {r v} → S.Overflowing bounds (S.exact S.addition x b) r false
          → Iterations b r v → Iterations b x v

  header-execution : ∀ s x b → s 2 ≡ just (M.integer b) → s 3 ≡ just (M.integer x)
                    → ∀ {v} → Iterations b x v → Run program loop-add (M.advance loop-add 1 s) v
  header-execution s x b r2 r3 (overflow {r = r} ov) =
    transport (λ action → Run program loop-add action (M.some (M.integer x))) (sym (header-action s x b r2 r3))
      (called (overflow-call ov) (continued
        (transport (λ action → Run program loop-add action (M.some (M.integer x)))
          (sym (exit-action (flag-frame s r true) x r3)) returned)))
  header-execution s x b r2 r3 {v} (again {r = r} ov iterations) =
    transport (λ action → Run program loop-add action v) (sym (header-action s x b r2 r3))
      (called (overflow-call ov) (continued (continued (continued
        (header-execution (backedge-frame s r) r b r2 refl iterations)))))

  execution : ∀ a b {v} → Iterations b a v
             → Run program loop-add (M.advance loop-add 0 (M.initial (M.integer a ∷ M.integer b ∷ []))) v
  execution a b iterations = continued (header-execution (entry-frame a b) a b refl refl iterations)

module InI128 = Proofs S.i128
