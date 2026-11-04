{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- The exported, checked MIR graphs of linear.add/linear.mul and two direct
-- callers. Proofs below evaluate the actual blocks in GeneratedMir; there
-- is no handwritten replacement body or assumed direct-call summary.
------------------------------------------------------------------------
module MirCorrespondence where

open import Schematic
open import Theory
open import Adequacy using (sig; module Adequate)
import Integers as Z
open Z using (ℤ; _≈_; ℤ-ring)
import ScalarExecution as S
import MirExecution as M
open import GeneratedMir
open import ListExecution using (bind; g0)
open Σ
open Rule
open Rules sig rules
open Adequate ℤ-ring using (OD; closure; ⟦_⟧)

-- Metadata is checked along with the graph. The serializer also checks
-- MIR's argument count, passing conventions and supported value types.
signatures : (map M.Function.arguments program ≡
  ((M.int-type ∷ M.int-type ∷ []) ∷ (M.int-type ∷ M.int-type ∷ []) ∷
   (M.int-type ∷ M.int-type ∷ []) ∷ (M.int-type ∷ M.int-type ∷ []) ∷
   (M.int-type ∷ M.int-type ∷ []) ∷ []))
  × (map M.Function.result program ≡ (M.option-type ∷ M.option-type ∷ M.option-type ∷ M.option-type ∷ M.option-type ∷ []))
signatures = refl , refl

data Represents : M.Value → Tm → Set where
  option-none : Represents M.none #Option⟨i128⟩·None
  option-some : ∀ {r t} → GroundWS t ˢZ → ⟦ t ⟧ ≈ r
              → Represents (M.some (M.integer r)) (#Option⟨i128⟩·Some t)

embed : Maybe ℤ → M.Value
embed nothing = M.none
embed (just r) = M.some (M.integer r)

from-scalar : ∀ {r t} → S.Represents r t → Represents (embed r) t
from-scalar S.none = option-none
from-scalar (S.some g e) = option-some g e

representation-ground : ∀ {v t} → Represents v t → GroundWS t ˢOption⟨i128⟩
representation-ground option-none = g0 refl refl
representation-ground (option-some (g , w) e) =
  (λ { x (arg (hd o)) → g x o ; x (arg (tl ())) }) , node refl (w ∷ [])

caller : S.Operation → Tm → Tm → Tm → Tm
caller S.addition a b r = #fn·mir‿add a b r
caller S.multiplication a b r = #fn·mir‿mul a b r

hypothesis : S.Operation → Tm
hypothesis op = S.call op (var 0) (var 1) (var 2)

conclusion : S.Operation → Tm
conclusion op = caller op (var 0) (var 1) (var 2)

CallerMatches : S.Operation → Rule → Set
CallerMatches op r = (prem r ≡ (hypothesis op ∷ [])) × (concl r ≡ conclusion op)
  × (rs r 0 ≡ ˢZ) × (rs r 1 ≡ ˢZ) × (rs r 2 ≡ ˢOption⟨i128⟩)

caller-matches? : (op : S.Operation) (r : Rule) → Dec (CallerMatches op r)
caller-matches? op r = (prem r ≟ₜs (hypothesis op ∷ [])) ×? ((concl r ≟ₜ conclusion op)
  ×? ((rs r 0 ≟ ˢZ) ×? ((rs r 1 ≟ ˢZ) ×? (rs r 2 ≟ ˢOption⟨i128⟩))))

caller-selected : ∀ op → Any (CallerMatches op) rules
caller-selected S.addition = witness (any? (caller-matches? S.addition) rules) tt
caller-selected S.multiplication = witness (any? (caller-matches? S.multiplication) rules) tt

allowed : ∀ op → All (λ y → y ∈ (0 ∷ 1 ∷ 2 ∷ [])) (vars (hypothesis op) ++ vars (conclusion op))
allowed S.addition = witness (all? (λ y → any? (λ n → y ≟ n) (0 ∷ 1 ∷ 2 ∷ [])) _) tt
allowed S.multiplication = witness (all? (λ y → any? (λ n → y ≟ n) (0 ∷ 1 ∷ 2 ∷ [])) _) tt

instantiate-caller : ∀ op {a b t} → GroundWS a ˢZ → GroundWS b ˢZ → GroundWS t ˢOption⟨i128⟩
                   → (r : Rule) → r ∈ rules → CallerMatches op r
                   → OD (sub (bind (a ∷ b ∷ t ∷ [])) (hypothesis op))
                   → OD (sub (bind (a ∷ b ∷ t ∷ [])) (conclusion op))
instantiate-caller op {a} {b} {t} ga gb gt (rule .(hypothesis op ∷ []) .(conclusion op) sorts)
  member (refl , refl , s0 , s1 , s2) derivation = closure member σ ok (derivation ∷ [])
  where
    σ = bind (a ∷ b ∷ t ∷ [])
    ground : ∀ y → y ∈ (0 ∷ 1 ∷ 2 ∷ []) → GroundWS (σ y) (sorts y)
    ground .0 (here refl) = transport (GroundWS a) (sym s0) ga
    ground .1 (there (here refl)) = transport (GroundWS b) (sym s1) gb
    ground .2 (there (there (here refl))) = transport (GroundWS t) (sym s2) gt
    ground y (there (there (there ())))

    ok : ∀ y → OccR y (rule (hypothesis op ∷ []) (conclusion op) sorts) → GroundWS (σ y) (sorts y)
    ok y (inl (hd o)) = ground y (all-∈ (allowed op) (any-++ˡ (occ-vars (hypothesis op) o)))
    ok y (inl (tl ()))
    ok y (inr o) = ground y (all-∈ (allowed op) (any-++ʳ (vars (hypothesis op)) (occ-vars (conclusion op) o)))

sub-hypothesis : ∀ op σ → sub σ (hypothesis op) ≡ S.call op (σ 0) (σ 1) (σ 2)
sub-hypothesis S.addition σ = refl
sub-hypothesis S.multiplication σ = refl

sub-conclusion : ∀ op σ → sub σ (conclusion op) ≡ caller op (σ 0) (σ 1) (σ 2)
sub-conclusion S.addition σ = refl
sub-conclusion S.multiplication σ = refl

lift-caller : ∀ op {a b t} → GroundWS a ˢZ → GroundWS b ˢZ → GroundWS t ˢOption⟨i128⟩
            → OD (S.call op a b t) → OD (caller op a b t)
lift-caller op {a} {b} {t} ga gb gt derivation with S.locate (caller-selected op)
... | r , member , matches = transport OD (sub-conclusion op σ)
  (instantiate-caller op ga gb gt r member matches (transport OD (sym (sub-hypothesis op σ)) derivation))
  where σ = bind (a ∷ b ∷ t ∷ [])

module Proofs (bounds : S.Bounds) where
  open M.Semantics bounds

  data Result (op : S.Operation) (a b : ℤ) : M.Value → Set where
    accepted : ∀ {r} → S.Overflowing bounds (S.exact op a b) r false
             → Result op a b (M.some (M.integer r))
    rejected : ∀ {r} → S.Overflowing bounds (S.exact op a b) r true
             → Result op a b M.none

  start : ℤ → ℤ → M.Store
  start a b = M.initial (M.integer a ∷ M.integer b ∷ [])

  -- Each clause proves the actual returned value after tuple projections,
  -- lifetime markers, the zero switch and every intervening jump/copy.
  helper-add-wp : ∀ a b → wp program helper-add 4 (M.advance helper-add 0 (start a b)) (Result S.addition a b)
  helper-add-wp a b _ (overflow-call {flag = false} ov) = accepted ov
  helper-add-wp a b _ (overflow-call {flag = true} ov) = rejected ov

  helper-mul-wp : ∀ a b → wp program helper-mul 4 (M.advance helper-mul 0 (start a b)) (Result S.multiplication a b)
  helper-mul-wp a b _ (overflow-call {flag = false} ov) = accepted ov
  helper-mul-wp a b _ (overflow-call {flag = true} ov) = rejected ov

  helper-add-run : ∀ {a b v} → Run program helper-add (M.advance helper-add 0 (start a b)) v → Result S.addition a b v
  helper-add-run {a} {b} = wp-sound program helper-add 4 _ _ (helper-add-wp a b)

  helper-mul-run : ∀ {a b v} → Run program helper-mul (M.advance helper-mul 0 (start a b)) v → Result S.multiplication a b v
  helper-mul-run {a} {b} = wp-sound program helper-mul 4 _ _ (helper-mul-wp a b)

  -- Calls are interpreted by their own Run derivation. These clauses
  -- compose the proved callee execution with the caller's actual frame.
  caller-add-wp : ∀ a b → wp program caller-add 2 (M.advance caller-add 0 (start a b)) (Result S.addition a b)
  caller-add-wp a b v (function-call refl arity run) = helper-add-run run

  caller-mul-wp : ∀ a b → wp program caller-mul 2 (M.advance caller-mul 0 (start a b)) (Result S.multiplication a b)
  caller-mul-wp a b v (function-call refl arity run) = helper-mul-run run

  caller-add-run : ∀ {a b v} → Run program caller-add (M.advance caller-add 0 (start a b)) v → Result S.addition a b v
  caller-add-run {a} {b} = wp-sound program caller-add 2 _ _ (caller-add-wp a b)

  caller-mul-run : ∀ {a b v} → Run program caller-mul (M.advance caller-mul 0 (start a b)) v → Result S.multiplication a b v
  caller-mul-run {a} {b} = wp-sound program caller-mul 2 _ _ (caller-mul-wp a b)

  -- Conversely, every permitted intrinsic result has a returning graph
  -- execution. These witnesses also rule out a vacuous proof caused by
  -- treating a reachable statement as stuck.
  helper-add-execution : ∀ {a b r flag} → S.Overflowing bounds (S.exact S.addition a b) r flag
                       → Run program helper-add (M.advance helper-add 0 (start a b)) (embed (S.project r flag))
  helper-add-execution {flag = false} ov = called (overflow-call ov) (continued (continued returned))
  helper-add-execution {flag = true} ov = called (overflow-call ov) (continued returned)

  helper-mul-execution : ∀ {a b r flag} → S.Overflowing bounds (S.exact S.multiplication a b) r flag
                       → Run program helper-mul (M.advance helper-mul 0 (start a b)) (embed (S.project r flag))
  helper-mul-execution {flag = false} ov = called (overflow-call ov) (continued (continued returned))
  helper-mul-execution {flag = true} ov = called (overflow-call ov) (continued returned)

  caller-add-execution : ∀ {a b r flag} → S.Overflowing bounds (S.exact S.addition a b) r flag
                       → Run program caller-add (M.advance caller-add 0 (start a b)) (embed (S.project r flag))
  caller-add-execution ov = called (function-call refl refl (helper-add-execution ov)) returned

  caller-mul-execution : ∀ {a b r flag} → S.Overflowing bounds (S.exact S.multiplication a b) r flag
                       → Run program caller-mul (M.advance caller-mul 0 (start a b)) (embed (S.project r flag))
  caller-mul-execution ov = called (function-call refl refl (helper-mul-execution ov)) returned

  result-horn : ∀ op a b ta tb → GroundWS ta ˢZ → GroundWS tb ˢZ → ⟦ ta ⟧ ≈ a → ⟦ tb ⟧ ≈ b
              → ∀ {v} → Result op a b v → Σ Tm (λ t → Represents v t × OD (S.call op ta tb t))
  result-horn op a b ta tb ga gb ea eb (accepted {r} ov)
    with S.intrinsic-execution bounds op a b r false ta tb ga gb ea eb ov
  ... | t , rep , derivation = t , from-scalar rep , derivation
  result-horn op a b ta tb ga gb ea eb (rejected {r} ov)
    with S.intrinsic-execution bounds op a b r true ta tb ga gb ea eb ov
  ... | t , rep , derivation = t , from-scalar rep , derivation

  helper-add-horn : ∀ a b ta tb → GroundWS ta ˢZ → GroundWS tb ˢZ → ⟦ ta ⟧ ≈ a → ⟦ tb ⟧ ≈ b
                  → ∀ {v} → Run program helper-add (M.advance helper-add 0 (start a b)) v
                  → Σ Tm (λ t → Represents v t × OD (#fn·add ta tb t))
  helper-add-horn a b ta tb ga gb ea eb run = result-horn S.addition a b ta tb ga gb ea eb (helper-add-run run)

  helper-mul-horn : ∀ a b ta tb → GroundWS ta ˢZ → GroundWS tb ˢZ → ⟦ ta ⟧ ≈ a → ⟦ tb ⟧ ≈ b
                  → ∀ {v} → Run program helper-mul (M.advance helper-mul 0 (start a b)) v
                  → Σ Tm (λ t → Represents v t × OD (#fn·mul ta tb t))
  helper-mul-horn a b ta tb ga gb ea eb run = result-horn S.multiplication a b ta tb ga gb ea eb (helper-mul-run run)

  caller-add-horn : ∀ a b ta tb → GroundWS ta ˢZ → GroundWS tb ˢZ → ⟦ ta ⟧ ≈ a → ⟦ tb ⟧ ≈ b
                  → ∀ {v} → Run program caller-add (M.advance caller-add 0 (start a b)) v
                  → Σ Tm (λ t → Represents v t × OD (#fn·mir‿add ta tb t))
  caller-add-horn a b ta tb ga gb ea eb run
    with result-horn S.addition a b ta tb ga gb ea eb (caller-add-run run)
  ... | t , rep , derivation = t , rep , lift-caller S.addition ga gb (representation-ground rep) derivation

  caller-mul-horn : ∀ a b ta tb → GroundWS ta ˢZ → GroundWS tb ˢZ → ⟦ ta ⟧ ≈ a → ⟦ tb ⟧ ≈ b
                  → ∀ {v} → Run program caller-mul (M.advance caller-mul 0 (start a b)) v
                  → Σ Tm (λ t → Represents v t × OD (#fn·mir‿mul ta tb t))
  caller-mul-horn a b ta tb ga gb ea eb run
    with result-horn S.multiplication a b ta tb ga gb ea eb (caller-mul-run run)
  ... | t , rep , derivation = t , rep , lift-caller S.multiplication ga gb (representation-ground rep) derivation

module InI128 = Proofs S.i128
