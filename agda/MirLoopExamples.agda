{-# OPTIONS --safe --without-K #-}
module MirLoopExamples where

open import Schematic
open import Theory
open import Adequacy using (sig; module Adequate)
open import Integers using (_⊖_; ℤ-ring)
import ScalarExecution as S
import MirExecution as M
open import GeneratedMir
open import MirCorrespondence using (Represents)
open import MirLoopCorrespondence
-- Keep the helper, direct-call and lifetime examples in the same check.
import MirExecutionExamples
open import ListExecution using (number; number-ground; g0)
open Rules sig rules
open Adequate ℤ-ring using (OD)
open Σ

-- These bounds test control flow. The general proof also instantiates
-- signed i128; the native intrinsic does not overflow at these bounds.
word : S.Bounds
word = S.signed 3

module E = Proofs word
open M.Semantics word

to-six : S.Overflowing word (6 ⊖ 0) (6 ⊖ 0) false
to-six = S.exact-result (witness (S.inside? word (6 ⊖ 0)) tt) refl

to-seven : S.Overflowing word (7 ⊖ 0) (7 ⊖ 0) false
to-seven = S.exact-result (witness (S.inside? word (7 ⊖ 0)) tt) refl

upper-overflow : S.Overflowing word (8 ⊖ 0) (0 ⊖ 8) true
upper-overflow = S.overflow-result (S.rejected word S.addition (7 ⊖ 0) (1 ⊖ 0) refl)
  (witness (S.inside? word (0 ⊖ 8)) tt)

positive-run : Run program loop-add
  (M.advance loop-add 0 (M.initial (M.integer (5 ⊖ 0) ∷ M.integer (1 ⊖ 0) ∷ [])))
  (M.some (M.integer (7 ⊖ 0)))
positive-run = E.execution (5 ⊖ 0) (1 ⊖ 0) (E.again to-six (E.again to-seven (E.overflow upper-overflow)))

immediate-run : Run program loop-add
  (M.advance loop-add 0 (M.initial (M.integer (7 ⊖ 0) ∷ M.integer (1 ⊖ 0) ∷ [])))
  (M.some (M.integer (7 ⊖ 0)))
immediate-run = E.execution (7 ⊖ 0) (1 ⊖ 0) (E.overflow upper-overflow)

module Positive = E.ForInputs (5 ⊖ 0) (1 ⊖ 0) (number 5) #z1
  (number-ground 5) (g0 refl refl) refl refl

positive-result : Positive.Post (M.some (M.integer (7 ⊖ 0)))
positive-result = Positive.sound (witness (S.inside? word (5 ⊖ 0)) tt) positive-run

positive-horn : Σ Tm (λ t → Represents (M.some (M.integer (7 ⊖ 0))) t × OD (#fn·mir‿loop (number 5) #z1 t))
positive-horn = snd positive-result

to-minus-seven : S.Overflowing word (0 ⊖ 7) (0 ⊖ 7) false
to-minus-seven = S.exact-result (witness (S.inside? word (0 ⊖ 7)) tt) refl

to-minus-eight : S.Overflowing word (0 ⊖ 8) (0 ⊖ 8) false
to-minus-eight = S.exact-result (witness (S.inside? word (0 ⊖ 8)) tt) refl

lower-overflow : S.Overflowing word (0 ⊖ 9) (7 ⊖ 0) true
lower-overflow = S.overflow-result (S.rejected word S.addition (0 ⊖ 8) (0 ⊖ 1) refl)
  (witness (S.inside? word (7 ⊖ 0)) tt)

negative-run : Run program loop-add
  (M.advance loop-add 0 (M.initial (M.integer (0 ⊖ 6) ∷ M.integer (0 ⊖ 1) ∷ [])))
  (M.some (M.integer (0 ⊖ 8)))
negative-run = E.execution (0 ⊖ 6) (0 ⊖ 1)
  (E.again to-minus-seven (E.again to-minus-eight (E.overflow lower-overflow)))

negative-ground : ∀ {t} → GroundWS t ˢZ → GroundWS (#neg t) ˢZ
negative-ground (g , w) = (λ { x (arg (hd o)) → g x o ; x (arg (tl ())) }) , node refl (w ∷ [])

module Negative = E.ForInputs (0 ⊖ 6) (0 ⊖ 1) (#neg (number 6)) (#neg #z1)
  (negative-ground (number-ground 6)) (negative-ground (g0 refl refl)) refl refl

negative-result : Negative.Post (M.some (M.integer (0 ⊖ 8)))
negative-result = Negative.sound (witness (S.inside? word (0 ⊖ 6)) tt) negative-run

-- A successful intrinsic may use a numerically equal representation.
-- The invariant must transport its range and Horn witness accordingly.
noncanonical-six : S.Overflowing word (6 ⊖ 0) (7 ⊖ 1) false
noncanonical-six = S.exact-result (witness (S.inside? word (6 ⊖ 0)) tt) refl

canonical-seven : S.Overflowing word (8 ⊖ 1) (7 ⊖ 0) false
canonical-seven = S.exact-result (witness (S.inside? word (8 ⊖ 1)) tt) refl

noncanonical-run : Run program loop-add
  (M.advance loop-add 0 (M.initial (M.integer (5 ⊖ 0) ∷ M.integer (1 ⊖ 0) ∷ [])))
  (M.some (M.integer (7 ⊖ 0)))
noncanonical-run = E.execution (5 ⊖ 0) (1 ⊖ 0)
  (E.again noncanonical-six (E.again canonical-seven (E.overflow upper-overflow)))

noncanonical-result : Positive.Post (M.some (M.integer (7 ⊖ 0)))
noncanonical-result = Positive.sound (witness (S.inside? word (5 ⊖ 0)) tt) noncanonical-run

-- A cycle with no return demonstrates that paths-sound does not assume
-- termination, even when the proposed postcondition is uninhabited.
spin : M.Function
spin = M.function [] M.option-type (M.option-type ∷ []) (M.block [] (M.goto 0) ∷ [])

SpinInvariant : ℕ → M.Store → Set
SpinInvariant bb s = bb ≡ 0

spin-closed : ∀ bb s → SpinInvariant bb s → Paths [] spin SpinInvariant (λ _ → ⊥) (M.advance spin bb s)
spin-closed .0 s refl = cut refl

spin-cannot-return : ∀ {v} → Run [] spin (M.advance spin 0 (M.initial [])) v → ⊥
spin-cannot-return = paths-sound [] spin SpinInvariant (λ _ → ⊥) spin-closed (cut refl)
