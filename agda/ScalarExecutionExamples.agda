{-# OPTIONS --safe --without-K #-}
module ScalarExecutionExamples where

open import Schematic
open import Theory
open import Adequacy using (module Adequate)
open import Integers using (ℤ; _⊖_; ℤ-ring)
open import ListExecution using (number; number-ground; g0)
open import ScalarExecution
open Adequate ℤ-ring using (OD)

-- Four-bit signed examples exercise both inclusive bounds, overflow on
-- either side, negative multiplication and noncanonical integer values.
word : Bounds
word = signed 3

upper-inclusive : checked word addition (7 ⊖ 0) (0 ⊖ 0) ≡ just (7 ⊖ 0)
upper-inclusive = refl

lower-inclusive : checked word addition (0 ⊖ 8) (0 ⊖ 0) ≡ just (0 ⊖ 8)
lower-inclusive = refl

positive-overflow : checked word addition (7 ⊖ 0) (1 ⊖ 0) ≡ nothing
positive-overflow = refl

negative-overflow : checked word addition (0 ⊖ 8) (0 ⊖ 1) ≡ nothing
negative-overflow = refl

negating-minimum : checked word multiplication (0 ⊖ 8) (0 ⊖ 1) ≡ nothing
negating-minimum = refl

negative-product : checked word multiplication (0 ⊖ 2) (3 ⊖ 0) ≡ just (0 ⊖ 6)
negative-product = refl

cancellation : Same (just (0 ⊖ 0)) (checked word addition (0 ⊖ 7) (7 ⊖ 0))
cancellation = present refl

add-witness : Σ Tm (λ r → Represents (just (5 ⊖ 0)) r × OD (#fn·add (number 2) (number 3) r))
add-witness = checked-execution word addition (2 ⊖ 0) (3 ⊖ 0) (number 2) (number 3)
  (number-ground 2) (number-ground 3) refl refl

overflow-witness : Σ Tm (λ r → Represents nothing r × OD (#fn·add (number 7) #z1 r))
overflow-witness = checked-execution word addition (7 ⊖ 0) (1 ⊖ 0) (number 7) #z1
  (number-ground 7) (g0 refl refl) refl refl

-- The returned value need only be numerically equal to the exact result.
intrinsic-witness : Σ Tm (λ r → Represents (just (6 ⊖ 1)) r × OD (#fn·add (number 2) (number 3) r))
intrinsic-witness = intrinsic-execution word addition (2 ⊖ 0) (3 ⊖ 0) (6 ⊖ 1) false
  (number 2) (number 3) (number-ground 2) (number-ground 3) refl refl
  (exact-result (witness (inside? word (5 ⊖ 0)) tt) refl)

overflowing-call : Overflowing word (8 ⊖ 0) (0 ⊖ 8) true
overflowing-call = overflow-result (rejected word addition (7 ⊖ 0) (1 ⊖ 0) positive-overflow)
  (witness (inside? word (0 ⊖ 8)) tt)

projected-overflow : Same nothing (checked word addition (7 ⊖ 0) (1 ⊖ 0))
projected-overflow = projection-correct word addition (7 ⊖ 0) (1 ⊖ 0) (0 ⊖ 8) true overflowing-call
