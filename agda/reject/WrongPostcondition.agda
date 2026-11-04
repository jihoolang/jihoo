{-# OPTIONS --safe --without-K #-}
module WrongPostcondition where

open import Schematic using (false; refl)
open import CheckRemovalExamples

-- Returning immediately from an arbitrary counter does not establish
-- the loop's postcondition that the counter is zero.
bad : vc return false (invariant 0)
bad h = refl
