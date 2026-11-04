{-# OPTIONS --safe --without-K #-}
module MissingBranch where

open import Schematic using (false; refl; _,_; tt)
open import CheckRemovalExamples

-- The false branch of the test reaches block 1 with a zero counter.
-- Checking only the other branch would accept this unsafe invariant.
bad : vc (branch nonzero 0 1) false (invariant 0)
bad = (λ h q → tt) , (λ h q → refl)
