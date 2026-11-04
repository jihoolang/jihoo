{-# OPTIONS --safe --without-K #-}
module RemovedFalseGuard where

open import Schematic using (true; _≡_; refl; _,_; tt)
open import CheckRemovalExamples

-- An attempted certificate for removing an assertion which always fails.
-- Agda must reject false ≡ true, rather than trust the removal mask.
bad : vc (assert never 0) true (invariant 0)
bad = (λ h → refl) , (λ h q → tt)
