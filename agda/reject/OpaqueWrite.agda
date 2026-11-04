{-# OPTIONS --safe --without-K #-}
module OpaqueWrite where

open import Schematic using (false; refl)
open import CheckRemovalExamples

-- An unknown write can set the counter to zero; the next block needs it
-- nonzero. A true guard alone cannot justify the destination invariant.
bad : vc (effect unknown 1) false (invariant 0)
bad h r = refl
