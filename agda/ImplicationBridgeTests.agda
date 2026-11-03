{-# OPTIONS --safe --without-K #-}
module ImplicationBridgeTests where

open import Schematic
open import Implication
open import ImplicationBridge

module Examples (Sg : Signature) (R : List Rule) (M : Rules.Model Sg R) where
  open CalculusIn Sg R M
  open ImplicationsIn Sg R M
  open In Sg R M

  identity : (j : Tm) → Valid (j ∷ []) j
  identity j = to-valid (assume-valid j)

  duplicate : (j : Tm) → Valid (j ∷ j ∷ []) j
  duplicate j = result (λ { (here refl) → here refl }) (assume-valid j)

  reordered : (j k : Tm) → Valid (k ∷ j ∷ []) j
  reordered j k = result (λ { (here refl) → there (here refl) }) (assume-valid j)

  roundtrip : (j : Tm) → Valid (j ∷ []) j
  roundtrip j = to-valid (from-valid (identity j))
