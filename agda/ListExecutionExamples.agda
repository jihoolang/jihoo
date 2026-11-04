{-# OPTIONS --safe --without-K #-}
module ListExecutionExamples where

open import Schematic
open import Theory
open import Adequacy using (module Adequate; gz0)
open import Integers using (ℤ-ring)
open import ListExecution
open Adequate ℤ-ring using (OD)

module T = Terms ℤ-ring
module F = Facts ℤ-ring
module W = Weights ℤ-ring

coefficient : T.Value
coefficient = #Tup⟨ZˌZ⟩·mk #z0 #z1 , g2 refl refl gz0 (g0 refl refl)

form : F.Value
form = #Lin·mk #Vec⟨⟨i64ˌi128⟩⟩·nil #z0 , g2 refl refl (T.encode-ground []) gz0

weight : W.Value
weight = #z1 , g0 refl refl

terms-index : OD (Schemas.index terms (T.encode (coefficient ∷ coefficient ∷ [])) (number 1) (Σ.fst coefficient))
terms-index = T.index-execution (coefficient ∷ coefficient ∷ []) 1 coefficient refl

facts-length : OD (Schemas.len facts (F.encode (form ∷ form ∷ [])) (number 2))
facts-length = F.length-execution (form ∷ form ∷ [])

weights-push : OD (Schemas.snoc weights (W.encode (weight ∷ [])) #z1 (W.encode (weight ∷ weight ∷ [])))
weights-push = W.push-execution (weight ∷ []) weight

-- z1 is the machine index 1; number 1 has the spelling add z0 z1.
-- The semantic equality connects them without identifying their syntax.
weights-computed-index : OD (Schemas.index weights (W.encode (weight ∷ weight ∷ [])) #z1 #z1)
weights-computed-index = W.index-execution-at (weight ∷ weight ∷ []) 1 weight #z1
  (g0 refl refl) refl refl
