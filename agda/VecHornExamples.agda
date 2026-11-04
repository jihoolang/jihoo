{-# OPTIONS --safe --without-K #-}
module VecHornExamples where

open import Schematic
open import Theory
open import Adequacy using (module Adequate; gz0)
open import Integers using (ℤ-ring)
open import ListExecution using (g0; g2; number; module Schemas; terms; facts; weights)
import VecHornExecution as V
open Adequate ℤ-ring using (OD)

module T = V.Terms ℤ-ring
module F = V.Facts ℤ-ring
module W = V.Weights ℤ-ring

coefficient : T.E.Value
coefficient = #Tup⟨ZˌZ⟩·mk #z0 #z1 , g2 refl refl gz0 (g0 refl refl)

form : F.E.Value
form = #Lin·mk #Vec⟨⟨i64ˌi128⟩⟩·nil #z0 , g2 refl refl (T.E.encode-ground []) gz0

weight : W.E.Value
weight = #z1 , g0 refl refl

term-buffer : T.M.Vector
term-buffer = T.M.vector (just coefficient ∷ nothing ∷ []) 1 2

terms-represented : T.M.Represents term-buffer (coefficient ∷ [])
terms-represented = T.M.represents (T.M.initialized T.M.empty) refl (inr refl)

terms-index : OD (Schemas.index terms (T.E.encode (coefficient ∷ [])) (number 0) (Σ.fst coefficient))
terms-index = T.index-horn {i = 0} {x = coefficient} terms-represented refl

fact-buffer : F.M.Vector
fact-buffer = F.M.vector (just form ∷ just form ∷ nothing ∷ []) 2 3

facts-represented : F.M.Represents fact-buffer (form ∷ form ∷ [])
facts-represented = F.M.represents (F.M.initialized (F.M.initialized F.M.empty)) refl (inr refl)

facts-length : OD (Schemas.len facts (F.E.encode (form ∷ form ∷ [])) (number 2))
facts-length = F.length-horn facts-represented

borrowed-weights : W.M.Vector
borrowed-weights = W.M.vector (just weight ∷ just weight ∷ []) 2 0

weights-represented : W.M.Represents borrowed-weights (weight ∷ weight ∷ [])
weights-represented = W.M.represents (W.M.initialized (W.M.initialized W.M.empty)) refl (inl refl)

weights-computed-index : OD (Schemas.index weights (W.E.encode (weight ∷ weight ∷ [])) #z1 #z1)
weights-computed-index = W.index-horn-at {i = 1} {x = weight} weights-represented refl (g0 refl refl) refl

owned-weights : W.M.Vector
owned-weights = W.M.vector (just weight ∷ just weight ∷ just weight ∷ nothing ∷ []) 3 4

weights-push : W.M.Represents owned-weights (weight ∷ weight ∷ weight ∷ [])
             × OD (Schemas.snoc weights (W.E.encode (weight ∷ weight ∷ [])) #z1
                    (W.E.encode (weight ∷ weight ∷ weight ∷ [])))
weights-push = W.push-horn {cap = 4} weights-represented refl
