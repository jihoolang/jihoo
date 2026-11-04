{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Compose the typed backing-store specification with the generated Horn
-- len/nth/snoc relations, for every represented vector and successful
-- operation. The memory operations do not assume these Horn relations.
------------------------------------------------------------------------
module VecHornExecution where

open import Schematic
open import Theory
open import Adequacy using (OrderedRing; module Adequate; sig)
import ListExecution as L
import VecMemory as V
open Σ
open Rules sig rules using (GroundWS)

module Bridge (S : L.ListSignature) (present : L.Schemas.Present S) (Rg : OrderedRing) where
  module E = L.Execution S present Rg
  module M = V.Memory E.Value
  open L.Schemas S
  open Adequate Rg using (OD; ⟦_⟧)
  open OrderedRing Rg using (_≈ᴿ_)

  sizes : (xs : List E.Value) → V.size xs ≡ L.size xs
  sizes [] = refl
  sizes (_ ∷ xs) = cong suc (sizes xs)

  length-horn : ∀ {v xs} → M.Represents v xs
              → OD (len (E.encode xs) (L.number (M.length v)))
  length-horn {v} {xs} rep = transport (λ n → OD (len (E.encode xs) (L.number n)))
    (sym (trans (M.count rep) (sizes xs))) (E.length-execution xs)

  index-horn : ∀ {v xs i x} → M.Represents v xs → M.index v i ≡ just x
             → OD (index (E.encode xs) (L.number i) (fst x))
  index-horn {xs = xs} {i} {x} rep found = E.index-execution xs i x
    (trans (sym (M.index-exact rep i)) found)

  -- MIR indices can have any ground spelling with the right integer
  -- value. Capacity, spare cells and relocation do not enter that value.
  index-horn-at : ∀ {v xs i x t} → M.Represents v xs → M.index v i ≡ just x
                → GroundWS t ˢZ → ⟦ t ⟧ ≈ᴿ ⟦ L.number i ⟧
                → OD (index (E.encode xs) t (fst x))
  index-horn-at {xs = xs} {i} {x} {t} rep found gt value = E.index-execution-at xs i x t gt value
    (trans (sym (M.index-exact rep i)) found)

  reserve-preserves : ∀ {v xs cap w} → M.Represents v xs → M.reserve-to v cap ≡ just w
                    → M.Represents w xs × OD (len (E.encode xs) (L.number (M.length w)))
  reserve-preserves rep copied = M.reserve-sound rep copied , length-horn (M.reserve-sound rep copied)

  push-horn : ∀ {v xs cap x w} → M.Represents v xs → M.push v cap x ≡ just w
            → M.Represents w (xs ++ (x ∷ []))
              × OD (snoc (E.encode xs) (fst x) (E.encode (xs ++ (x ∷ []))))
  push-horn {xs = xs} {x = x} rep wrote = M.push-sound rep wrote , E.push-execution xs x

module Terms (Rg : OrderedRing) = Bridge L.terms L.terms-present Rg
module Facts (Rg : OrderedRing) = Bridge L.facts L.facts-present Rg
module Weights (Rg : OrderedRing) = Bridge L.weights L.weights-present Rg
