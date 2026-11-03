{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- The linear checker is sound, with no premise left.
--
-- Adequacy.agda reads the theory of lib/proof/refine.jh in an ordered
-- commutative ring and proves: if the goal is valid there, `check`
-- returning `Ok` means no point satisfies the facts and the negated
-- claim. Validity was a premise, established by jihoo's own Horn checker.
--
-- CheckCertificate.agda is the certificate refine.jh produces, exported
-- by Horn's `schematic-kernel --agda` (untrusted) and checked here by
-- Agda running Horn's checker, which agda/ImplicationCheck.agda proves
-- sound in every model of the rules. Its signature gives sorts to every
-- variable of the certificate, Adequacy's to the goal's five; `Transfer`
-- moves the ring's model across, since the two agree on every symbol and
-- on the goal's variables. The theory and the goal are the same terms in
-- both, which Agda checks by conversion.
------------------------------------------------------------------------
module Certified where

open import Schematic
open import ImplicationCheck using (module Transfer; module Meaning)
open import Theory
open import Adequacy
import CheckCertificate as Cert
open Σ
open Rules sig rules using (GroundWS)

-- The goal's variables have the same sorts in both signatures.
agree : ∀ x → Calculus.Vars sig rules goalH goalJ x → Signature.vs sig x ≡ Signature.vs Cert.sig x
agree x v = all-∈ (witness (all? (λ y → Signature.vs sig y ≟ Signature.vs Cert.sig y) goalVars) tt) (inVars v)
  where
    goalVars : List ℕ
    goalVars = vars goalJ ++ varss goalH

    inVars : Calculus.Vars sig rules goalH goalJ x → x ∈ goalVars
    inVars (inl o) = any-++ˡ (occ-vars goalJ o)
    inVars (inr a) = any-++ʳ (vars goalJ) (occs-varss goalH (any-occs a))

module Certified (Rg : OrderedRing) where
  open OrderedRing Rg using (_+ᴿ_; 1ᴿ; 0ᴿ; _≤ᴿ_)
  open Adequate Rg

  private
    module T = Transfer sig Cert.sig rules (λ f → refl) (λ f → refl)

    first : {A : Set} {P : A → Set} {a : A} → All P (a ∷ []) → P a
    first (p ∷ []) = p

  -- The premise of Adequacy.sound, from the checked certificate.
  valid : CalculusIn.Valid sig rules model goalH goalJ
  valid = T.valid-back model agree (first (Cert.theorem (T.model model)))

  -- When `check` returns `Ok` for facts fs, claim cl and weights ws (its
  -- rules hold of those values), no point x of the ring makes every fact
  -- non-negative and the claim negative.
  check-sound : {fs cl ws m x : Tm}
              → GroundWS fs ˢVec⟨Lin⟩ → GroundWS cl ˢLin → GroundWS ws ˢVec⟨i128⟩ → GroundWS m ˢZ → GroundWS x ˢX
              → OD (#fn·check (#Goal·mk fs cl) (#Certificate·mk ws) (#Result⟨i64ˌstr⟩·Ok m))
              → Facts x fs
              → val cl x +ᴿ 1ᴿ ≤ᴿ 0ᴿ
              → ⊥
  check-sound = sound valid

-- In the integers (Integers.agda).
open import Integers using (ℤ-ring)

module InIntegers = Certified ℤ-ring
