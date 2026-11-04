{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Connecting the checked Farkas certificate to semantic check removal.
--
-- A guard's certificate is useful only if the facts describe every
-- invariant state and failure of the guard makes the claim negative.
-- `guard-holds` combines those connections with Certified.check-sound;
-- it discharges the guard VC without trusting a prover or Horn checker.
-- The continuation VC is still needed: opaque writes and control flow
-- must preserve the invariant used to justify the next removal.
--
-- `accepted` is still the generated Horn relation, not a MIR execution.
-- Execution-to-Horn correspondence, the concrete MIR-to-model mapping,
-- invariant generation and contract dependencies remain release gates.
------------------------------------------------------------------------
module CertifiedRemoval where

open import Schematic
open import Theory
open import Adequacy
import Certified
import CheckRemoval
open Rules sig rules using (GroundWS)

module Bridge (Rg : OrderedRing) (State Guard : Set)
  (test : Guard → State → Bool) where
  open OrderedRing Rg using (_+ᴿ_; _≤ᴿ_; 1ᴿ; 0ᴿ)
  open Adequate Rg using (OD; Facts; val)
  open Certified.Certified Rg using (check-sound)

  record GuardCertificate (p : State → Set) (g : Guard) : Set where
    field
      fs cl ws used : Tm
      facts-ground : GroundWS fs ˢVec⟨Lin⟩
      claim-ground : GroundWS cl ˢLin
      weights-ground : GroundWS ws ˢVec⟨i128⟩
      used-ground : GroundWS used ˢZ
      accepted : OD (#fn·check (#Goal·mk fs cl) (#Certificate·mk ws) (#Result⟨i64ˌstr⟩·Ok used))
      state-point : State → Tm
      point-ground : ∀ s → GroundWS (state-point s) ˢX
      facts-hold : ∀ {s} → p s → Facts (state-point s) fs
      failure-negative : ∀ {s} → p s → test g s ≡ false → val cl (state-point s) +ᴿ 1ᴿ ≤ᴿ 0ᴿ

  guard-holds : ∀ {p g s} → GuardCertificate p g → p s → test g s ≡ true
  guard-holds {g = g} {s = s} cert h with test g s in eq
  ... | true = refl
  ... | false = ⊥-elim (check-sound (facts-ground cert) (claim-ground cert)
      (weights-ground cert) (used-ground cert) (point-ground cert s)
      (accepted cert) (facts-hold cert h) (failure-negative cert h eq))
    where open GuardCertificate

  -- These constructors discharge precisely the guard part of the local
  -- conditions in CheckRemoval. The rest must be proved independently.
  module ForSemantics (Event Action : Set) where
    open CheckRemoval.Semantics State Event Action Guard test

    module ForActions (act : Action → State → Observation → State → Set) where
      open WithActions act

      module ForConditions (invariant : ℕ → State → Set) (post : State → Set) where
        open Conditions invariant post

        assert-vc : ∀ {pc g k}
                  → GuardCertificate (invariant pc) g
                  → (∀ {s} → invariant pc s → test g s ≡ true → invariant k s)
                  → vc (assert g k) true (invariant pc)
        assert-vc cert continuation = guard-holds cert , continuation

        checked-vc : ∀ {pc g a k}
                   → GuardCertificate (invariant pc) g
                   → (∀ {s e t} → invariant pc s → test g s ≡ true → act a s e t → invariant k t)
                   → vc (checked g a k) true (invariant pc)
        checked-vc cert continuation = guard-holds cert , continuation

-- The same composition in the integers, where the certificate is used by
-- the compiler. It does not assume completeness of the prover.
open import Integers using (ℤ-ring)
module InIntegers = Bridge ℤ-ring
