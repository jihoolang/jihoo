{-# OPTIONS --safe --without-K #-}
-- The result boundary for an implicational certificate. Rule hypotheses
-- may occur inside its proof, but only the stated plain hypotheses may
-- remain when its result is connected to Adequacy.sound.
module ImplicationBridge where

open import Schematic
open import Implication

module In (Sg : Signature) (R : List Rule) (M : Rules.Model Sg R) where
  open CalculusIn Sg R M
  open ImplicationsIn Sg R M

  -- Explicit context inclusion: this permits reordering and contraction,
  -- but never discards an undischarged hypothesis.
  weaken : {H K : List RHyp} {J : Tm}
         → (∀ {h} → h ∈ H → h ∈ K) → ValidR H J → ValidR K J
  weaken {H} {K} {J} inc valid γ gw sats = valid γ gw′ (select H (λ m → m))
    where
      put : ∀ {x h ks} → h ∈ ks → Fixed h x → Any (λ h → Fixed h x) ks
      put (here refl) p = here p
      put (there m) p = there (put m p)

      fixed : ∀ {x} {hs : List RHyp}
            → (∀ {h} → h ∈ hs → h ∈ K)
            → Any (λ h → Fixed h x) hs → Any (λ h → Fixed h x) K
      fixed f (here p) = put (f (here refl)) p
      fixed f (there p) = fixed (λ m → f (there m)) p

      gw′ : GW γ (VarsR H J)
      gw′ x (inl o) = gw x (inl o)
      gw′ x (inr o) = gw x (inr (fixed inc o))

      select : (hs : List RHyp) → (∀ {h} → h ∈ hs → h ∈ H) → All (Sat γ) hs
      select [] f = []
      select (h ∷ hs) f = all-∈ sats (inc (f (here refl))) ∷ select hs (λ m → f (there m))

  plain-fixed : {x : ℕ} {H : List Tm}
              → Any (λ h → Fixed h x) (map plainR H) → Any (Occ x) H
  plain-fixed {H = h ∷ hs} (here (inl o , _)) = here o
  plain-fixed {H = h ∷ hs} (here (inr () , _))
  plain-fixed {H = h ∷ hs} (there o) = there (plain-fixed o)

  -- Convert the implicational calculus to the exact semantic interface
  -- used by Adequacy. No postulate or executable checker is trusted here.
  to-valid : {H : List Tm} {J : Tm} → ValidR (map plainR H) J → Valid H J
  to-valid {H} {J} valid γ gw hs = valid γ gw′ (sats H (λ m → m) hs)
    where
      gw′ : GW γ (VarsR (map plainR H) J)
      gw′ x (inl o) = gw x (inl o)
      gw′ x (inr o) = gw x (inr (plain-fixed o))

      sats : (ps : List Tm) → (∀ {p} → p ∈ ps → p ∈ H)
           → All (λ p → Holds (sub γ p)) ps → All (Sat γ) (map plainR ps)
      sats [] inc [] = []
      sats (p ∷ ps) inc (d ∷ ds) =
        sat-plain γ p (λ x o → gw x (inr (put (inc (here refl)) o))) d
        ∷ sats ps (λ m → inc (there m)) ds
        where
          put : ∀ {x p hs} → p ∈ hs → Occ x p → Any (Occ x) hs
          put (here refl) o = here o
          put (there m) o = there (put m o)

  result : {H : List RHyp} {Ps : List Tm} {J : Tm}
         → (∀ {h} → h ∈ H → h ∈ map plainR Ps)
         → ValidR H J → Valid Ps J
  result inc proof = to-valid (weaken inc proof)

  -- Ordinary checked facts can also be used as implicational lemmas.
  -- Together with to-valid, this ensures the result boundary does not
  -- strengthen or weaken the meaning of a plain-hypothesis goal.
  from-valid : {H : List Tm} {J : Tm} → Valid H J → ValidR (map plainR H) J
  from-valid {H} {J} valid γ gw sats = valid γ gw′
    (sats-plain γ H (λ x o → gw x (inr (occs-plain H o))) sats)
    where
      lift : ∀ {x hs} → Any (Occ x) hs → Any (λ h → Fixed h x) (map plainR hs)
      lift (here o) = here (inl o , λ ())
      lift (there o) = there (lift o)

      gw′ : GW γ (Vars H J)
      gw′ x (inl o) = gw x (inl o)
      gw′ x (inr o) = gw x (inr (lift o))
