#!/usr/bin/env bash
# Run in a temporary directory containing Horn's and jihoo's Agda modules.
# Each mutation must be rejected by Agda, not by the exporter or Rust checker.
set -euo pipefail
agda --safe --no-libraries -i . -i horn ImplicationBridgeTests.agda
cat > DiscardedHypothesis.agda <<'AGDA'
{-# OPTIONS --safe --without-K #-}
module DiscardedHypothesis where
open import Schematic
open import Implication
open import ImplicationBridge
module Bad (Sg : Signature) (R : List Rule) (M : Rules.Model Sg R) where
  open CalculusIn Sg R M
  open ImplicationsIn Sg R M
  open In Sg R M
  bad : (j : Tm) → Valid [] j
  bad j = result (λ ()) (assume-valid j)
AGDA
if agda --safe --no-libraries -i . -i horn DiscardedHypothesis.agda > discarded.log 2>&1; then
  echo 'Agda accepted a discarded hypothesis' >&2
  exit 1
fi
grep -q '\[ShouldBeEmpty\]' discarded.log
cat > GeneralizedHypothesis.agda <<'AGDA'
{-# OPTIONS --safe --without-K #-}
module GeneralizedHypothesis where
open import Schematic
open import Implication
open import ImplicationBridge
module Bad (Sg : Signature) (R : List Rule) (M : Rules.Model Sg R) where
  open CalculusIn Sg R M
  open ImplicationsIn Sg R M
  open In Sg R M
  bad : (j : Tm) → ValidR (rhyp [] j (0 ∷ []) ∷ []) j → Valid (j ∷ []) j
  bad j p = result (λ { (here refl) → here refl }) p
AGDA
if agda --safe --no-libraries -i . -i horn GeneralizedHypothesis.agda > generalized.log 2>&1; then
  echo 'Agda accepted a generalized hypothesis as a plain result premise' >&2
  exit 1
fi
grep -q '\[UnequalTerms\]' generalized.log
echo 'implication bridge: checked; discarded and generalized hypotheses rejected'
