{-# OPTIONS --safe --without-K #-}
module MirExecutionExamples where

open import Schematic
open import Theory
open import Adequacy using (sig; module Adequate)
open import Integers using (_⊖_; ℤ-ring)
import ScalarExecution as S
import MirExecution as M
open import GeneratedMir
open import MirCorrespondence
open import ListExecution using (number; number-ground)
open Rules sig rules using (GroundWS)
open Adequate ℤ-ring using (OD)

-- Small bounds exercise both flag paths without enumerating i128 values.
-- MirCorrespondence.InI128 is the actual checker's intrinsic instance.
word : S.Bounds
word = S.signed 3

module E = Proofs word
open M.Semantics word

normal : S.Overflowing word (5 ⊖ 0) (5 ⊖ 0) false
normal = S.exact-result (witness (S.inside? word (5 ⊖ 0)) tt) refl

overflow : S.Overflowing word (8 ⊖ 0) (0 ⊖ 8) true
overflow = S.overflow-result (S.rejected word S.addition (7 ⊖ 0) (1 ⊖ 0) refl)
  (witness (S.inside? word (0 ⊖ 8)) tt)

helper-normal : Run program helper-add (M.advance helper-add 0 (E.start (2 ⊖ 0) (3 ⊖ 0))) (M.some (M.integer (5 ⊖ 0)))
helper-normal = E.helper-add-execution normal

caller-normal : Run program caller-add (M.advance caller-add 0 (E.start (2 ⊖ 0) (3 ⊖ 0))) (M.some (M.integer (5 ⊖ 0)))
caller-normal = E.caller-add-execution normal

caller-overflow : Run program caller-add (M.advance caller-add 0 (E.start (7 ⊖ 0) (1 ⊖ 0))) M.none
caller-overflow = E.caller-add-execution overflow

caller-model : Σ Tm (λ t → Represents (M.some (M.integer (5 ⊖ 0))) t × OD (#fn·mir‿add (number 2) (number 3) t))
caller-model = E.caller-add-horn (2 ⊖ 0) (3 ⊖ 0) (number 2) (number 3)
  (number-ground 2) (number-ground 3) refl refl caller-normal

-- Lifetime markers clear the frame: a stale read must not give a value.
read-after-dead : M.statements-step
  (M.live 3 ∷ M.assign 3 (M.use (M.local 1 [])) ∷ M.dead 3 ∷ M.assign 0 (M.use (M.local 3 [])) ∷ [])
  (E.start (2 ⊖ 0) (3 ⊖ 0)) ≡ nothing
read-after-dead = refl

bad-projection : M.read (E.start (2 ⊖ 0) (3 ⊖ 0)) (M.local 1 (0 ∷ [])) ≡ nothing
bad-projection = refl
