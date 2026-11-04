{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Instantiations of the check-removal theorem, checked by evaluation and
-- proofs rather than an external test runner. The loop has observable
-- writes and no iteration bound; the unknown action may change all state.
------------------------------------------------------------------------
module CheckRemovalExamples where

open import Schematic using
  (ℕ; zero; suc; Bool; true; false; []; _∷_; _≡_; refl; _×_; _,_; Σ; ⊤; tt)
open import CheckRemoval

data Action : Set where
  decrement unknown : Action

data Guard : Set where
  nonzero always never : Guard

test : Guard → ℕ → Bool
test nonzero zero    = false
test nonzero (suc _) = true
test always  _      = true
test never   _      = false

open Semantics ℕ ℕ Action Guard test public

data Act : Action → ℕ → Observation → ℕ → Set where
  dec : ∀ {n} → Act decrement (suc n) (emit n) n
  any : ∀ {s t} → Act unknown s silent t

open WithActions Act public

code : Code
code zero = branch nonzero 1 4
code (suc zero) = checked nonzero decrement 2
code (suc (suc zero)) = assert always 3
code (suc (suc (suc zero))) = jump 0
code (suc (suc (suc (suc zero)))) = return
code (suc (suc (suc (suc (suc zero))))) = trap
code (suc (suc (suc (suc (suc (suc zero)))))) = assert never 4
code (suc (suc (suc (suc (suc (suc (suc _))))))) = effect unknown 0

remove : ℕ → Bool
remove (suc zero) = true
remove (suc (suc zero)) = true
remove _ = false

invariant : ℕ → ℕ → Set
invariant (suc zero) s = test nonzero s ≡ true
invariant (suc (suc (suc (suc zero)))) s = s ≡ 0
invariant _          s = ⊤

post : ℕ → Set
post s = s ≡ 0

open Conditions invariant post public

false-is-zero : ∀ {s} → test nonzero s ≡ false → s ≡ 0
false-is-zero {zero} _ = refl
false-is-zero {suc s} ()

conditions : ∀ pc → vc (code pc) (remove pc) (invariant pc)
conditions zero = (λ h q → q) , (λ h q → false-is-zero q)
conditions (suc zero) = (λ h → h) , (λ h q r → tt)
conditions (suc (suc zero)) = (λ h → refl) , (λ h q → tt)
conditions (suc (suc (suc zero))) = λ h → tt
conditions (suc (suc (suc (suc zero)))) = λ h → h
conditions (suc (suc (suc (suc (suc zero))))) = tt
conditions (suc (suc (suc (suc (suc (suc zero)))))) = tt , (λ h ())
conditions (suc (suc (suc (suc (suc (suc (suc _))))))) = λ h r → tt

open TraceTheorem.Proved invariant post code remove conditions

-- Zero iterations and one iteration, with the observable decrement.
zero-run : Run code (running 0 0) (silent ∷ silent ∷ []) (done 0)
zero-run = next (branch-false refl) (next return-step stop)

one-run : Run code (running 0 1)
  (silent ∷ emit 0 ∷ silent ∷ silent ∷ silent ∷ silent ∷ []) (done 0)
one-run = next (branch-true refl)
  (next (checked-pass refl dec)
    (next (assert-pass refl)
      (next jump-step zero-run)))

erased-one-run : Run (erase remove code) (running 0 1)
  (silent ∷ emit 0 ∷ silent ∷ silent ∷ silent ∷ silent ∷ []) (done 0)
erased-one-run = Schematic.Σ.fst (forward-run tt one-run)

restored-one-run : Run code (running 0 1)
  (silent ∷ emit 0 ∷ silent ∷ silent ∷ silent ∷ silent ∷ []) (done 0)
restored-one-run = Schematic.Σ.fst (backward-run tt erased-one-run)

-- A failure left in the code still fails, in both directions.
retained-failure : ∀ s → Run code (running 6 s) (silent ∷ []) failed
retained-failure s = next (assert-fail refl) stop

erased-failure : ∀ s → Run (erase remove code) (running 6 s) (silent ∷ []) failed
erased-failure s = Schematic.Σ.fst (forward-run tt (retained-failure s))

-- Opaque memory effects are universally quantified: even changing the
-- counter to an arbitrary value must preserve the destination invariant.
unknown-step : ∀ s t → Step (erase remove code) (running 7 s) silent (running 0 t) × Good (running 0 t)
unknown-step s t = Conditions.Verified.forward invariant post code remove conditions
  {c = running 7 s} {t = running 0 t} tt (effect-step any)

-- An unbounded cycle, showing there is no hidden decreasing fuel in vc.
cycle : Code
cycle _ = jump 0

cycle-conditions : ∀ pc → vc (cycle pc) false (λ _ → ⊤)
cycle-conditions _ _ = tt

-- Checked failure is retained too, even where the primitive has no result.
checked-failure : Execute (erase-one false (checked never decrement 0)) 0 silent failed
checked-failure = checked-fail refl

-- Traps and returns are unchanged by a removal bit.
trap-preserved : ∀ s → Execute (erase-one true trap) s silent failed
trap-preserved _ = trap-step
