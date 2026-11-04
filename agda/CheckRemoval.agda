{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- A first semantics and check-removal theorem for the verifier (0.5).
--
-- The graph may have cycles. State and observable primitive operations
-- are parameters, including nondeterministic operations; guards are total.
-- A checked primitive is its unchecked operation guarded by a predicate.
-- Relating this assumption to machine arithmetic is a separate obligation.
-- Assertions, checked operations, branches, jumps, returns and traps have
-- small-step semantics. A removed check still takes one silent step.
--
-- `vc` computes the local semantic verification conditions for a proposed
-- invariant and removal mask. `forward` and `backward` prove that discharging
-- them gives a step-for-step correspondence, including retained failures.
-- `forward-run` and `backward-run` preserve every finite trace and final
-- configuration. Loops need no bound or termination assumption.
--
-- This is a specification to connect obligations.jh/vc.jh/verify.jh to,
-- not yet a proof that those implementations produce these conditions.
------------------------------------------------------------------------
module CheckRemoval where

open import Schematic using
  (ℕ; Bool; true; false; List; []; _∷_; _≡_; refl; _×_; _,_; Σ; ⊤; tt; ⊥; ⊥-elim)

module Semantics
  (State Event Action Guard : Set)
  (test : Guard → State → Bool)
  where

  data Observation : Set where
    silent : Observation
    emit   : Event → Observation

  -- The unchecked primitive's entire effect, including its observable
  -- event and any changes to memory. An opaque operation can have any
  -- transition; proving its VC must cover every one of them.
  module WithActions (act : Action → State → Observation → State → Set) where

    data Instruction : Set where
      effect  : Action → ℕ → Instruction
      checked : Guard → Action → ℕ → Instruction
      assert  : Guard → ℕ → Instruction
      branch  : Guard → ℕ → ℕ → Instruction
      jump    : ℕ → Instruction
      return  : Instruction
      trap    : Instruction

    Code : Set
    Code = ℕ → Instruction

    data Configuration : Set where
      running : ℕ → State → Configuration
      done    : State → Configuration
      failed  : Configuration

    data Execute : Instruction → State → Observation → Configuration → Set where
      effect-step : ∀ {a k s e t} → act a s e t
                  → Execute (effect a k) s e (running k t)
      checked-pass : ∀ {g a k s e t} → test g s ≡ true → act a s e t
                   → Execute (checked g a k) s e (running k t)
      checked-fail : ∀ {g a k s} → test g s ≡ false
                   → Execute (checked g a k) s silent failed
      assert-pass : ∀ {g k s} → test g s ≡ true
                  → Execute (assert g k) s silent (running k s)
      assert-fail : ∀ {g k s} → test g s ≡ false
                  → Execute (assert g k) s silent failed
      branch-true : ∀ {g yes no s} → test g s ≡ true
                  → Execute (branch g yes no) s silent (running yes s)
      branch-false : ∀ {g yes no s} → test g s ≡ false
                   → Execute (branch g yes no) s silent (running no s)
      jump-step : ∀ {k s} → Execute (jump k) s silent (running k s)
      return-step : ∀ {s} → Execute return s silent (done s)
      trap-step : ∀ {s} → Execute trap s silent failed

    Step : Code → Configuration → Observation → Configuration → Set
    Step code (running pc s) e t = Execute (code pc) s e t
    Step code (done _)       e t = ⊥
    Step code failed         e t = ⊥

    -- Exactly the two local erasures of verify.erase_one: an assertion
    -- becomes a jump, and checked arithmetic its unchecked operation.
    -- Panic removal and retargeting calls are not covered by this model.
    erase-one : Bool → Instruction → Instruction
    erase-one _ (effect a k)      = effect a k
    erase-one _ (branch g yes no) = branch g yes no
    erase-one _ (jump k)          = jump k
    erase-one _ return            = return
    erase-one _ trap              = trap
    erase-one true  (checked g a k) = effect a k
    erase-one false (checked g a k) = checked g a k
    erase-one true  (assert g k)    = jump k
    erase-one false (assert g k)    = assert g k

    erase : (ℕ → Bool) → Code → Code
    erase remove code pc = erase-one (remove pc) (code pc)

    module Conditions
      (invariant : ℕ → State → Set)
      (post : State → Set)
      where

      Good : Configuration → Set
      Good (running pc s) = invariant pc s
      Good (done s)       = post s
      Good failed         = ⊤

      -- An unremoved check needs no proof of its guard. Its successful
      -- continuation must still preserve the invariant. In particular,
      -- the invariant is not assumed after an arbitrary opaque write.
      GuardVC : Bool → Guard → (State → Set) → Set
      GuardVC false g p = ⊤
      GuardVC true  g p = ∀ {s} → p s → test g s ≡ true

      vc : Instruction → Bool → (State → Set) → Set
      vc (effect a k) remove p =
        ∀ {s e t} → p s → act a s e t → invariant k t
      vc (checked g a k) remove p = GuardVC remove g p ×
        (∀ {s e t} → p s → test g s ≡ true → act a s e t → invariant k t)
      vc (assert g k) remove p = GuardVC remove g p ×
        (∀ {s} → p s → test g s ≡ true → invariant k s)
      vc (branch g yes no) remove p =
        (∀ {s} → p s → test g s ≡ true → invariant yes s) ×
        (∀ {s} → p s → test g s ≡ false → invariant no s)
      vc (jump k) remove p = ∀ {s} → p s → invariant k s
      vc return remove p = ∀ {s} → p s → post s
      vc trap remove p = ⊤

      impossible : ∀ {b : Bool} → b ≡ true → b ≡ false → ⊥
      impossible refl ()

      -- Local forward simulation, with preservation of the destination's
      -- invariant. Neither a removed assertion nor a removed overflow
      -- check can take its failing branch in an invariant state.
      forward-one : ∀ {i b p s e t} → vc i b p → p s → Execute i s e t
                  → Execute (erase-one b i) s e t × Good t
      forward-one {effect a k} c h (effect-step r) = effect-step r , c h r
      forward-one {checked g a k} {false} (gvc , c) h (checked-pass q r) = checked-pass q r , c h q r
      forward-one {checked g a k} {false} c h (checked-fail q) = checked-fail q , tt
      forward-one {checked g a k} {true} (gvc , c) h (checked-pass q r) = effect-step r , c h q r
      forward-one {checked g a k} {true} (gvc , c) h (checked-fail q) = ⊥-elim (impossible (gvc h) q)
      forward-one {assert g k} {false} (gvc , c) h (assert-pass q) = assert-pass q , c h q
      forward-one {assert g k} {false} c h (assert-fail q) = assert-fail q , tt
      forward-one {assert g k} {true} (gvc , c) h (assert-pass q) = jump-step , c h q
      forward-one {assert g k} {true} (gvc , c) h (assert-fail q) = ⊥-elim (impossible (gvc h) q)
      forward-one {branch g yes no} (l , r) h (branch-true q) = branch-true q , l h q
      forward-one {branch g yes no} (l , r) h (branch-false q) = branch-false q , r h q
      forward-one {jump k} c h jump-step = jump-step , c h
      forward-one {return} c h return-step = return-step , c h
      forward-one {trap} c h trap-step = trap-step , tt

      -- Backward simulation rules out introducing new behaviors when
      -- erasing checks, rather than only preserving successful runs.
      backward-one : ∀ {i b p s e t} → vc i b p → p s → Execute (erase-one b i) s e t
                   → Execute i s e t × Good t
      backward-one {effect a k} c h (effect-step r) = effect-step r , c h r
      backward-one {checked g a k} {false} (gvc , c) h (checked-pass q r) = checked-pass q r , c h q r
      backward-one {checked g a k} {false} c h (checked-fail q) = checked-fail q , tt
      backward-one {checked g a k} {true} (gvc , c) h (effect-step r) = checked-pass (gvc h) r , c h (gvc h) r
      backward-one {assert g k} {false} (gvc , c) h (assert-pass q) = assert-pass q , c h q
      backward-one {assert g k} {false} c h (assert-fail q) = assert-fail q , tt
      backward-one {assert g k} {true} (gvc , c) h jump-step = assert-pass (gvc h) , c h (gvc h)
      backward-one {branch g yes no} (l , r) h (branch-true q) = branch-true q , l h q
      backward-one {branch g yes no} (l , r) h (branch-false q) = branch-false q , r h q
      backward-one {jump k} c h jump-step = jump-step , c h
      backward-one {return} c h return-step = return-step , c h
      backward-one {trap} c h trap-step = trap-step , tt

      module Verified (code : Code) (remove : ℕ → Bool)
        (conditions : ∀ pc → vc (code pc) (remove pc) (invariant pc)) where

        forward : ∀ {c e t} → Good c → Step code c e t
                → Step (erase remove code) c e t × Good t
        forward {running pc s} h r = forward-one (conditions pc) h r
        forward {done _} h ()
        forward {failed} h ()

        backward : ∀ {c e t} → Good c → Step (erase remove code) c e t
                 → Step code c e t × Good t
        backward {running pc s} h r = backward-one (conditions pc) h r
        backward {done _} h ()
        backward {failed} h ()

    -- A run records every observation, including silent steps. The two
    -- simulations thus preserve visible traces as well as step counts.
    data Run (code : Code) : Configuration → List Observation → Configuration → Set where
      stop : ∀ {c} → Run code c [] c
      next : ∀ {c e d es t} → Step code c e d → Run code d es t → Run code c (e ∷ es) t

    module TraceTheorem
      (invariant : ℕ → State → Set)
      (post : State → Set)
      (code : Code) (remove : ℕ → Bool)
      where
      open Conditions invariant post

      module Proved (conditions : ∀ pc → vc (code pc) (remove pc) (invariant pc)) where
        open Verified code remove conditions

        forward-run : ∀ {c es t} → Good c → Run code c es t
                    → Run (erase remove code) c es t × Good t
        forward-run h stop = stop , h
        forward-run h (next r rs) with forward h r
        ... | q , hd with forward-run hd rs
        ...   | qs , ht = next q qs , ht

        backward-run : ∀ {c es t} → Good c → Run (erase remove code) c es t
                     → Run code c es t × Good t
        backward-run h stop = stop , h
        backward-run h (next r rs) with backward h r
        ... | q , hd with backward-run hd rs
        ...   | qs , ht = next q qs , ht

        -- This is the entry-to-exit theorem. The identical final
        -- configuration includes the entire state or the retained fault.
        from-entry : (entry : ℕ) (pre : State → Set)
                   → (∀ {s} → pre s → invariant entry s)
                   → ∀ {s es t} → pre s
                   → (Run code (running entry s) es t → Run (erase remove code) (running entry s) es t × Good t)
                   × (Run (erase remove code) (running entry s) es t → Run code (running entry s) es t × Good t)
        from-entry entry pre initial h = forward-run (initial h) , backward-run (initial h)
