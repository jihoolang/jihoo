{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- A scalar MIR fragment with local frames and real direct-call execution.
-- Blocks retain their statements, lifetime markers and terminators.
-- Undefined reads, invalid projections, pending blocks and unsupported
-- operations have no returning execution. Direct calls run the selected
-- function's graph in a new frame and resume the caller with its result.
--
-- `wp-sound` proves finite proof-directed symbolic execution sound for
-- arbitrary graphs and nondeterministic calls. Its fuel limits the proof,
-- not Run: Run and Calls describe arbitrary finite executions, including
-- recursive calls. Invariants for unbounded loops are future work.
------------------------------------------------------------------------
module MirExecution where

open import Schematic using
  (ℕ; zero; suc; Bool; true; false; List; []; _∷_; Maybe; nothing; just; _>>=_;
   Σ; _×_; _,_; _≡_; refl; _==_; ⊥; lookup)
import Integers as Z
import ScalarExecution as Scalar
open Σ

data Value : Set where
  integer : Z.ℤ → Value
  boolean : Bool → Value
  pair : Value → Value → Value
  none : Value
  some : Value → Value

data ValueType : Set where
  int-type bool-type pair-type option-type : ValueType

data Operand : Set where
  local : ℕ → List ℕ → Operand

data Rvalue : Set where
  use : Operand → Rvalue
  option-none : Rvalue
  option-some : Operand → Rvalue

data Statement : Set where
  assign : ℕ → Rvalue → Statement
  live dead : ℕ → Statement
  nop : Statement

data Callee : Set where
  overflowing : Scalar.Operation → Callee
  direct : ℕ → Callee

data Terminator : Set where
  goto : ℕ → Terminator
  switch : Operand → ℕ → ℕ → Terminator
  call : Callee → List Operand → ℕ → ℕ → Terminator
  return stop : Terminator

record Block : Set where
  constructor block
  field
    statements : List Statement
    terminator : Terminator
open Block

record Function : Set where
  constructor function
  field
    arguments : List ValueType
    result : ValueType
    locals : List ValueType
    blocks : List Block
open Function

Program : Set
Program = List Function

Store : Set
Store = ℕ → Maybe Value

set : Store → ℕ → Maybe Value → Store
set s at v n with n == at
... | true = v
... | false = s n

initial : List Value → Store
initial args zero = nothing
initial args (suc n) = lookup args n

project : Value → List ℕ → Maybe Value
project v [] = just v
project (pair a b) (zero ∷ xs) = project a xs
project (pair a b) (suc zero ∷ xs) = project b xs
project _ (_ ∷ _) = nothing

read : Store → Operand → Maybe Value
read s (local n fields) = s n >>= λ v → project v fields

read-all : Store → List Operand → Maybe (List Value)
read-all s [] = just []
read-all s (x ∷ xs) = read s x >>= λ v → read-all s xs >>= λ vs → just (v ∷ vs)

eval : Store → Rvalue → Maybe Value
eval s (use p) = read s p
eval s option-none = just none
eval s (option-some p) = read s p >>= λ v → just (some v)

statements-step : List Statement → Store → Maybe Store
statements-step [] s = just s
statements-step (assign n r ∷ ss) s = eval s r >>= λ v → statements-step ss (set s n (just v))
statements-step (live n ∷ ss) s = statements-step ss (set s n nothing)
statements-step (dead n ∷ ss) s = statements-step ss (set s n nothing)
statements-step (nop ∷ ss) s = statements-step ss s

data Action : Set where
  finished : Value → Action
  next : ℕ → Store → Action
  invoke : Callee → List Value → ℕ → ℕ → Store → Action
  stuck : Action

terminate : Terminator → Store → Action
terminate (goto bb) s = next bb s
terminate (switch p zero-bb other-bb) s with read s p
... | just (boolean false) = next zero-bb s
... | just (boolean true) = next other-bb s
... | _ = stuck
terminate (call c args dest bb) s with read-all s args
... | just vs = invoke c vs dest bb s
... | nothing = stuck
terminate return s with s 0
... | just v = finished v
... | nothing = stuck
terminate stop s = stuck

advance : Function → ℕ → Store → Action
advance f bb s with lookup (blocks f) bb
... | nothing = stuck
... | just b with statements-step (statements b) s
...   | nothing = stuck
...   | just t = terminate (terminator b) t

size : {A : Set} → List A → ℕ
size [] = zero
size (_ ∷ xs) = suc (size xs)

module Semantics (bounds : Scalar.Bounds) where
  mutual
    data Run (p : Program) (f : Function) : Action → Value → Set where
      returned : ∀ {v} → Run p f (finished v) v
      continued : ∀ {bb s v} → Run p f (advance f bb s) v → Run p f (next bb s) v
      called : ∀ {c args dest bb s v r} → Calls p c args v
             → Run p f (advance f bb (set s dest (just v))) r
             → Run p f (invoke c args dest bb s) r

    data Calls (p : Program) : Callee → List Value → Value → Set where
      overflow-call : ∀ {op a b r flag} → Scalar.Overflowing bounds (Scalar.exact op a b) r flag
                → Calls p (overflowing op) (integer a ∷ integer b ∷ []) (pair (integer r) (boolean flag))
      function-call : ∀ {id f args v} → lookup p id ≡ just f → size args ≡ size (arguments f)
                    → Run p f (advance f 0 (initial args)) v → Calls p (direct id) args v

  -- wp universally quantifies over every possible call result. A caller
  -- can use a callee's summary only after proving it for Calls, whose
  -- direct-call constructor contains the callee's actual Run derivation.
  wp : Program → Function → ℕ → Action → (Value → Set) → Set
  wp p f zero a post = ⊥
  wp p f (suc fuel) (finished v) post = post v
  wp p f (suc fuel) (next bb s) post = wp p f fuel (advance f bb s) post
  wp p f (suc fuel) (invoke c args dest bb s) post =
    ∀ v → Calls p c args v → wp p f fuel (advance f bb (set s dest (just v))) post
  wp p f (suc fuel) stuck post = ⊥

  wp-sound : ∀ p f fuel a post → wp p f fuel a post → ∀ {v} → Run p f a v → post v
  wp-sound p f zero a post () run
  wp-sound p f (suc fuel) (finished v) post proof returned = proof
  wp-sound p f (suc fuel) (next bb s) post proof (continued run) =
    wp-sound p f fuel (advance f bb s) post proof run
  wp-sound p f (suc fuel) (invoke c args dest bb s) post proof (called {v = v} invoked run) =
    wp-sound p f fuel (advance f bb (set s dest (just v))) post (proof v invoked) run
  wp-sound p f (suc fuel) stuck post () run
