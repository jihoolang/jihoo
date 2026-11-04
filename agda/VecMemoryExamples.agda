{-# OPTIONS --safe --without-K #-}
module VecMemoryExamples where

open import Schematic hiding (_+_)
open import VecMemory
open Memory ℕ

-- Uninitialized and even previously initialized spare cells are outside
-- length. Neither can be read as an element of the vector.
spare-is-not-an-element : index (vector (just 10 ∷ just 99 ∷ nothing ∷ []) 1 3) 1 ≡ nothing
spare-is-not-an-element = refl

uninitialized-read : index (vector (nothing ∷ []) 1 1) 0 ≡ nothing
uninitialized-read = refl

empty-read : index new 0 ≡ nothing
empty-read = refl

no-storage : push-in-place (vector [] 0 1) 7 ≡ nothing
no-storage = refl

full : push-in-place (vector (just 10 ∷ []) 1 1) 7 ≡ nothing
full = refl

borrowed : Vector
borrowed = vector (just 10 ∷ just 20 ∷ []) 2 0

borrowed-represents : Represents borrowed (10 ∷ 20 ∷ [])
borrowed-represents = represents (initialized (initialized empty)) refl (inl refl)

borrowed-read : index borrowed 1 ≡ just 20
borrowed-read = index-exact borrowed-represents 1

borrowed-no-write : push-in-place borrowed 30 ≡ nothing
borrowed-no-write = refl

-- Even a spare backing cell is read-only until the zero-capacity
-- descriptor has been relocated into owned storage.
borrowed-spare-no-write : push-in-place (vector (just 99 ∷ []) 0 0) 7 ≡ nothing
borrowed-spare-no-write = refl

relocated : Vector
relocated = vector (just 10 ∷ just 20 ∷ nothing ∷ nothing ∷ []) 2 4

relocation : reserve-to borrowed 4 ≡ just relocated
relocation = refl

relocation-represents : Represents relocated (10 ∷ 20 ∷ [])
relocation-represents = reserve-sound {cap = 4} borrowed-represents relocation

relocation-exists : resize (size (10 ∷ 20 ∷ []) + 2) 2 (cells borrowed)
                  ≡ just (map just (10 ∷ 20 ∷ []) ++ holes 2)
relocation-exists = resize-complete (prefix borrowed-represents) 2

undersized-relocation : reserve-to borrowed 1 ≡ nothing
undersized-relocation = refl

short-copy : reserve-to (vector (just 10 ∷ []) 2 0) 4 ≡ nothing
short-copy = refl

grown : Vector
grown = vector (just 10 ∷ just 20 ∷ just 30 ∷ nothing ∷ []) 3 4

growth : push borrowed 4 30 ≡ just grown
growth = refl

growth-represents : Represents grown (10 ∷ 20 ∷ 30 ∷ [])
growth-represents = push-sound {cap = 4} borrowed-represents growth

no-room-after-copy : push borrowed 2 30 ≡ nothing
no-room-after-copy = refl

spare : Vector
spare = vector (just 10 ∷ nothing ∷ just 99 ∷ []) 1 3

spare-represents : Represents spare (10 ∷ [])
spare-represents = represents (initialized empty) refl (inr refl)

in-place : push spare 0 20 ≡ just (vector (just 10 ∷ just 20 ∷ just 99 ∷ []) 2 3)
in-place = refl

-- An unrelated spare cell survives an in-place write, including its old
-- contents. This uses the general frame theorem, rather than evaluation.
spare-written : Written 20 1 (cells spare) (just 10 ∷ just 20 ∷ just 99 ∷ [])
spare-written = at-suc at-zero

spare-frame : lookup (just 10 ∷ just 20 ∷ just 99 ∷ []) 2
             ≡ lookup (cells spare) 2
spare-frame = written-frame spare-written 2 (λ ())
