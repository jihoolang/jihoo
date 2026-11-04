{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- A typed backing store for Vec: initialized cells, spare capacity and
-- the initialized prefix named by the descriptor's length. A zero-capacity
-- borrowed buffer may have a nonzero length, as String.from_static does.
--
-- Reads respect length, writes require an existing cell within capacity,
-- and successful relocation copies the prefix before adding spare cells.
-- Relocation models successful allocation at a supplied new capacity.
-- This is a memory specification, not a proof of std.Vec's MIR, byte/pointer
-- layout, allocator, ownership checker or bounded machine arithmetic.
------------------------------------------------------------------------
module VecMemory where

open import Schematic hiding (_+_)
open Σ

size : {A : Set} → List A → ℕ
size [] = zero
size (_ ∷ xs) = suc (size xs)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

less : ℕ → ℕ → Bool
less _ zero = false
less zero (suc _) = true
less (suc m) (suc n) = less m n

size-snoc : {A : Set} → (xs : List A) → (x : A) → size (xs ++ (x ∷ [])) ≡ suc (size xs)
size-snoc [] x = refl
size-snoc (_ ∷ xs) x = cong suc (size-snoc xs x)

module Memory (A : Set) where
  Cells : Set
  Cells = List (Maybe A)

  record Vector : Set where
    constructor vector
    field
      cells : Cells
      length capacity : ℕ
  open Vector public

  -- Spare cells can contain anything, including uninitialized memory or
  -- old values. Only the initialized prefix belongs to the abstract list.
  data Prefix : List A → Cells → Set where
    empty : ∀ {cs} → Prefix [] cs
    initialized : ∀ {x xs cs} → Prefix xs cs → Prefix (x ∷ xs) (just x ∷ cs)

  record Represents (v : Vector) (xs : List A) : Set where
    constructor represents
    field
      prefix : Prefix xs (cells v)
      count : length v ≡ size xs
      extent : (capacity v ≡ zero) ⊎ (capacity v ≡ size (cells v))
  open Represents public

  new : Vector
  new = vector [] 0 0

  new-represents : Represents new []
  new-represents = represents empty refl (inr refl)

  -- Read a typed cell only inside the descriptor's initialized range.
  bounded-read : ℕ → Cells → ℕ → Maybe A
  bounded-read zero cs i = nothing
  bounded-read (suc n) [] i = nothing
  bounded-read (suc n) (c ∷ cs) zero = c
  bounded-read (suc n) (c ∷ cs) (suc i) = bounded-read n cs i

  index : Vector → ℕ → Maybe A
  index v i = bounded-read (length v) (cells v) i

  prefix-read : ∀ {xs cs} → Prefix xs cs → ∀ i → bounded-read (size xs) cs i ≡ lookup xs i
  prefix-read empty i = refl
  prefix-read (initialized p) zero = refl
  prefix-read (initialized p) (suc i) = prefix-read p i

  index-exact : ∀ {v xs} → Represents v xs → ∀ i → index v i ≡ lookup xs i
  index-exact {v} (represents p refl e) i = prefix-read p i

  -- Writing an initialized cell never extends an allocation. In particular,
  -- a borrowed buffer (capacity zero) cannot be written by this operation.
  write-next : ℕ → ℕ → Cells → A → Maybe Cells
  write-next n zero cs x = nothing
  write-next n (suc cap) [] x = nothing
  write-next zero (suc cap) (c ∷ cs) x = just (just x ∷ cs)
  write-next (suc n) (suc cap) (c ∷ cs) x =
    write-next n cap cs x >>= λ ds → just (c ∷ ds)

  data Written (x : A) : ℕ → Cells → Cells → Set where
    at-zero : ∀ {c cs} → Written x zero (c ∷ cs) (just x ∷ cs)
    at-suc : ∀ {n c cs ds} → Written x n cs ds → Written x (suc n) (c ∷ cs) (c ∷ ds)

  write-next-sound : ∀ n cap cs x ds → write-next n cap cs x ≡ just ds → Written x n cs ds
  write-next-sound n zero cs x ds ()
  write-next-sound n (suc cap) [] x ds ()
  write-next-sound zero (suc cap) (c ∷ cs) x .(just x ∷ cs) refl = at-zero
  write-next-sound (suc n) (suc cap) (c ∷ cs) x ds e
    with bind-inv (write-next n cap cs x) (λ ts → just (c ∷ ts)) e
  ... | ts , w , refl = at-suc (write-next-sound n cap cs x ts w)

  write-next-room : ∀ n cap cs x ds → write-next n cap cs x ≡ just ds → less n cap ≡ true
  write-next-room n zero cs x ds ()
  write-next-room n (suc cap) [] x ds ()
  write-next-room zero (suc cap) (c ∷ cs) x ds e = refl
  write-next-room (suc n) (suc cap) (c ∷ cs) x ds e
    with bind-inv (write-next n cap cs x) (λ ts → just (c ∷ ts)) e
  ... | ts , w , refl = write-next-room n cap cs x ts w

  written-size : ∀ {x n cs ds} → Written x n cs ds → size ds ≡ size cs
  written-size at-zero = refl
  written-size (at-suc w) = cong suc (written-size w)

  written-prefix : ∀ {xs cs ds x} → Prefix xs cs → Written x (size xs) cs ds
                 → Prefix (xs ++ (x ∷ [])) ds
  written-prefix empty at-zero = initialized empty
  written-prefix (initialized p) (at-suc w) = initialized (written-prefix p w)

  -- A frame property for arbitrary backing cells, including spare cells:
  -- every address other than the appended cell keeps its previous value.
  written-frame : ∀ {x n cs ds} → Written x n cs ds → ∀ i → ¬ (i ≡ n) → lookup ds i ≡ lookup cs i
  written-frame at-zero zero different = ⊥-elim (different refl)
  written-frame at-zero (suc i) different = refl
  written-frame (at-suc w) zero different = refl
  written-frame (at-suc w) (suc i) different = written-frame w i (λ e → different (cong suc e))

  push-in-place : Vector → A → Maybe Vector
  push-in-place v x = write-next (length v) (capacity v) (cells v) x >>= λ ds →
    just (vector ds (suc (length v)) (capacity v))

  push-in-place-sound : ∀ {v xs x w} → Represents v xs → push-in-place v x ≡ just w
                      → Represents w (xs ++ (x ∷ [])) × Written x (length v) (cells v) (cells w)
  push-in-place-sound {v = vector cs n cap} {xs} {x} (represents p count extent) e
    with bind-inv (write-next n cap cs x) (λ ds → just (vector ds (suc n) cap)) e
  ... | ds , wrote , refl = result , written
    where
      written : Written x n cs ds
      written = write-next-sound n cap cs x ds wrote

      capacity-ok : (cap ≡ zero) ⊎ (cap ≡ size cs) → (cap ≡ zero) ⊎ (cap ≡ size ds)
      capacity-ok (inl e) = ⊥-elim (nothing≢just
        (transport (λ c → write-next n c cs x ≡ just ds) e wrote))
      capacity-ok (inr e) = inr (trans e (sym (written-size written)))

      result : Represents (vector ds (suc n) cap) (xs ++ (x ∷ []))
      result = represents (written-prefix p (transport (λ i → Written x i cs ds) count written))
        (trans (cong suc count) (sym (size-snoc xs x))) (capacity-ok extent)

  holes : ℕ → Cells
  holes zero = []
  holes (suc n) = nothing ∷ holes n

  -- Copy exactly len cells, then provide uninitialized spare storage.
  -- A short source or a destination smaller than len cannot succeed.
  resize : ℕ → ℕ → Cells → Maybe Cells
  resize cap zero cs = just (holes cap)
  resize zero (suc n) cs = nothing
  resize (suc cap) (suc n) [] = nothing
  resize (suc cap) (suc n) (c ∷ cs) = resize cap n cs >>= λ ds → just (c ∷ ds)

  holes-size : ∀ n → size (holes n) ≡ n
  holes-size zero = refl
  holes-size (suc n) = cong suc (holes-size n)

  resize-size : ∀ cap n cs ds → resize cap n cs ≡ just ds → size ds ≡ cap
  resize-size cap zero cs .(holes cap) refl = holes-size cap
  resize-size zero (suc n) cs ds ()
  resize-size (suc cap) (suc n) [] ds ()
  resize-size (suc cap) (suc n) (c ∷ cs) ds e
    with bind-inv (resize cap n cs) (λ ts → just (c ∷ ts)) e
  ... | ts , r , refl = cong suc (resize-size cap n cs ts r)

  resize-prefix : ∀ {xs cs} → Prefix xs cs → ∀ cap ds
                → resize cap (size xs) cs ≡ just ds → Prefix xs ds
  resize-prefix empty cap ds e = empty
  resize-prefix (initialized p) zero ds ()
  resize-prefix (initialized {x} {xs} {cs} p) (suc cap) ds e
    with bind-inv (resize cap (size xs) cs) (λ ts → just (just x ∷ ts)) e
  ... | ts , r , refl = initialized (resize-prefix p cap ts r)

  -- A constructive success theorem: sufficient capacity always gives an
  -- actual relocation, for every represented prefix and arbitrary spare
  -- contents. Preservation does not rely on a vacuous success premise.
  resize-complete : ∀ {xs cs} → Prefix xs cs → ∀ spare
                  → resize (size xs + spare) (size xs) cs ≡ just (map just xs ++ holes spare)
  resize-complete empty spare = refl
  resize-complete (initialized p) spare rewrite resize-complete p spare = refl

  reserve-to : Vector → ℕ → Maybe Vector
  reserve-to v cap = resize cap (length v) (cells v) >>= λ ds → just (vector ds (length v) cap)

  reserve-sound : ∀ {v xs cap w} → Represents v xs → reserve-to v cap ≡ just w → Represents w xs
  reserve-sound {vector cs n old} {xs} {cap} (represents p count extent) e
    with bind-inv (resize cap n cs) (λ ds → just (vector ds n cap)) e
  ... | ds , copied , refl = represents
    (resize-prefix p cap ds (transport (λ k → resize cap k cs ≡ just ds) count copied))
    count (inr (sym (resize-size cap n cs ds copied)))

  write-relocated : ∀ xs spare x
                  → write-next (size xs) (size xs + suc spare) (map just xs ++ holes (suc spare)) x
                    ≡ just (map just (xs ++ (x ∷ [])) ++ holes spare)
  write-relocated [] spare x = refl
  write-relocated (y ∷ xs) spare x rewrite write-relocated xs spare x = refl

  reserve-and-push : Vector → ℕ → A → Maybe Vector
  reserve-and-push v cap x = reserve-to v cap >>= λ moved → push-in-place moved x

  growth-complete : ∀ {v xs} → Represents v xs → ∀ spare x
                  → Σ Vector (λ w → reserve-and-push v (size xs + suc spare) x ≡ just w)
  growth-complete {vector cs .(size xs) cap} {xs} (represents p refl e) spare x
    rewrite resize-complete p (suc spare) | write-relocated xs spare x = _ , refl

  push : Vector → ℕ → A → Maybe Vector
  push v new-cap x with less (length v) (capacity v)
  ... | true = push-in-place v x
  ... | false = reserve-and-push v new-cap x

  push-sound : ∀ {v xs cap x w} → Represents v xs → push v cap x ≡ just w → Represents w (xs ++ (x ∷ []))
  push-sound {v} {xs} {cap} {x} rep e with less (length v) (capacity v)
  ... | true = fst (push-in-place-sound rep e)
  ... | false with bind-inv (reserve-to v cap) (λ moved → push-in-place moved x) e
  ...   | moved , copied , wrote = fst (push-in-place-sound (reserve-sound rep copied) wrote)
