{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Execution-to-Horn correspondence for the checker's list primitives.
--
-- Values are finite lists of well-sorted ground elements. `size`,
-- `lookup` and appending one element are their executable semantics.
-- Each result derives the corresponding len/nth/snoc relation in the
-- actual Theory generated from compiler/linear.jh. Rule membership is
-- checked by Agda conversion, including all premises and variable sorts.
--
-- This discharges the list-model part of the execution bridge. It does
-- not establish that std.Vec's allocation, pointer accesses and borrows
-- implement these lists, or that horn.jh translates MIR paths correctly.
------------------------------------------------------------------------
module ListExecution where

open import Schematic
open import Theory
open import Adequacy using (OrderedRing; module Adequate; sig; head; gz0)
open Rule
open Σ
open Signature sig
open Rules sig rules

record ListSignature : Set where
  field
    element-sort list-sort : ℕ
    nil-code cons-code len-code nth-code snoc-code : ℕ

module Schemas (S : ListSignature) where
  open ListSignature S

  nil : Tm
  nil = node nil-code []

  cons : Tm → Tm → Tm
  cons x xs = node cons-code (x ∷ xs ∷ [])

  len : Tm → Tm → Tm
  len xs n = node len-code (xs ∷ n ∷ [])

  index : Tm → Tm → Tm → Tm
  index xs i x = node nth-code (xs ∷ i ∷ x ∷ [])

  snoc : Tm → Tm → Tm → Tm
  snoc xs x ys = node snoc-code (xs ∷ x ∷ ys ∷ [])

  len-nil len-cons nth-zero nth-succ snoc-nil snoc-cons : Rule
  len-nil = rule [] (len nil #z0) (λ _ → ˢZ)
  len-cons = rule (len (var 0) (var 1) ∷ [])
    (len (cons (var 2) (var 0)) (#add (var 1) #z1))
    (λ y → nth (list-sort ∷ ˢZ ∷ element-sort ∷ []) y ˢZ)
  nth-zero = rule (#eq (var 0) #z0 ∷ [])
    (index (cons (var 1) (var 2)) (var 0) (var 1))
    (λ y → nth (ˢZ ∷ element-sort ∷ list-sort ∷ []) y ˢZ)
  nth-succ = rule (index (var 0) (var 1) (var 2) ∷ #eq (var 3) (#add (var 1) #z1) ∷ [])
    (index (cons (var 4) (var 0)) (var 3) (var 2))
    (λ y → nth (list-sort ∷ ˢZ ∷ element-sort ∷ ˢZ ∷ element-sort ∷ []) y ˢZ)
  snoc-nil = rule [] (snoc nil (var 0) (cons (var 0) nil))
    (λ y → nth (element-sort ∷ []) y ˢZ)
  snoc-cons = rule (snoc (var 0) (var 1) (var 2) ∷ [])
    (snoc (cons (var 3) (var 0)) (var 1) (cons (var 3) (var 2)))
    (λ y → nth (list-sort ∷ element-sort ∷ list-sort ∷ element-sort ∷ []) y ˢZ)

  record Present : Set where
    field
      nil-sort : out nil-code ≡ list-sort
      nil-args : ins nil-code ≡ []
      cons-sort : out cons-code ≡ list-sort
      cons-args : ins cons-code ≡ (element-sort ∷ list-sort ∷ [])
      has-len-nil : len-nil ∈ rules
      has-len-cons : len-cons ∈ rules
      has-nth-zero : nth-zero ∈ rules
      has-nth-succ : nth-succ ∈ rules
      has-snoc-nil : snoc-nil ∈ rules
      has-snoc-cons : snoc-cons ∈ rules

-- Ground constructor terms, with the sorts checked separately from the
-- absence of variables. These helpers never manufacture a ground value
-- of an uninhabited sort.
g0 : ∀ {f s} → out f ≡ s → ins f ≡ [] → GroundWS (node f []) s
g0 o i = (λ { x (arg ()) }) , node o (transport (WSsv (Signature.vs sig) []) (sym i) [])

g2 : ∀ {f s a b sa sb} → out f ≡ s → ins f ≡ (sa ∷ sb ∷ [])
   → GroundWS a sa → GroundWS b sb → GroundWS (node f (a ∷ b ∷ [])) s
g2 o i (ga , wa) (gb , wb) =
  (λ { x (arg (hd q)) → ga x q ; x (arg (tl (hd q))) → gb x q ; x (arg (tl (tl ()))) })
  , node o (transport (WSsv (Signature.vs sig) _) (sym i) (wa ∷ wb ∷ []))

-- Naturals as integer expressions; an index is never rounded or wrapped.
number : ℕ → Tm
number zero = #z0
number (suc n) = #add (number n) #z1

number-ground : ∀ n → GroundWS (number n) ˢZ
number-ground zero = gz0
number-ground (suc n) = g2 refl refl (number-ground n) (g0 refl refl)

size : {A : Set} → List A → ℕ
size [] = zero
size (_ ∷ xs) = suc (size xs)

bind : List Tm → Subst
bind ts y = nth ts y #z0

module Execution (S : ListSignature) (present : Schemas.Present S) (Rg : OrderedRing) where
  open ListSignature S
  open Schemas S
  open Present present
  open Adequate Rg using (OD; closure; truth; eqA; ⟦_⟧)
  open OrderedRing Rg using (A; 0ᴿ; 1ᴿ; _+ᴿ_; _≈ᴿ_; ≈ᴿ-refl; +ᴿ-cong)

  Value : Set
  Value = Σ Tm (λ t → GroundWS t element-sort)

  encode : List Value → Tm
  encode [] = nil
  encode (x ∷ xs) = cons (fst x) (encode xs)

  encode-ground : ∀ xs → GroundWS (encode xs) list-sort
  encode-ground [] = g0 nil-sort nil-args
  encode-ground (x ∷ xs) = g2 cons-sort cons-args (snd x) (encode-ground xs)

  eq-self : ∀ {t} → GroundWS t ˢZ → OD (#eq t t)
  eq-self g = truth (eqA g g) ≈ᴿ-refl

  natural : ℕ → A
  natural zero = 0ᴿ
  natural (suc n) = natural n +ᴿ 1ᴿ

  number-value : ∀ n → ⟦ number n ⟧ ≈ᴿ natural n
  number-value zero = ≈ᴿ-refl
  number-value (suc n) = +ᴿ-cong (number-value n) ≈ᴿ-refl

  -- A terminating length computation derives the actual generated rule
  -- relation, for every finite list, rather than only tested inputs.
  length-execution : ∀ xs → OD (len (encode xs) (number (size xs)))
  length-execution [] = closure has-len-nil (bind []) (λ _ _ → gz0) []
  length-execution (x ∷ xs) = closure has-len-cons σ ok (length-execution xs ∷ [])
    where
      σ = bind (encode xs ∷ number (size xs) ∷ fst x ∷ [])
      ok : ∀ y → OccR y len-cons → GroundWS (σ y) (rs len-cons y)
      ok zero _ = encode-ground xs
      ok (suc zero) _ = number-ground (size xs)
      ok (suc (suc zero)) _ = snd x
      ok (suc (suc (suc _))) _ = gz0

  -- `lookup` is an ordinary recursive operation. Its successful result,
  -- including a nonzero index, derives nth; no rule asserts out-of-bounds
  -- success. Proving native bounds/allocator behavior remains separate.
  index-execution : ∀ xs i x → lookup xs i ≡ just x
                  → OD (index (encode xs) (number i) (fst x))
  index-execution [] i x ()
  index-execution (x ∷ xs) zero .x refl = closure has-nth-zero σ ok (eq-self gz0 ∷ [])
    where
      σ = bind (#z0 ∷ fst x ∷ encode xs ∷ [])
      ok : ∀ y → OccR y nth-zero → GroundWS (σ y) (rs nth-zero y)
      ok zero _ = gz0
      ok (suc zero) _ = snd x
      ok (suc (suc zero)) _ = encode-ground xs
      ok (suc (suc (suc _))) _ = gz0
  index-execution (h ∷ xs) (suc i) x e = closure has-nth-succ σ ok
    (index-execution xs i x e ∷ eq-self (number-ground (suc i)) ∷ [])
    where
      σ = bind (encode xs ∷ number i ∷ fst x ∷ number (suc i) ∷ fst h ∷ [])
      ok : ∀ y → OccR y nth-succ → GroundWS (σ y) (rs nth-succ y)
      ok zero _ = encode-ground xs
      ok (suc zero) _ = number-ground i
      ok (suc (suc zero)) _ = snd x
      ok (suc (suc (suc zero))) _ = number-ground (suc i)
      ok (suc (suc (suc (suc zero)))) _ = snd h
      ok (suc (suc (suc (suc (suc _))))) _ = gz0

  -- MIR may compute an index as any integer expression, rather than the
  -- canonical `number i`. A true equality in the ring relates it to the
  -- executable lookup's natural index. No syntactic equality is assumed.
  index-execution-at : ∀ xs i x t → GroundWS t ˢZ
                     → ⟦ t ⟧ ≈ᴿ ⟦ number i ⟧ → lookup xs i ≡ just x
                     → OD (index (encode xs) t (fst x))
  index-execution-at [] i x t gt e ()
  index-execution-at (x ∷ xs) zero .x t gt e refl = closure has-nth-zero σ ok
    (truth (eqA gt gz0) e ∷ [])
    where
      σ = bind (t ∷ fst x ∷ encode xs ∷ [])
      ok : ∀ y → OccR y nth-zero → GroundWS (σ y) (rs nth-zero y)
      ok zero _ = gt
      ok (suc zero) _ = snd x
      ok (suc (suc zero)) _ = encode-ground xs
      ok (suc (suc (suc _))) _ = gz0
  index-execution-at (h ∷ xs) (suc i) x t gt e found = closure has-nth-succ σ ok
    (index-execution xs i x found ∷ truth (eqA gt (number-ground (suc i))) e ∷ [])
    where
      σ = bind (encode xs ∷ number i ∷ fst x ∷ t ∷ fst h ∷ [])
      ok : ∀ y → OccR y nth-succ → GroundWS (σ y) (rs nth-succ y)
      ok zero _ = encode-ground xs
      ok (suc zero) _ = number-ground i
      ok (suc (suc zero)) _ = snd x
      ok (suc (suc (suc zero))) _ = gt
      ok (suc (suc (suc (suc zero)))) _ = snd h
      ok (suc (suc (suc (suc (suc _))))) _ = gz0

  push-execution : ∀ xs x → OD (snoc (encode xs) (fst x) (encode (xs ++ (x ∷ [])) ))
  push-execution [] x = closure has-snoc-nil σ ok []
    where
      σ = bind (fst x ∷ [])
      ok : ∀ y → OccR y snoc-nil → GroundWS (σ y) (rs snoc-nil y)
      ok zero _ = snd x
      ok (suc _) _ = gz0
  push-execution (h ∷ xs) x = closure has-snoc-cons σ ok (push-execution xs x ∷ [])
    where
      σ = bind (encode xs ∷ fst x ∷ encode (xs ++ (x ∷ [])) ∷ fst h ∷ [])
      ok : ∀ y → OccR y snoc-cons → GroundWS (σ y) (rs snoc-cons y)
      ok zero _ = encode-ground xs
      ok (suc zero) _ = snd x
      ok (suc (suc zero)) _ = encode-ground (xs ++ (x ∷ []))
      ok (suc (suc (suc zero))) _ = snd h
      ok (suc (suc (suc (suc _)))) _ = gz0

-- These are the three list sorts used by linear.check. The schema
-- witnesses below refer to Theory's actual rule positions, not copies of
-- the rules supplied as axioms. Altering a generated rule invalidates refl.
terms facts weights : ListSignature
terms = record
  { element-sort = ˢTup⟨ZˌZ⟩ ; list-sort = ˢVec⟨⟨i64ˌi128⟩⟩
  ; nil-code = head #Vec⟨⟨i64ˌi128⟩⟩·nil
  ; cons-code = head (#Vec⟨⟨i64ˌi128⟩⟩·cons #z0 #z0)
  ; len-code = head (#Vec⟨⟨i64ˌi128⟩⟩·len #z0 #z0)
  ; nth-code = head (#Vec⟨⟨i64ˌi128⟩⟩·nth #z0 #z0 #z0)
  ; snoc-code = head (#Vec⟨⟨i64ˌi128⟩⟩·snoc #z0 #z0 #z0) }
facts = record
  { element-sort = ˢLin ; list-sort = ˢVec⟨Lin⟩
  ; nil-code = head #Vec⟨Lin⟩·nil
  ; cons-code = head (#Vec⟨Lin⟩·cons #z0 #z0)
  ; len-code = head (#Vec⟨Lin⟩·len #z0 #z0)
  ; nth-code = head (#Vec⟨Lin⟩·nth #z0 #z0 #z0)
  ; snoc-code = head (#Vec⟨Lin⟩·snoc #z0 #z0 #z0) }
weights = record
  { element-sort = ˢZ ; list-sort = ˢVec⟨i128⟩
  ; nil-code = head #Vec⟨i128⟩·nil
  ; cons-code = head (#Vec⟨i128⟩·cons #z0 #z0)
  ; len-code = head (#Vec⟨i128⟩·len #z0 #z0)
  ; nth-code = head (#Vec⟨i128⟩·nth #z0 #z0 #z0)
  ; snoc-code = head (#Vec⟨i128⟩·snoc #z0 #z0 #z0) }

terms-present : Schemas.Present terms
terms-present = record
  { nil-sort = refl ; nil-args = refl ; cons-sort = refl ; cons-args = refl
  ; has-len-nil = lookup-∈ rules ⁱVec⟨⟨i64ˌi128⟩⟩·len·nil refl
  ; has-len-cons = lookup-∈ rules ⁱVec⟨⟨i64ˌi128⟩⟩·len·cons refl
  ; has-nth-zero = lookup-∈ rules ⁱVec⟨⟨i64ˌi128⟩⟩·nth·zero refl
  ; has-nth-succ = lookup-∈ rules ⁱVec⟨⟨i64ˌi128⟩⟩·nth·succ refl
  ; has-snoc-nil = lookup-∈ rules ⁱVec⟨⟨i64ˌi128⟩⟩·snoc·nil refl
  ; has-snoc-cons = lookup-∈ rules ⁱVec⟨⟨i64ˌi128⟩⟩·snoc·cons refl }

facts-present : Schemas.Present facts
facts-present = record
  { nil-sort = refl ; nil-args = refl ; cons-sort = refl ; cons-args = refl
  ; has-len-nil = lookup-∈ rules ⁱVec⟨Lin⟩·len·nil refl
  ; has-len-cons = lookup-∈ rules ⁱVec⟨Lin⟩·len·cons refl
  ; has-nth-zero = lookup-∈ rules ⁱVec⟨Lin⟩·nth·zero refl
  ; has-nth-succ = lookup-∈ rules ⁱVec⟨Lin⟩·nth·succ refl
  ; has-snoc-nil = lookup-∈ rules ⁱVec⟨Lin⟩·snoc·nil refl
  ; has-snoc-cons = lookup-∈ rules ⁱVec⟨Lin⟩·snoc·cons refl }

weights-present : Schemas.Present weights
weights-present = record
  { nil-sort = refl ; nil-args = refl ; cons-sort = refl ; cons-args = refl
  ; has-len-nil = lookup-∈ rules ⁱVec⟨i128⟩·len·nil refl
  ; has-len-cons = lookup-∈ rules ⁱVec⟨i128⟩·len·cons refl
  ; has-nth-zero = lookup-∈ rules ⁱVec⟨i128⟩·nth·zero refl
  ; has-nth-succ = lookup-∈ rules ⁱVec⟨i128⟩·nth·succ refl
  ; has-snoc-nil = lookup-∈ rules ⁱVec⟨i128⟩·snoc·nil refl
  ; has-snoc-cons = lookup-∈ rules ⁱVec⟨i128⟩·snoc·cons refl }

module Terms (Rg : OrderedRing) = Execution terms terms-present Rg
module Facts (Rg : OrderedRing) = Execution facts facts-present Rg
module Weights (Rg : OrderedRing) = Execution weights weights-present Rg
