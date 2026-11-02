{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- The integers are an ordered commutative ring, and the theorem of
-- Adequacy.agda holds in them.
--
-- An integer is a difference `p ⊖ n` of naturals; two are equal when
-- p + n′ = p′ + n, and ordered when p + n′ ≤ p′ + n. Each law of
-- `OrderedRing` (ring.jh's axioms) is then an identity between
-- polynomials over the naturals, proved by `solve`, a normalizer to
-- Horner form proved sound below, together with cancellation.
--
-- No library is imported: Schematic.agda's prelude is used.
------------------------------------------------------------------------
module Integers where

open import Schematic hiding (_+_; +-zero; +-suc; _⊕_)
open import Adequacy using (OrderedRing; module Adequate)

------------------------------------------------------------------------
-- Naturals

infixl 6 _+_
infixl 7 _*_

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n

suc-inj : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

+-zero : ∀ m → m + 0 ≡ m
+-zero zero    = refl
+-zero (suc m) = cong suc (+-zero m)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+-zero n)
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

+-assoc : ∀ m n k → m + n + k ≡ m + (n + k)
+-assoc zero    n k = refl
+-assoc (suc m) n k = cong suc (+-assoc m n k)

*-zero : ∀ m → m * 0 ≡ 0
*-zero zero    = refl
*-zero (suc m) = *-zero m

*-suc : ∀ m n → m * suc n ≡ m + m * n
*-suc zero    n = refl
*-suc (suc m) n =
  cong suc (trans (cong (n +_) (*-suc m n))
    (trans (sym (+-assoc n m (m * n))) (trans (cong (_+ m * n) (+-comm n m)) (+-assoc m n (m * n)))))

*-comm : ∀ m n → m * n ≡ n * m
*-comm zero    n = sym (*-zero n)
*-comm (suc m) n = trans (cong (n +_) (*-comm m n)) (sym (*-suc n m))

dist-r : ∀ m n k → (m + n) * k ≡ m * k + n * k
dist-r zero    n k = refl
dist-r (suc m) n k = trans (cong (k +_) (dist-r m n k)) (sym (+-assoc k (m * k) (n * k)))

dist-l : ∀ m n k → m * (n + k) ≡ m * n + m * k
dist-l m n k = trans (*-comm m (n + k)) (trans (dist-r n k m) (cong₂ _+_ (*-comm n m) (*-comm k m)))

*-assoc : ∀ m n k → m * n * k ≡ m * (n * k)
*-assoc zero    n k = refl
*-assoc (suc m) n k = trans (dist-r n (m * n) k) (cong (n * k +_) (*-assoc m n k))

+-cancel : ∀ m n k → m + k ≡ n + k → m ≡ n
+-cancel m n zero    e = trans (sym (+-zero m)) (trans e (+-zero n))
+-cancel m n (suc k) e = +-cancel m n k (suc-inj (trans (sym (+-suc m k)) (trans e (+-suc n k))))

------------------------------------------------------------------------
-- Polynomial identities over the naturals

infixl 6 _:+_
infixl 7 _:*_

data Expr : Set where
  v     : ℕ → Expr
  lit   : ℕ → Expr
  _:+_  : Expr → Expr → Expr
  _:*_  : Expr → Expr → Expr

-- Values of the first n variables.
Vals : ℕ → Set
Vals zero    = ⊤
Vals (suc n) = ℕ × Vals n

at : (n : ℕ) → Vals n → ℕ → ℕ
at zero    _       _       = 0
at (suc n) (x , _) zero    = x
at (suc n) (_ , ρ) (suc i) = at n ρ i

⟦_⟧ₑ : {n : ℕ} → Expr → Vals n → ℕ
⟦_⟧ₑ {n} (v i)    ρ = at n ρ i
⟦ lit k ⟧ₑ        ρ = k
⟦ a :+ b ⟧ₑ       ρ = ⟦ a ⟧ₑ ρ + ⟦ b ⟧ₑ ρ
⟦ a :* b ⟧ₑ       ρ = ⟦ a ⟧ₑ ρ * ⟦ b ⟧ₑ ρ

-- Horner form: a polynomial in n variables is a natural (n = 0) or the
-- list of its coefficients in the first variable, polynomials in the rest.
-- Each operation on polynomials has a twin (…L) on coefficient lists.
Poly : ℕ → Set
Poly zero    = ℕ
Poly (suc n) = List (Poly n)

mutual
  evalP : (n : ℕ) → Poly n → Vals n → ℕ
  evalP zero    k  _ = k
  evalP (suc n) ps ρ = evalL n ps ρ

  evalL : (n : ℕ) → List (Poly n) → Vals (suc n) → ℕ
  evalL n []       _       = 0
  evalL n (p ∷ ps) (x , ρ) = evalP n p ρ + x * evalL n ps (x , ρ)

zeroP : (n : ℕ) → Poly n
zeroP zero    = 0
zeroP (suc n) = []

constP : (n : ℕ) → ℕ → Poly n
constP zero    k = k
constP (suc n) k = constP n k ∷ []

varP : (n : ℕ) → ℕ → Poly n
varP zero    i       = 0
varP (suc n) zero    = zeroP n ∷ constP n 1 ∷ []
varP (suc n) (suc i) = varP n i ∷ []

mutual
  addP : (n : ℕ) → Poly n → Poly n → Poly n
  addP zero    a  b  = a + b
  addP (suc n) ps qs = addL n ps qs

  addL : (n : ℕ) → List (Poly n) → List (Poly n) → List (Poly n)
  addL n []       qs       = qs
  addL n (p ∷ ps) []       = p ∷ ps
  addL n (p ∷ ps) (q ∷ qs) = addP n p q ∷ addL n ps qs

mutual
  scaleL : (n : ℕ) → Poly n → List (Poly n) → List (Poly n)
  scaleL n a []       = []
  scaleL n a (q ∷ qs) = mulP n a q ∷ scaleL n a qs

  mulP : (n : ℕ) → Poly n → Poly n → Poly n
  mulP zero    a  b  = a * b
  mulP (suc n) ps qs = mulL n ps qs

  mulL : (n : ℕ) → List (Poly n) → List (Poly n) → List (Poly n)
  mulL n []       qs = []
  mulL n (p ∷ ps) qs = addL n (scaleL n p qs) (zeroP n ∷ mulL n ps qs)

norm : (n : ℕ) → Expr → Poly n
norm n (v i)    = varP n i
norm n (lit k)  = constP n k
norm n (a :+ b) = addP n (norm n a) (norm n b)
norm n (a :* b) = mulP n (norm n a) (norm n b)

-- Canonical form: no zero coefficient last, at every level.
isZero : (n : ℕ) → Poly n → Bool
isZero zero    zero    = true
isZero zero    (suc _) = false
isZero (suc n) []      = true
isZero (suc n) (_ ∷ _) = false

consP : (n : ℕ) → Poly n → List (Poly n) → List (Poly n)
consP n p []       = if isZero n p then [] else (p ∷ [])
consP n p (q ∷ qs) = p ∷ q ∷ qs

mutual
  strip : (n : ℕ) → Poly n → Poly n
  strip zero    k  = k
  strip (suc n) ps = stripL n ps

  stripL : (n : ℕ) → List (Poly n) → List (Poly n)
  stripL n []       = []
  stripL n (p ∷ ps) = consP n (strip n p) (stripL n ps)

-- Soundness of each operation.

swap4 : ∀ w x y z → (w + x) + (y + z) ≡ (w + y) + (x + z)
swap4 w x y z =
  trans (+-assoc w x (y + z)) (trans (cong (w +_) (trans (sym (+-assoc x y z))
    (trans (cong (_+ z) (+-comm x y)) (+-assoc y x z)))) (sym (+-assoc w y (x + z))))

eval-zero : (n : ℕ) (ρ : Vals n) → evalP n (zeroP n) ρ ≡ 0
eval-zero zero    _ = refl
eval-zero (suc n) _ = refl

eval-const : (n k : ℕ) (ρ : Vals n) → evalP n (constP n k) ρ ≡ k
eval-const zero    k _       = refl
eval-const (suc n) k (x , ρ) = trans (cong₂ _+_ (eval-const n k ρ) (*-zero x)) (+-zero k)

eval-var : (n i : ℕ) (ρ : Vals n) → evalP n (varP n i) ρ ≡ at n ρ i
eval-var zero    i       _       = refl
eval-var (suc n) zero    (x , ρ) =
  trans (cong₂ _+_ (eval-zero n ρ) (cong (x *_) (cong₂ _+_ (eval-const n 1 ρ) (*-zero x))))
    (trans (*-suc x 0) (trans (cong (x +_) (*-zero x)) (+-zero x)))
eval-var (suc n) (suc i) (x , ρ) = trans (cong₂ _+_ (eval-var n i ρ) (*-zero x)) (+-zero _)

mutual
  eval-add : (n : ℕ) (p q : Poly n) (ρ : Vals n) → evalP n (addP n p q) ρ ≡ evalP n p ρ + evalP n q ρ
  eval-add zero    a  b  _ = refl
  eval-add (suc n) ps qs ρ = eval-addL n ps qs ρ

  eval-addL : (n : ℕ) (ps qs : List (Poly n)) (ρ : Vals (suc n))
            → evalL n (addL n ps qs) ρ ≡ evalL n ps ρ + evalL n qs ρ
  eval-addL n []       qs       _       = refl
  eval-addL n (p ∷ ps) []       _       = sym (+-zero _)
  eval-addL n (p ∷ ps) (q ∷ qs) (x , ρ) =
    trans (cong₂ _+_ (eval-add n p q ρ) (trans (cong (x *_) (eval-addL n ps qs (x , ρ))) (dist-l x PS QS)))
      (swap4 (evalP n p ρ) (evalP n q ρ) (x * PS) (x * QS))
    where
      PS = evalL n ps (x , ρ)
      QS = evalL n qs (x , ρ)

swap-mul : ∀ x a q → x * (a * q) ≡ a * (x * q)
swap-mul x a q = trans (sym (*-assoc x a q)) (trans (cong (_* q) (*-comm x a)) (*-assoc a x q))

mutual
  eval-scale : (n : ℕ) (a : Poly n) (qs : List (Poly n)) (x : ℕ) (ρ : Vals n)
             → evalL n (scaleL n a qs) (x , ρ) ≡ evalP n a ρ * evalL n qs (x , ρ)
  eval-scale n a []       x ρ = sym (*-zero (evalP n a ρ))
  eval-scale n a (q ∷ qs) x ρ =
    trans (cong₂ _+_ (eval-mul n a q ρ)
            (trans (cong (x *_) (eval-scale n a qs x ρ)) (swap-mul x (evalP n a ρ) (evalL n qs (x , ρ)))))
      (sym (dist-l (evalP n a ρ) _ _))

  eval-mul : (n : ℕ) (p q : Poly n) (ρ : Vals n) → evalP n (mulP n p q) ρ ≡ evalP n p ρ * evalP n q ρ
  eval-mul zero    a  b  _ = refl
  eval-mul (suc n) ps qs ρ = eval-mulL n ps qs ρ

  eval-mulL : (n : ℕ) (ps qs : List (Poly n)) (ρ : Vals (suc n))
            → evalL n (mulL n ps qs) ρ ≡ evalL n ps ρ * evalL n qs ρ
  eval-mulL n []       qs _       = refl
  eval-mulL n (p ∷ ps) qs (x , ρ) =
    trans (eval-addL n (scaleL n p qs) (zeroP n ∷ mulL n ps qs) (x , ρ))
      (trans (cong₂ _+_ (eval-scale n p qs x ρ)
                (trans (cong₂ _+_ (eval-zero n ρ) (cong (x *_) (eval-mulL n ps qs (x , ρ))))
                  (sym (*-assoc x PS QS))))
        (sym (dist-r (evalP n p ρ) (x * PS) QS)))
    where
      PS = evalL n ps (x , ρ)
      QS = evalL n qs (x , ρ)

eval-norm : (n : ℕ) (e : Expr) (ρ : Vals n) → evalP n (norm n e) ρ ≡ ⟦ e ⟧ₑ ρ
eval-norm n (v i)    ρ = eval-var n i ρ
eval-norm n (lit k)  ρ = eval-const n k ρ
eval-norm n (a :+ b) ρ = trans (eval-add n (norm n a) (norm n b) ρ) (cong₂ _+_ (eval-norm n a ρ) (eval-norm n b ρ))
eval-norm n (a :* b) ρ = trans (eval-mul n (norm n a) (norm n b) ρ) (cong₂ _*_ (eval-norm n a ρ) (eval-norm n b ρ))

zero-is-0 : (n : ℕ) (p : Poly n) (ρ : Vals n) → isZero n p ≡ true → evalP n p ρ ≡ 0
zero-is-0 zero    zero    _ _ = refl
zero-is-0 zero    (suc _) _ ()
zero-is-0 (suc n) []      _ _ = refl
zero-is-0 (suc n) (_ ∷ _) _ ()

eval-consP : (n : ℕ) (p : Poly n) (qs : List (Poly n)) (x : ℕ) (ρ : Vals n)
           → evalL n (consP n p qs) (x , ρ) ≡ evalP n p ρ + x * evalL n qs (x , ρ)
eval-consP n p (q ∷ qs) x ρ = refl
eval-consP n p []       x ρ with isZero n p | zero-is-0 n p ρ
... | true  | z = sym (trans (cong₂ _+_ (z refl) (*-zero x)) refl)
... | false | _ = refl

mutual
  eval-strip : (n : ℕ) (p : Poly n) (ρ : Vals n) → evalP n (strip n p) ρ ≡ evalP n p ρ
  eval-strip zero    k  _ = refl
  eval-strip (suc n) ps ρ = eval-stripL n ps ρ

  eval-stripL : (n : ℕ) (ps : List (Poly n)) (ρ : Vals (suc n)) → evalL n (stripL n ps) ρ ≡ evalL n ps ρ
  eval-stripL n []       _       = refl
  eval-stripL n (p ∷ ps) (x , ρ) =
    trans (eval-consP n (strip n p) (stripL n ps) x ρ)
      (cong₂ _+_ (eval-strip n p ρ) (cong (x *_) (eval-stripL n ps (x , ρ))))

-- Two expressions with the same canonical form are equal everywhere.
solve : (n : ℕ) (a b : Expr) → strip n (norm n a) ≡ strip n (norm n b) → (ρ : Vals n) → ⟦ a ⟧ₑ ρ ≡ ⟦ b ⟧ₑ ρ
solve n a b e ρ =
  trans (sym (eval-norm n a ρ))
    (trans (sym (eval-strip n (norm n a) ρ))
      (trans (cong (λ p → evalP n p ρ) e) (trans (eval-strip n (norm n b) ρ) (eval-norm n b ρ))))

v0 v1 v2 v3 v4 v5 v6 v7 v8 : Expr
v0 = v 0
v1 = v 1
v2 = v 2
v3 = v 3
v4 = v 4
v5 = v 5
v6 = v 6
v7 = v 7
v8 = v 8

------------------------------------------------------------------------
-- The integers

infixl 6 _+ℤ_
infixl 7 _*ℤ_
infix 4 _≈_ _≤_

record ℤ : Set where
  constructor _⊖_
  field
    pos neg : ℕ
open ℤ

_≈_ : ℤ → ℤ → Set
a ≈ b = pos a + neg b ≡ pos b + neg a

_≤ℕ_ : ℕ → ℕ → Set
m ≤ℕ n = Σ ℕ (λ k → m + k ≡ n)

_≤_ : ℤ → ℤ → Set
a ≤ b = (pos a + neg b) ≤ℕ (pos b + neg a)

0ℤ 1ℤ : ℤ
0ℤ = 0 ⊖ 0
1ℤ = 1 ⊖ 0

_+ℤ_ : ℤ → ℤ → ℤ
(ap ⊖ an) +ℤ (bp ⊖ bn) = (ap + bp) ⊖ (an + bn)

_*ℤ_ : ℤ → ℤ → ℤ
(ap ⊖ an) *ℤ (bp ⊖ bn) = (ap * bp + an * bn) ⊖ (ap * bn + an * bp)

negℤ : ℤ → ℤ
negℤ (ap ⊖ an) = an ⊖ ap

_≈?_ : (a b : ℤ) → Dec (a ≈ b)
a ≈? b = (pos a + neg b) ≟ (pos b + neg a)

≈-trans : {a b c : ℤ} → a ≈ b → b ≈ c → a ≈ c
≈-trans {ap ⊖ an} {bp ⊖ bn} {cp ⊖ cn} e₁ e₂ =
  +-cancel (ap + cn) (cp + an) (bp + bn)
    (trans (solve 6 ((v0 :+ v5) :+ (v2 :+ v3)) ((v0 :+ v3) :+ (v2 :+ v5)) refl (ap , an , bp , bn , cp , cn , tt))
      (trans (cong₂ _+_ e₁ e₂)
        (solve 6 ((v2 :+ v1) :+ (v4 :+ v3)) ((v4 :+ v1) :+ (v2 :+ v3)) refl (ap , an , bp , bn , cp , cn , tt))))

+-cong : {a b c d : ℤ} → a ≈ b → c ≈ d → a +ℤ c ≈ b +ℤ d
+-cong {ap ⊖ an} {bp ⊖ bn} {cp ⊖ cn} {dp ⊖ dn} e₁ e₂ =
  trans (swap4 ap cp bn dn) (trans (cong₂ _+_ e₁ e₂) (swap4 bp an dp cn))

*-comm-ℤ : (a b : ℤ) → a *ℤ b ≈ b *ℤ a
*-comm-ℤ (ap ⊖ an) (bp ⊖ bn) =
  solve 4 (((v0 :* v2) :+ (v1 :* v3)) :+ ((v2 :* v1) :+ (v3 :* v0)))
          (((v2 :* v0) :+ (v3 :* v1)) :+ ((v0 :* v3) :+ (v1 :* v2))) refl (ap , an , bp , bn , tt)

*-congˡ : {a b : ℤ} (c : ℤ) → a ≈ b → a *ℤ c ≈ b *ℤ c
*-congˡ {ap ⊖ an} {bp ⊖ bn} (cp ⊖ cn) e =
  trans (solve 6 (((v0 :* v4) :+ (v1 :* v5)) :+ ((v2 :* v5) :+ (v3 :* v4)))
                 (((v0 :+ v3) :* v4) :+ ((v2 :+ v1) :* v5)) refl ρ)
    (trans (cong₂ (λ s t → s * cp + t * cn) e (sym e))
      (solve 6 (((v2 :+ v1) :* v4) :+ ((v0 :+ v3) :* v5))
               (((v2 :* v4) :+ (v3 :* v5)) :+ ((v0 :* v5) :+ (v1 :* v4))) refl ρ))
  where
    ρ = ap , an , bp , bn , cp , cn , tt

*-cong : {a b c d : ℤ} → a ≈ b → c ≈ d → a *ℤ c ≈ b *ℤ d
*-cong {a} {b} {c} {d} e₁ e₂ =
  ≈-trans {a *ℤ c} {b *ℤ c} {b *ℤ d} (*-congˡ {a} {b} c e₁)
    (≈-trans {b *ℤ c} {c *ℤ b} {b *ℤ d} (*-comm-ℤ b c)
      (≈-trans {c *ℤ b} {d *ℤ b} {b *ℤ d} (*-congˡ {c} {d} b e₂) (*-comm-ℤ d b)))

neg-cong : {a b : ℤ} → a ≈ b → negℤ a ≈ negℤ b
neg-cong {ap ⊖ an} {bp ⊖ bn} e = trans (+-comm an bp) (trans (sym e) (+-comm ap bn))

≤-trans : {a b c : ℤ} → a ≤ b → b ≤ c → a ≤ c
≤-trans {ap ⊖ an} {bp ⊖ bn} {cp ⊖ cn} (k , e₁) (j , e₂) =
  k + j ,
  +-cancel (ap + cn + (k + j)) (cp + an) (bp + bn)
    (trans (solve 8 (((v0 :+ v5) :+ (v6 :+ v7)) :+ (v2 :+ v3))
                    (((v0 :+ v3) :+ v6) :+ ((v2 :+ v5) :+ v7)) refl ρ)
      (trans (cong₂ _+_ e₁ e₂)
        (solve 8 ((v2 :+ v1) :+ (v4 :+ v3)) ((v4 :+ v1) :+ (v2 :+ v3)) refl ρ)))
  where
    ρ = ap , an , bp , bn , cp , cn , k , j , tt

zero-l : (k j : ℕ) → k + j ≡ 0 → k ≡ 0
zero-l zero    j _  = refl
zero-l (suc k) j ()

≤-antisym : {a b : ℤ} → a ≤ b → b ≤ a → a ≈ b
≤-antisym {ap ⊖ an} {bp ⊖ bn} (k , e₁) (j , e₂) =
  trans (sym (+-zero (ap + bn))) (transport (λ m → ap + bn + m ≡ bp + an) (zero-l k j sum0) e₁)
  where
    -- Going round: ap + bn + (k + j) = ap + bn, so k + j = 0.
    round : ap + bn + (k + j) ≡ ap + bn + 0
    round = trans (sym (+-assoc (ap + bn) k j)) (trans (cong (_+ j) e₁) (trans e₂ (sym (+-zero _))))

    sum0 : k + j ≡ 0
    sum0 = +-cancel (k + j) 0 (ap + bn) (trans (+-comm (k + j) (ap + bn)) (trans round (+-comm (ap + bn) 0)))

≤-resp : {a b c d : ℤ} → a ≤ b → a ≈ c → b ≈ d → c ≤ d
≤-resp {ap ⊖ an} {bp ⊖ bn} {cp ⊖ cn} {dp ⊖ dn} (k , e) e₁ e₂ =
  k ,
  +-cancel (cp + dn + k) (dp + cn) (ap + bn + an + bp)
    (trans (solve 9 ((((v4 :+ v7) :+ v8) :+ (((v0 :+ v3) :+ v1) :+ v2)))
                    ((((v0 :+ v3) :+ v8) :+ (v4 :+ v1)) :+ (v2 :+ v7)) refl ρ)
      (trans (cong₂ _+_ (cong₂ _+_ e (sym e₁)) e₂)
        (solve 9 (((v2 :+ v1) :+ (v0 :+ v5)) :+ (v6 :+ v3))
                 ((v6 :+ v5) :+ (((v0 :+ v3) :+ v1) :+ v2)) refl ρ)))
  where
    ρ = ap , an , bp , bn , cp , cn , dp , dn , k , tt

≤-add : {a b : ℤ} (c : ℤ) → a ≤ b → a +ℤ c ≤ b +ℤ c
≤-add {ap ⊖ an} {bp ⊖ bn} (cp ⊖ cn) (k , e) =
  k ,
  trans (solve 7 (((v0 :+ v4) :+ (v3 :+ v5)) :+ v6) (((v0 :+ v3) :+ v6) :+ (v4 :+ v5)) refl ρ)
    (trans (cong (_+ (cp + cn)) e)
      (solve 7 ((v2 :+ v1) :+ (v4 :+ v5)) ((v2 :+ v4) :+ (v1 :+ v5)) refl ρ))
  where
    ρ = ap , an , bp , bn , cp , cn , k , tt

-- From n + k = p + 0, the positive part is n + k.
fix : (p n k : ℕ) → n + k ≡ p + 0 → p ≡ n + k
fix p n k e = trans (sym (+-zero p)) (sym e)

≤-mul : {a b : ℤ} → 0ℤ ≤ a → 0ℤ ≤ b → 0ℤ ≤ a *ℤ b
≤-mul {ap ⊖ an} {bp ⊖ bn} (k , e₁) (j , e₂) with fix ap an k e₁ | fix bp bn j e₂
... | refl | refl =
  k * j ,
  solve 4 ((((v0 :+ v1) :* v2) :+ (v0 :* (v2 :+ v3))) :+ (v1 :* v3))
          ((((v0 :+ v1) :* (v2 :+ v3)) :+ (v0 :* v2)) :+ lit 0) refl (an , k , bn , j , tt)

ℤ-ring : OrderedRing
ℤ-ring = record
  { A         = ℤ
  ; _≈ᴿ_      = _≈_
  ; _≤ᴿ_      = _≤_
  ; 0ᴿ        = 0ℤ
  ; 1ᴿ        = 1ℤ
  ; _+ᴿ_      = _+ℤ_
  ; _*ᴿ_      = _*ℤ_
  ; negᴿ      = negℤ
  ; _≈?_      = _≈?_
  ; ≈ᴿ-refl   = refl
  ; ≈ᴿ-sym    = sym
  ; ≈ᴿ-trans  = λ {a} {b} {c} → ≈-trans {a} {b} {c}
  ; +ᴿ-cong   = λ {a} {b} {c} {d} → +-cong {a} {b} {c} {d}
  ; *ᴿ-cong   = λ {a} {b} {c} {d} → *-cong {a} {b} {c} {d}
  ; neg-cong  = λ {a} {b} → neg-cong {a} {b}
  ; +ᴿ-comm   = λ { (ap ⊖ an) (bp ⊖ bn) →
                  solve 4 ((v0 :+ v2) :+ (v3 :+ v1)) ((v2 :+ v0) :+ (v1 :+ v3)) refl (ap , an , bp , bn , tt) }
  ; +ᴿ-assoc  = λ { (ap ⊖ an) (bp ⊖ bn) (cp ⊖ cn) →
                  solve 6 (((v0 :+ v2) :+ v4) :+ (v1 :+ (v3 :+ v5)))
                          ((v0 :+ (v2 :+ v4)) :+ ((v1 :+ v3) :+ v5)) refl (ap , an , bp , bn , cp , cn , tt) }
  ; +ᴿ-zero   = λ { (ap ⊖ an) → solve 2 ((v0 :+ lit 0) :+ v1) (v0 :+ (v1 :+ lit 0)) refl (ap , an , tt) }
  ; +ᴿ-neg    = λ { (ap ⊖ an) → solve 2 ((v0 :+ v1) :+ lit 0) (lit 0 :+ (v1 :+ v0)) refl (ap , an , tt) }
  ; *ᴿ-comm   = *-comm-ℤ
  ; *ᴿ-assoc  = λ { (ap ⊖ an) (bp ⊖ bn) (cp ⊖ cn) →
                  let P = λ x y z w → (x :* y) :+ (z :* w) in
                  solve 6 (P (P v0 v2 v1 v3) v4 (P v0 v3 v1 v2) v5 :+ (v0 :* P v2 v5 v3 v4 :+ v1 :* P v2 v4 v3 v5))
                          (P v0 (P v2 v4 v3 v5) v1 (P v2 v5 v3 v4) :+ (P (P v0 v2 v1 v3) v5 (P v0 v3 v1 v2) v4))
                          refl (ap , an , bp , bn , cp , cn , tt) }
  ; *ᴿ-one    = λ { (ap ⊖ an) →
                  solve 2 (((v0 :* lit 1) :+ (v1 :* lit 0)) :+ v1) (v0 :+ ((v0 :* lit 0) :+ (v1 :* lit 1))) refl (ap , an , tt) }
  ; *ᴿ-dist   = λ { (ap ⊖ an) (bp ⊖ bn) (cp ⊖ cn) →
                  solve 6 (((v0 :* (v2 :+ v4)) :+ (v1 :* (v3 :+ v5))) :+ (((v0 :* v3) :+ (v1 :* v2)) :+ ((v0 :* v5) :+ (v1 :* v4))))
                          ((((v0 :* v2) :+ (v1 :* v3)) :+ ((v0 :* v4) :+ (v1 :* v5))) :+ ((v0 :* (v3 :+ v5)) :+ (v1 :* (v2 :+ v4))))
                          refl (ap , an , bp , bn , cp , cn , tt) }
  ; ≤ᴿ-resp   = λ {a} {b} {c} {d} → ≤-resp {a} {b} {c} {d}
  ; ≤ᴿ-refl   = λ { {ap ⊖ an} → 0 , +-zero (ap + an) }
  ; ≤ᴿ-antisym = λ {a} {b} → ≤-antisym {a} {b}
  ; ≤ᴿ-trans  = λ {a} {b} {c} → ≤-trans {a} {b} {c}
  ; ≤ᴿ-add    = λ {a} {b} → ≤-add {a} {b}
  ; ≤ᴿ-mul    = λ {a} {b} → ≤-mul {a} {b}
  ; 0≤1       = 1 , refl
  ; 1≰0       = λ { (_ , ()) }
  }

------------------------------------------------------------------------
-- The theorem, in the integers: when `check` returns `Ok` for facts fs,
-- claim cl and weights ws (its rules hold of those values), no integer
-- point x makes every fact non-negative and the claim negative.

open Adequate ℤ-ring public using (OD; Facts; val; sound)
