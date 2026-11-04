{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Scalar execution-to-Horn correspondence for linear.add and linear.mul.
-- Exact integer arithmetic, inclusive bounds and the overflow decision
-- are executable. The bounds are parameters, including signed i128.
--
-- The MIR intrinsic's contract is exact when its flag is false. When
-- true, its wrapped value is discarded by these two helpers, so only the
-- flag and range matter here. Computing that wrapped value, and relating
-- LLVM's intrinsics to this MIR contract, are separate obligations.
--
-- Successful and rejected helper executions derive the actual generated
-- fn.add/fn.mul rules. Rule selection checks the complete schema and the
-- variables' sorts; it does not depend on fresh rule names or positions.
------------------------------------------------------------------------
module ScalarExecution where

open import Schematic
open import Theory
open import Adequacy using (sig; OrderedRing; module Adequate)
import Integers as Z
open Z using (ℤ; _⊖_; _≈_; _≤_; _+ℤ_; _*ℤ_; ℤ-ring)
open import ListExecution using (bind; g0; g2)
open Rule
open Σ
open Rules sig rules
open Adequate ℤ-ring using (OD; closure; ⟦_⟧)

------------------------------------------------------------------------
-- Executable bounded scalar semantics

record Bounds : Set where
  constructor bounds
  field lower upper : ℤ
open Bounds

Inside : Bounds → ℤ → Set
Inside b x = (lower b ≤ x) × (x ≤ upper b)

leℕ? : (m n : ℕ) → Dec (Z._≤ℕ_ m n)
leℕ? zero n = yes (n , refl)
leℕ? (suc m) zero = no (λ { (k , ()) })
leℕ? (suc m) (suc n) with leℕ? m n
... | yes (k , e) = yes (k , cong suc e)
... | no bad = no (λ { (k , e) → bad (k , Z.suc-inj e) })

leℤ? : (a b : ℤ) → Dec (a ≤ b)
leℤ? (ap ⊖ an) (bp ⊖ bn) = leℕ? (Z._+_ ap bn) (Z._+_ bp an)

inside? : (b : Bounds) (x : ℤ) → Dec (Inside b x)
inside? b x = leℤ? (lower b) x ×? leℤ? x (upper b)

power2 : ℕ → ℕ
power2 zero = 1
power2 (suc n) = Z._+_ (power2 n) (power2 n)

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

-- n magnitude bits and one sign bit. The theorem below quantifies over
-- arbitrary bounds, so specializing it to 127 does not enumerate i128s.
signed : ℕ → Bounds
signed n = bounds (0 ⊖ power2 n) (pred (power2 n) ⊖ 0)

i128 : Bounds
i128 = signed 127

data Operation : Set where
  addition multiplication : Operation

exact : Operation → ℤ → ℤ → ℤ
exact addition a b = a +ℤ b
exact multiplication a b = a *ℤ b

checked : Bounds → Operation → ℤ → ℤ → Maybe ℤ
checked b op a c with inside? b (exact op a c)
... | yes _ = just (exact op a c)
... | no _ = nothing

successful : ∀ b op a c r → checked b op a c ≡ just r
           → Inside b r × (r ≈ exact op a c)
successful b op a c r e with inside? b (exact op a c)
... | yes ok with e
...   | refl = ok , refl
successful b op a c r () | no _

rejected : ∀ b op a c → checked b op a c ≡ nothing → ¬ Inside b (exact op a c)
rejected b op a c e with inside? b (exact op a c)
... | yes _ with e
...   | ()
rejected b op a c e | no bad = bad

reject-outside : ∀ b op a c → ¬ Inside b (exact op a c) → checked b op a c ≡ nothing
reject-outside b op a c bad with inside? b (exact op a c)
... | yes ok = ⊥-elim (bad ok)
... | no _ = refl

-- The projection of the overflowing intrinsic needed by these helpers.
-- An overflowed result may be any in-range value because the helpers
-- discard it. This is not a specification of its observable wrapped bits.
data Overflowing (b : Bounds) (v : ℤ) : ℤ → Bool → Set where
  exact-result : ∀ {r} → Inside b v → r ≈ v → Overflowing b v r false
  overflow-result : ∀ {r} → ¬ Inside b v → Inside b r → Overflowing b v r true

project : ℤ → Bool → Maybe ℤ
project r false = just r
project r true = nothing

data Same : Maybe ℤ → Maybe ℤ → Set where
  absent : Same nothing nothing
  present : ∀ {a b} → a ≈ b → Same (just a) (just b)

projection-correct : ∀ b op a c r flag → Overflowing b (exact op a c) r flag
                   → Same (project r flag) (checked b op a c)
projection-correct b op a c r false (exact-result ok e) with inside? b (exact op a c)
... | yes _ = present e
... | no bad = ⊥-elim (bad ok)
projection-correct b op a c r true (overflow-result bad ok) with inside? b (exact op a c)
... | yes p = ⊥-elim (bad p)
... | no _ = absent

------------------------------------------------------------------------
-- Find the actual generated helper rules, without trusting their names

expression : Operation → Tm → Tm → Tm
expression addition a b = #add a b
expression multiplication a b = #mul a b

call : Operation → Tm → Tm → Tm → Tm
call addition a b r = #fn·add a b r
call multiplication a b r = #fn·mul a b r

schema : Operation → Bool → Tm
schema op false = call op (var 0) (var 1) (#Option⟨i128⟩·Some (expression op (var 0) (var 1)))
schema op true = call op (var 0) (var 1) #Option⟨i128⟩·None

Matches : Tm → Rule → Set
Matches t r = (prem r ≡ []) × (concl r ≡ t) × (rs r 0 ≡ ˢZ) × (rs r 1 ≡ ˢZ)

matches? : (t : Tm) (r : Rule) → Dec (Matches t r)
matches? t r = (prem r ≟ₜs []) ×? ((concl r ≟ₜ t) ×? ((rs r 0 ≟ ˢZ) ×? (rs r 1 ≟ ˢZ)))

selected : (op : Operation) (flag : Bool) → Any (Matches (schema op flag)) rules
selected addition false = witness (any? (matches? (schema addition false)) rules) tt
selected addition true = witness (any? (matches? (schema addition true)) rules) tt
selected multiplication false = witness (any? (matches? (schema multiplication false)) rules) tt
selected multiplication true = witness (any? (matches? (schema multiplication true)) rules) tt

OnlyTwo : ℕ → Set
OnlyTwo y = (y ≡ 0) ⊎ (y ≡ 1)

onlyTwo? : (y : ℕ) → Dec (OnlyTwo y)
onlyTwo? y with y ≟ 0
... | yes e = yes (inl e)
... | no n0 with y ≟ 1
...   | yes e = yes (inr e)
...   | no n1 = no (λ { (inl e) → n0 e ; (inr e) → n1 e })

only-schema : ∀ op flag → All OnlyTwo (vars (schema op flag))
only-schema addition false = witness (all? onlyTwo? (vars (schema addition false))) tt
only-schema addition true = witness (all? onlyTwo? (vars (schema addition true))) tt
only-schema multiplication false = witness (all? onlyTwo? (vars (schema multiplication false))) tt
only-schema multiplication true = witness (all? onlyTwo? (vars (schema multiplication true))) tt

locate : ∀ {A : Set} {P : A → Set} {xs} → Any P xs → Σ A (λ x → (x ∈ xs) × P x)
locate (here p) = _ , here refl , p
locate (there p) with locate p
... | x , m , q = x , there m , q

instantiate : ∀ {t a b} → All OnlyTwo (vars t) → GroundWS a ˢZ → GroundWS b ˢZ
            → (r : Rule) → r ∈ rules → Matches t r → OD (sub (bind (a ∷ b ∷ [])) t)
instantiate {t} {a} {b} only ga gb (rule [] .t sorts) member (refl , refl , s0 , s1) =
  closure member (bind (a ∷ b ∷ [])) ok []
  where
    ok : ∀ y → OccR y (rule [] t sorts) → GroundWS (bind (a ∷ b ∷ []) y) (sorts y)
    ok y (inl ())
    ok y (inr o) with all-∈ only (occ-vars t o)
    ... | inl refl = transport (GroundWS a) (sym s0) ga
    ... | inr refl = transport (GroundWS b) (sym s1) gb

derive : ∀ op flag {a b} → GroundWS a ˢZ → GroundWS b ˢZ
       → OD (sub (bind (a ∷ b ∷ [])) (schema op flag))
derive op flag ga gb with locate (selected op flag)
... | r , member , matches = instantiate (only-schema op flag) ga gb r member matches

------------------------------------------------------------------------
-- Execution results and their Horn witnesses, read in the integers

expression-ground : ∀ op {a b} → GroundWS a ˢZ → GroundWS b ˢZ → GroundWS (expression op a b) ˢZ
expression-ground addition ga gb = g2 refl refl ga gb
expression-ground multiplication ga gb = g2 refl refl ga gb

expression-value : ∀ op {ta tb a b} → ⟦ ta ⟧ ≈ a → ⟦ tb ⟧ ≈ b
                 → ⟦ expression op ta tb ⟧ ≈ exact op a b
expression-value addition {ta} {tb} {a} {b} ea eb = Z.+-cong {⟦ ta ⟧} {a} {⟦ tb ⟧} {b} ea eb
expression-value multiplication {ta} {tb} {a} {b} ea eb = Z.*-cong {⟦ ta ⟧} {a} {⟦ tb ⟧} {b} ea eb

data Represents : Maybe ℤ → Tm → Set where
  none : Represents nothing #Option⟨i128⟩·None
  some : ∀ {r t} → GroundWS t ˢZ → ⟦ t ⟧ ≈ r → Represents (just r) (#Option⟨i128⟩·Some t)

success : ∀ op {a b} → GroundWS a ˢZ → GroundWS b ˢZ
        → OD (call op a b (#Option⟨i128⟩·Some (expression op a b)))
success addition ga gb = derive addition false ga gb
success multiplication ga gb = derive multiplication false ga gb

failure : ∀ op {a b} → GroundWS a ˢZ → GroundWS b ˢZ → OD (call op a b #Option⟨i128⟩·None)
failure addition ga gb = derive addition true ga gb
failure multiplication ga gb = derive multiplication true ga gb

checked-execution : ∀ b op a c ta tc → GroundWS ta ˢZ → GroundWS tc ˢZ
                  → ⟦ ta ⟧ ≈ a → ⟦ tc ⟧ ≈ c
                  → Σ Tm (λ r → Represents (checked b op a c) r × OD (call op ta tc r))
checked-execution b op a c ta tc ga gc ea ec with inside? b (exact op a c)
... | yes _ = #Option⟨i128⟩·Some (expression op ta tc)
            , some (expression-ground op ga gc) (expression-value op {ta} {tc} {a} {c} ea ec)
            , success op ga gc
... | no _ = #Option⟨i128⟩·None , none , failure op ga gc

intrinsic-execution : ∀ b op a c r flag ta tc → GroundWS ta ˢZ → GroundWS tc ˢZ
                    → ⟦ ta ⟧ ≈ a → ⟦ tc ⟧ ≈ c → Overflowing b (exact op a c) r flag
                    → Σ Tm (λ t → Represents (project r flag) t × OD (call op ta tc t))
intrinsic-execution b op a c r false ta tc ga gc ea ec (exact-result ok e) =
  #Option⟨i128⟩·Some (expression op ta tc)
  , some (expression-ground op ga gc)
      (Z.≈-trans {⟦ expression op ta tc ⟧} {exact op a c} {r}
        (expression-value op {ta} {tc} {a} {c} ea ec) (sym e))
  , success op ga gc
intrinsic-execution b op a c r true ta tc ga gc ea ec (overflow-result bad ok) =
  #Option⟨i128⟩·None , none , failure op ga gc
