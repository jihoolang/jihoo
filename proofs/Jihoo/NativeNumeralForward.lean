import Jihoo.NativeEnvironmentConversionBasis

/-! Literal equality yields a genuine finite forward computation to a valid
literal. Additive splitting may expand a literal, so numerals are not assumed
to be syntactically normal in MixedRed. Numeric trees are contracted by proof,
without computing unary expansions of large machine-word constants. -/
namespace Jihoo.NativeKernel.EnvironmentDelta.NumeralForward
open NativeKernel.Conversion (ListRel)

inductive Represents : Term → Nat → Prop where
  | natural (value : Nat) : Represents (.natural value) value
  | add : Represents a m → Represents b n → Represents (.uadd a b) (m+n)

private theorem node_transport
    (children : ListRel (fun a b => ∀ {value}, Represents a value → Represents b value) xs ys)
    (represented : Represents (.node op xs) value) : Represents (.node op ys) value := by
  cases represented with
  | natural _ => cases children; exact .natural _
  | add first second =>
    cases children with
    | cons left rest => cases rest with
      | cons right rest => cases rest; exact .add (left first) (right second)

/-- Symbolic proof: no concrete replicate of a large numeral is evaluated. -/
theorem replicate_ones (value : Nat) :
    Represents (ACU.compact (List.replicate value (.natural 1))) value := by
  induction value with
  | zero => exact .natural 0
  | succ value ih =>
    cases value with
    | zero => exact .natural 1
    | succ value =>
      change Represents (.uadd (.natural 1) (ACU.compact (List.replicate (value+1) (.natural 1)))) (value+1+1)
      have result := Represents.add (.natural 1) ih
      simpa only [Nat.add_comm 1 (value+1)] using result

theorem arithmetic_preserves (step : ACU.ArithmeticRed input output) :
    ∀ {value}, Represents input value → Represents output value := by
  induction step using ACU.ArithmeticRed.rec
    (motive_2 := fun xs ys _ => ListRel
      (fun a b => ∀ {value}, Represents a value → Represents b value) xs ys) with
  | refl => intro value represented; exact represented
  | trans first second ihfirst ihsecond => intro value represented; exact ihsecond (ihfirst represented)
  | node op children ih => intro value represented; exact node_transport ih represented
  | assocRight a b c =>
    intro value represented
    cases represented with
    | add first third => cases first with
      | add first second => simpa only [Nat.add_assoc] using Represents.add first (.add second third)
  | assocLeft a b c =>
    intro value represented
    cases represented with
    | add first rest => cases rest with
      | add second third => simpa only [Nat.add_assoc] using Represents.add (.add first second) third
  | comm a b =>
    intro value represented
    cases represented with
    | add first second => simpa only [Nat.add_comm] using Represents.add second first
  | zeroRight a =>
    intro value represented
    cases represented with
    | add first second => cases second; simpa only [Nat.add_zero] using first
  | zeroLeft a =>
    intro value represented
    cases represented with
    | add first second => cases first; simpa only [Nat.zero_add] using second
  | literalSplit n bound => intro value represented; cases represented; exact replicate_ones n
  | literalAdd m n bound =>
    intro value represented
    cases represented with
    | add first second => cases first; cases second; exact .natural _
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

private theorem computes_impossible (step : ACU.Computes input output)
    (represented : Represents input value) : False := by
  cases step <;> cases represented

theorem mixed_preserves (step : ACU.MixedRed input output) :
    ∀ {value}, Represents input value → Represents output value := by
  induction step using ACU.MixedRed.rec
    (motive_2 := fun xs ys _ => ListRel
      (fun a b => ∀ {value}, Represents a value → Represents b value) xs ys) with
  | refl => intro value represented; exact represented
  | trans first second ihfirst ihsecond => intro value represented; exact ihsecond (ihfirst represented)
  | node op children ih => intro value represented; exact node_transport ih represented
  | arithmetic reduced => exact arithmetic_preserves reduced
  | compute reduced => intro value represented; exact False.elim (computes_impossible reduced represented)
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

theorem forward_preserves (step : EnvironmentDelta.Forward env input output) :
    ∀ {value}, Represents input value → Represents output value := by
  induction step using EnvironmentDelta.Forward.rec
    (motive_2 := fun xs ys _ => ListRel
      (fun a b => ∀ {value}, Represents a value → Represents b value) xs ys) with
  | refl => intro value represented; exact represented
  | trans first second ihfirst ihsecond => intro value represented; exact ihsecond (ihfirst represented)
  | node op children ih => intro value represented; exact node_transport ih represented
  | acu reduced => exact mixed_preserves reduced
  | delta found => intro value represented; cases represented
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

/-- Every numeric tree with valid total value has a forward literal contraction. -/
theorem Represents.contract (represented : Represents term value) (bound : value < 2^64) :
    EnvironmentDelta.Forward env term (.natural value) := by
  induction represented with
  | natural => exact .refl
  | @add a m b n left right ihleft ihright =>
    have first := ihleft (by omega)
    have second := ihright (by omega)
    exact .trans (.node .uadd (.cons first (.cons second .nil)))
      (.acu (.arithmetic (.literalAdd m n bound)))

/-- Actual Church--Rosser plus numeric shape gives the path to the numeral,
not merely a shared reduct or an untyped symmetric expansion. -/
theorem conversion_to_forward (admissible : EnvironmentDelta.Admissible env)
    (converted : Basis.Conv env term (.natural value)) (bound : value < 2^64) :
    EnvironmentDelta.Forward env term (.natural value) := by
  obtain ⟨common,left,right⟩ := converted.church_rosser admissible
  exact .trans left ((forward_preserves right (.natural value)).contract bound)

end Jihoo.NativeKernel.EnvironmentDelta.NumeralForward
