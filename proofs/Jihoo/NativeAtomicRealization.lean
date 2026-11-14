import Jihoo.NativeSemanticCandidates
import Jihoo.NativeEnvironmentContextualPreservation

/-! Atomic proposition realization over actual native terms and full ACU.
Numeral observations are constructive conversion certificates produced by the
concrete bounded normalizer; no numeric equality is accepted as a conversion
oracle. The full typing fundamental lemma remains a later obligation. -/
namespace Jihoo.NativeKernel.Environment.Semantics
open Jihoo.NativeKernel.Environment.Conversion

structure NumeralObservation (env : Environment) (term : Term) where
  value : Nat
  bound : value < 2^64
  converted : Conv env term (.natural value)

def observeNumeral (env : Environment) (fuel : Nat) (term : Term) : Option Nat := do
  let normal ← Conversion.normalize? env fuel term
  match normal with
  | .natural value => if value < 2^64 then some value else none
  | _ => none

theorem observeNumeral_sound (observed : observeNumeral env fuel term = some value) :
    ∃ observation : NumeralObservation env term, observation.value = value := by
  unfold observeNumeral at observed
  cases normalized : Conversion.normalize? env fuel term with
  | none => simp [normalized] at observed
  | some normal =>
    simp only [normalized,Bind.bind,Option.bind] at observed
    split at observed
    · split at observed
      · cases observed
        exact ⟨⟨_,by assumption,Conversion.normalize?_sound normalized⟩,rfl⟩
      · contradiction
    · contradiction

def NumeralObservation.literal {value : Nat} (bound : value < 2^64) :
    NumeralObservation env (.natural value) := ⟨value,bound,.refl _⟩

theorem NumeralObservation.unique (wf : UnifiedProgram.EnvWellFormed env) (first second : NumeralObservation env term) : first.value = second.value :=
  (EnvironmentDelta.Basis.Conv.trans (.symm first.converted) second.converted).natural_injective wf.admissible

def NumeralObservation.add (first : NumeralObservation env a) (second : NumeralObservation env b)
    (bound : first.value + second.value < 2^64) : NumeralObservation env (.uadd a b) :=
  ⟨first.value + second.value,bound,.trans
    (.node .uadd (.cons first.converted (.cons second.converted .nil)))
    (.legacy (.add first.value second.value bound))⟩

/-- An independently generated realization of an atomic proposition class.
Equality carries actual endpoint conversion. Strict bounds carry independently
observed endpoints and a primitive mathematical order derivation. -/
inductive AtomicTruth (env : Environment) : Term → Prop where
  | equality : Conv env left right → AtomicTruth env (.eq left right)
  | less : Conv env left (.natural m) → Conv env right (.natural n) → m < n → AtomicTruth env (.lt left right)
  | convert : AtomicTruth env original → Conv env original replacement → AtomicTruth env replacement

theorem AtomicTruth.extend (realized : AtomicTruth before type) (extension : Environment.Extends before after) :
    AtomicTruth after type := by
  induction realized with
  | equality converted => exact .equality (converted.extend extension)
  | less left right ordered => exact .less (left.extend extension) (right.extend extension) ordered
  | convert _ converted ih => exact .convert ih (converted.extend extension)

private theorem eq_lt_separate (wf : UnifiedProgram.EnvWellFormed env) : ¬ Conv env (.eq a b) (.lt c d) :=
  fun h => EnvironmentDelta.Basis.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same) h wf.admissible

theorem AtomicTruth.equal_endpoints (wf : UnifiedProgram.EnvWellFormed env) (realized : AtomicTruth env T) :
    ∀ {left right}, Conv env T (.eq left right) → Conv env left right := by
  induction realized with
  | equality equal =>
    intro left right converted
    have endpoints := converted.eq_injective wf.admissible
    exact .trans (.symm endpoints.1) (.trans equal endpoints.2)
  | less left right ordered =>
    intro a b converted
    exact False.elim (eq_lt_separate wf (.symm converted))
  | convert realized converted ih => intro left right target; exact ih (.trans converted target)

theorem AtomicTruth.less_numerals (wf : UnifiedProgram.EnvWellFormed env) (realized : AtomicTruth env T) :
    ∀ {m n}, Conv env T (.lt (.natural m) (.natural n)) → m < n := by
  induction realized with
  | equality equal => intro m n converted; exact False.elim (eq_lt_separate wf converted)
  | @less left m right n cleft cright ordered =>
    intro m' n' converted
    have endpoints := converted.lt_injective wf.admissible
    have first := (EnvironmentDelta.Basis.Conv.trans (.symm cleft) endpoints.1).natural_injective wf.admissible
    have second := (EnvironmentDelta.Basis.Conv.trans (.symm cright) endpoints.2).natural_injective wf.admissible
    simpa only [←first,←second] using ordered
  | convert realized converted ih => intro m n target; exact ih (.trans converted target)

theorem AtomicTruth.less_zero_false (wf : UnifiedProgram.EnvWellFormed env) (realized : AtomicTruth env T) :
    ∀ {index}, Conv env T (.lt index (.natural 0)) → False := by
  induction realized with
  | equality equal => intro index converted; exact eq_lt_separate wf converted
  | @less left m right n cleft cright ordered =>
    intro index converted
    have zero := (EnvironmentDelta.Basis.Conv.trans (.symm cright) (converted.lt_injective wf.admissible).2).natural_injective wf.admissible
    omega
  | convert realized converted ih => intro index target; exact ih (.trans converted target)

theorem AtomicTruth.no_false_equality (wf : UnifiedProgram.EnvWellFormed env) (different : m ≠ n) :
    ¬ AtomicTruth env (.eq (.natural m) (.natural n)) := by
  intro realized
  exact different ((equal_endpoints wf realized (.refl _)).natural_injective wf.admissible)

theorem AtomicTruth.no_false_less (wf : UnifiedProgram.EnvWellFormed env) (unordered : ¬ m < n) :
    ¬ AtomicTruth env (.lt (.natural m) (.natural n)) := fun realized => unordered (less_numerals wf realized (.refl _))

def atomic (type : Term) : Candidate env := proposition (AtomicTruth env type)

theorem AtomicTruth.transport (wf : UnifiedProgram.EnvWellFormed env) (realized : AtomicTruth env (.app predicate a))
    (equal : AtomicTruth env (.eq a b)) : AtomicTruth env (.app predicate b) :=
  .convert realized (.node .app (.cons (.refl _) (.cons (equal_endpoints wf equal (.refl _)) .nil)))

theorem AtomicTruth.zeroLe (observed : NumeralObservation env index) (bound : observed.value + 1 < 2^64) :
    AtomicTruth env (.lt (.natural 0) (.uadd index (.natural 1))) := by
  let next := observed.add (NumeralObservation.literal (env := env) (value := 1) (by decide)) bound
  exact .less (.refl _) next.converted (by change 0 < observed.value + 1; omega)

theorem AtomicTruth.ltAdd (wf : UnifiedProgram.EnvWellFormed env) (realized : AtomicTruth env (.lt a b))
    (first : NumeralObservation env a) (second : NumeralObservation env b) (step : NumeralObservation env c)
    (leftBound : first.value + step.value < 2^64) (rightBound : second.value + step.value < 2^64) :
    AtomicTruth env (.lt (.uadd a c) (.uadd b c)) := by
  have ordered := less_numerals wf realized (.node .lt (.cons first.converted (.cons second.converted .nil)))
  exact .less (first.add step leftBound).converted (second.add step rightBound).converted (by change first.value + step.value < second.value + step.value; omega)

theorem AtomicTruth.ltCancel (wf : UnifiedProgram.EnvWellFormed env) (realized : AtomicTruth env (.lt (.uadd a c) (.uadd b c)))
    (first : NumeralObservation env a) (second : NumeralObservation env b) (step : NumeralObservation env c)
    (leftBound : first.value + step.value < 2^64) (rightBound : second.value + step.value < 2^64) :
    AtomicTruth env (.lt a b) := by
  have ordered := AtomicTruth.less_numerals wf realized
    (.node .lt (.cons (first.add step leftBound).converted (.cons (second.add step rightBound).converted .nil)))
  change first.value + step.value < second.value + step.value at ordered
  exact .less first.converted second.converted (by omega)

theorem AtomicTruth.ltLe (wf : UnifiedProgram.EnvWellFormed env) (lower : AtomicTruth env (.lt a b)) (upper : AtomicTruth env (.lt b (.uadd c (.natural 1))))
    (first : NumeralObservation env a) (middle : NumeralObservation env b) (last : NumeralObservation env c)
    (bound : last.value + 1 < 2^64) : AtomicTruth env (.lt a c) := by
  let one := NumeralObservation.literal (env := env) (value := 1) (by decide)
  let next := last.add one bound
  have lo := less_numerals wf lower (.node .lt (.cons first.converted (.cons middle.converted .nil)))
  have hi := less_numerals wf upper (.node .lt (.cons middle.converted (.cons next.converted .nil)))
  change middle.value < last.value + 1 at hi
  exact .less first.converted last.converted (by omega)

end Jihoo.NativeKernel.Environment.Semantics
