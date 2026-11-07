import Jihoo.GraphCertificateCodec

/-! Composition of checked transformations with exact graph and selected-root
continuity. These theorems speak about supplied artifact bytes; association with
one actual compiler invocation and the runtime importer are still trusted. -/
namespace Jihoo.GraphCertificates
open CoreBridge

/-- Not merely equal denotations: the whole graph and selected root coincide. -/
def linked (previous next : Certificate) : Bool :=
  decide (previous.after = next.before ∧ previous.output = next.input)

inductive Linked : Certificate → List Certificate → Prop where
  | nil : Linked previous []
  | cons : previous.after = next.before → previous.output = next.input →
      Linked next rest → Linked previous (next :: rest)

/-- Independent meaning of the two supported operation requests. -/
def OperationMeaning (before : Graph) : Operation → Raw → Raw → Prop
  | .shift amount, input, output => output = input.rename (fun k => k + amount)
  | .substitute replacement, input, output =>
      ∃ value, Represents before replacement value ∧ output = input.subst (Raw.single value)

inductive Transforms : Raw → List Certificate → Raw → Prop where
  | nil : Transforms input [] input
  | cons : OperationMeaning c.before c.operation input middle →
      Transforms middle rest output → Transforms input (c :: rest) output

theorem expected_meaning {c : Certificate} {input output : Raw}
    (h : expected c input = some output) :
    OperationMeaning c.before c.operation input output := by
  cases hop : c.operation with
  | shift amount =>
      simp only [expected, hop] at h
      split at h <;> cases h
      rfl
  | substitute replacement =>
      simp only [expected, hop] at h
      split at h
      next =>
        cases hv : decode c.before replacement <;> simp [hv] at h
        case some value =>
          subst output
          exact ⟨value, decode_sound hv, rfl⟩
      next => contradiction

def checkFollowing (previous : Certificate) : List Certificate → Bool
  | [] => true
  | next :: rest => linked previous next && validate next && checkFollowing next rest

def validateChain (first : Certificate) (rest : List Certificate) : Bool :=
  validate first && checkFollowing first rest

def finalCertificate (first : Certificate) : List Certificate → Certificate
  | [] => first
  | next :: rest => finalCertificate next rest

theorem checkFollowing_linked {previous : Certificate} {rest : List Certificate}
    (h : checkFollowing previous rest = true) : Linked previous rest := by
  induction rest generalizing previous with
  | nil => exact .nil
  | cons next rest ih =>
      have hs := Bool.and_eq_true_iff.mp h
      have hl := of_decide_eq_true (Bool.and_eq_true_iff.mp hs.1).1
      exact .cons hl.1 hl.2 (ih hs.2)

theorem checkFollowing_transforms {previous : Certificate} {rest : List Certificate}
    {input : Raw} (h : checkFollowing previous rest = true)
    (hi : decode previous.after previous.output = some input) :
    ∃ output, decode (finalCertificate previous rest).after
      (finalCertificate previous rest).output = some output ∧ Transforms input rest output := by
  induction rest generalizing previous input with
  | nil => exact ⟨input, hi, .nil⟩
  | cons next rest ih =>
      have hs := Bool.and_eq_true_iff.mp h
      have hs' := Bool.and_eq_true_iff.mp hs.1
      have hl : previous.after = next.before ∧ previous.output = next.input :=
        of_decide_eq_true hs'.1
      obtain ⟨_, nextInput, nextOutput, hin, hout, _, _, he⟩ := validate_sound hs'.2
      rw [hl.1, hl.2, hin] at hi
      cases hi
      obtain ⟨output, ho, ht⟩ := ih hs.2 hout
      exact ⟨output, ho, .cons (expected_meaning he) ht⟩

/-- A chain accepted by the executable certificate validator has literal graph/root links
and composes every requested transformation from the first input to last output. -/
theorem validateChain_sound {first : Certificate} {rest : List Certificate}
    (h : validateChain first rest = true) :
    Linked first rest ∧
    ∃ input output, decode first.before first.input = some input ∧
      decode (finalCertificate first rest).after
        (finalCertificate first rest).output = some output ∧
      Represents first.before first.input input ∧
      Represents (finalCertificate first rest).after (finalCertificate first rest).output output ∧
      Transforms input (first :: rest) output := by
  have hs := Bool.and_eq_true_iff.mp h
  obtain ⟨_, input, middle, hin, hout, hir, _, he⟩ := validate_sound hs.1
  obtain ⟨output, ho, ht⟩ := checkFollowing_transforms hs.2 hout
  exact ⟨checkFollowing_linked hs.2, input, output, hin, ho, hir, decode_sound ho,
    .cons (expected_meaning he) ht⟩

/-- This request argument is independent of the artifact's self-description. -/
def validateRequested (previous next : Certificate) (requested : Operation) : Bool :=
  validateChain previous [next] && decide (next.operation = requested)

theorem validateRequested_sound {previous next : Certificate} {requested : Operation}
    (h : validateRequested previous next requested = true) :
    previous.after = next.before ∧ previous.output = next.input ∧
    next.operation = requested ∧
    ∃ input middle output, Represents previous.before previous.input input ∧
      Represents previous.after previous.output middle ∧
      Represents next.before next.input middle ∧
      Represents next.after next.output output ∧
      OperationMeaning previous.before previous.operation input middle ∧
      OperationMeaning next.before requested middle output := by
  have hs := Bool.and_eq_true_iff.mp h
  have hc := Bool.and_eq_true_iff.mp hs.1
  have hn := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc.2).1
  have hl : previous.after = next.before ∧ previous.output = next.input := of_decide_eq_true hn.1
  have hr : next.operation = requested := of_decide_eq_true hs.2
  obtain ⟨_, input, middle, _, hm, hir, hmr, he⟩ := validate_sound hc.1
  obtain ⟨_, middle', output, hm', _, hmr', hor, he'⟩ := validate_sound hn.2
  rw [hl.1, hl.2, hm'] at hm
  cases hm
  exact ⟨hl.1, hl.2, hr, input, middle, output, hir, hmr, hmr', hor,
    expected_meaning he, hr ▸ expected_meaning he'⟩

namespace Canonical

/-- Byte-level request validation uses the proved, complete canonical decoder. -/
def validateReplay (previousBytes nextBytes : ByteArray) (requested : Operation) : Bool :=
  match decodeCertificate previousBytes, decodeCertificate nextBytes with
  | some previous, some next => validateRequested previous next requested
  | _, _ => false

theorem validateReplay_sound {previousBytes nextBytes : ByteArray} {requested : Operation}
    (h : validateReplay previousBytes nextBytes requested = true) :
    ∃ previous next, encodeCertificate previous = previousBytes ∧
      encodeCertificate next = nextBytes ∧
      previous.after = next.before ∧ previous.output = next.input ∧ next.operation = requested ∧
      ∃ input middle output, Represents previous.before previous.input input ∧
        Represents previous.after previous.output middle ∧
        Represents next.before next.input middle ∧ Represents next.after next.output output ∧
        OperationMeaning previous.before previous.operation input middle ∧
        OperationMeaning next.before requested middle output := by
  unfold validateReplay at h
  cases hp : decodeCertificate previousBytes <;> cases hn : decodeCertificate nextBytes <;>
    simp [hp, hn] at h
  case some.some previous next =>
    exact ⟨previous, next, decodeCertificate_exact hp, decodeCertificate_exact hn,
      validateRequested_sound h⟩

end Canonical
end Jihoo.GraphCertificates
