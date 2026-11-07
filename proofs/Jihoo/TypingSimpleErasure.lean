import Jihoo.CoreBridgeSimpleSimulation
import Jihoo.HeadNormalizationCodec

namespace Jihoo.GraphCertificates.Typing.SimpleErasure
open CoreBridge CoreBridge.Raw Beta.SimpleErasure
open Typing.Wire

/-- The exact snapshot accepted by the existing checker has a closed simple
typing. This consumes the established certificate theorem, not Core acceptance. -/
theorem snapshot_erasure {s : Snapshot} (h : s.Sound) :
    ∃ t A a, decode s.graph s.termRoot = some t ∧
      decode s.graph s.typeRoot = some A ∧ Arity A a ∧
      Typed (fun _ => none) (erase t) a := by
  obtain ⟨t, A, ht, hA, typed, _⟩ := h
  obtain ⟨a, ha, hs⟩ := closed_erasure typed
  exact ⟨t, A, a, ht, hA, ha, hs⟩

theorem validate_erasure (h : Typing.Wire.validateAgainst s c = true) :
    s.Matches c ∧ ∃ t A a, decode s.graph s.termRoot = some t ∧
      decode s.graph s.typeRoot = some A ∧ Arity A a ∧
      Typed (fun _ => none) (erase t) a :=
  ⟨(Typing.Wire.validateAgainst_sound h).1, snapshot_erasure (Typing.Wire.validateAgainst_sound h).2⟩

private theorem cons_path (hp : HeadNormalization.headPath (.app f a) = some (k :: p)) :
    k = 0 ∧ HeadNormalization.headPath f = some p := by
  cases f <;> simp_all [HeadNormalization.headPath, Option.map_eq_some_iff]

/-- Only the policy-selected function-spine path is simulated by one step.
Arbitrary contextual beta reductions may disappear under this erasure. -/
theorem selected_head_step (hp : HeadNormalization.headPath t = some p)
    (hc : TypedBeta.contract p t = some result) : HeadStep t result.val := by
  induction p generalizing t result with
  | nil =>
      cases t <;> try (simp only [TypedBeta.contract] at hc) <;> try contradiction
      case app f a =>
        cases f <;> try (simp only [TypedBeta.contract] at hc) <;> try contradiction
        case lam e A body =>
          split at hc
          next => cases hc; exact .beta
          next => contradiction
  | cons k p ih =>
      cases t <;> try (simp [HeadNormalization.headPath] at hp)
      case app f a =>
        obtain ⟨rfl, hq⟩ := cons_path hp
        simp only [TypedBeta.contract] at hc
        cases hstep : TypedBeta.contract p f with
        | none => simp [hstep] at hc
        | some step =>
            simp [hstep] at hc
            cases hc
            exact .function (ih hq hstep)

/-- The trace length is preserved exactly. No successful head contraction is
hidden as a reflexive/stuttering step in the simple calculus. -/
theorem trace_simulation (h : HeadNormalization.Trace before cs after)
    (hi : decode before.graph before.termRoot = some t) :
    ∃ u, decode after.graph after.termRoot = some u ∧ SimpleSteps cs.length (erase t) (erase u) := by
  induction h generalizing t with
  | nil => exact ⟨t, hi, .refl⟩
  | cons he step _ ih =>
      obtain ⟨_, t', u, _, ht', _, hu, _, hp, ⟨result, hc, hr⟩, _⟩ := step
      rw [he, ht'] at hi
      cases hi
      obtain ⟨v, hv, rest⟩ := ih hu
      have hs : SimpleStep (erase t) (erase u) := by
        rw [← hr]
        exact (selected_head_step hp hc).simulation
      exact ⟨v, hv, .next hs rest⟩

theorem validate_head_simulation
    (h : HeadNormalization.validate before after c cs = true) :
    ∃ t u A a, decode before.graph before.termRoot = some t ∧
      decode after.graph after.termRoot = some u ∧
      decode before.graph before.typeRoot = some A ∧ Arity A a ∧
      Typed (fun _ => none) (erase t) a ∧ Typed (fun _ => none) (erase u) a ∧
      SimpleSteps cs.length (erase t) (erase u) := by
  obtain ⟨_, hb, trace, ha, _⟩ := HeadNormalization.validate_sound h
  obtain ⟨t, A, ht, hA, typed, _⟩ := hb
  obtain ⟨a, arity, simple⟩ := closed_erasure typed
  obtain ⟨u, hu, steps⟩ := trace_simulation trace ht
  obtain ⟨u', A', hu', hA', typed', _⟩ := ha
  rw [hu] at hu'; cases hu'
  have hAf := trace.original_type hA
  rw [hAf] at hA'; cases hA'
  exact ⟨t, u, A, a, ht, hu, hA, arity, simple,
    typed_at_arity typed' (fun _ _ hx => by cases hx) arity, steps⟩

end Jihoo.GraphCertificates.Typing.SimpleErasure
