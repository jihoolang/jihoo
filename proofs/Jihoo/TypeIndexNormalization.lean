import Jihoo.HeadNormalizationCodec

/-! Finite type-index beta traces after certified term head normalization.
The two phases have distinct roles: term traces retain the original type;
type traces retain the exact evidence term and transport its typing. -/
namespace Jihoo.GraphCertificates.TypeIndexNormalization
open CoreBridge CoreBridge.Raw Typing.Wire
abbrev Certificate := HeadNormalization.Certificate

/-- Deterministic left index first, function-spine beta only. No arithmetic
folding, binder-body search, arbitrary conversion or alternative type search. -/
def indexPath : Raw → Option (List Nat)
  | .eq a b | .lt a b =>
      match HeadNormalization.headPath a with
      | some p => some (0 :: p)
      | none => (HeadNormalization.headPath b).map (1 :: ·)
  | _ => none

def Transition (before after : Snapshot) (path : List Nat) : Prop :=
  before.termRoot = after.termRoot ∧
  ∃ t A B, decode before.graph before.termRoot = some t ∧
    decode after.graph after.termRoot = some t ∧
    decode before.graph before.typeRoot = some A ∧
    decode after.graph after.typeRoot = some B ∧
    indexPath A = some path ∧
    (∃ result, TypedBeta.contract path A = some result ∧ result.val = B) ∧
    Beta.Step A B

def checkTransition (c : TypedBeta.Certificate) : Option (PLift (Transition c.before c.after c.path)) := do
  if hr : c.before.termRoot = c.after.termRoot then do
    match ht : decode c.before.graph c.before.termRoot,
        hu : decode c.after.graph c.after.termRoot,
        ha : decode c.before.graph c.before.typeRoot,
        hb : decode c.after.graph c.after.typeRoot with
    | some t, some u, some A, some B => do
        if he : t = u then do
          if hp : indexPath A = some c.path then do
            match hc : TypedBeta.contract c.path A with
            | none => none
            | some result => do
                if hz : result.val = B then
                  pure ⟨⟨hr, t, A, B, ht, by simpa only [he] using hu, ha, hb,
                    hp, ⟨result, hc, hz⟩, hz ▸ result.property⟩⟩
                else none
          else none
        else none
    | _, _, _, _ => none
  else none

theorem Transition.preserve (h : Transition before after path) (hs : before.Sound) : after.Sound := by
  obtain ⟨_, t, A, B, ht, hu, hA, hB, _, _, step⟩ := h
  obtain ⟨t', A', ht', hA', typed, formed⟩ := hs
  rw [ht] at ht'; cases ht'
  rw [hA] at hA'; cases hA'
  exact ⟨t, B, hu, hB, typed.convert step.conversion, formed.preservation step⟩

inductive Trace : Snapshot → Certificate → Snapshot → Prop where
  | nil : Trace s [] s
  | cons : before = c.before → Transition c.before c.after c.path →
      Trace c.after rest after → Trace before (c :: rest) after

theorem Trace.preserve (h : Trace before cs after) (hs : before.Sound) : after.Sound := by
  induction h with
  | nil => exact hs
  | cons he step _ ih => exact ih (step.preserve (he ▸ hs))

theorem Trace.termRoot (h : Trace before cs after) : before.termRoot = after.termRoot := by
  induction h with
  | nil => rfl
  | cons he step _ ih => exact (congrArg Snapshot.termRoot he).trans (step.1.trans ih)

theorem Trace.evidence (h : Trace before cs after)
    (hi : decode before.graph before.termRoot = some t) :
    decode after.graph after.termRoot = some t := by
  induction h with
  | nil => exact hi
  | cons he step _ ih =>
      obtain ⟨_, u, _, _, hu, hu', _, _, _, _, _⟩ := step
      rw [he, hu] at hi; cases hi
      exact ih hu'

theorem Trace.reduction (h : Trace before cs after)
    (hi : decode before.graph before.typeRoot = some A) :
    ∃ B, decode after.graph after.typeRoot = some B ∧ Beta.Steps A B := by
  induction h generalizing A with
  | nil => exact ⟨A, hi, .refl⟩
  | cons he step _ ih =>
      obtain ⟨_, _, A', B, _, _, hA, hB, _, _, hs⟩ := step
      rw [he, hA] at hi; cases hi
      obtain ⟨C, hC, steps⟩ := ih hB
      exact ⟨C, hC, .next hs steps⟩

def checkTrace (before : Snapshot) : (cs : Certificate) →
    Option {after : Snapshot // Trace before cs after}
  | [] => some ⟨before, .nil⟩
  | c :: rest => do
      if he : before = c.before then do
        let step ← checkTransition c
        let final ← checkTrace c.after rest
        pure ⟨final.val, .cons he step.down final.property⟩
      else none

/-- The initial original-type term trace and subsequent type trace are bound to
one exact middle snapshot, including all unreachable graph nodes and root IDs. -/
def Sound (before middle after : Snapshot) (heads types : Certificate) : Prop :=
  HeadNormalization.Sound before middle heads ∧ Trace middle types after ∧ after.Sound

def checkPrefix (before middle after : Snapshot) (typing : Typing.Certificate)
    (heads types : Certificate) : Option (PLift (before.Matches typing ∧ Sound before middle after heads types)) := do
  -- Shared chain/node/expanded-work cap applies across both phases.
  if !HeadNormalization.budget before after (heads ++ types) then none else do
    let h ← HeadNormalization.check before middle typing heads
    let final ← checkTrace middle types
    if he : final.val = after then
      have trace : Trace middle types after := he ▸ final.property
      pure ⟨⟨h.down.1, h.down.2, trace, trace.preserve h.down.2.2.2.1⟩⟩
    else none

def validatePrefix (before middle after : Snapshot) (typing : Typing.Certificate)
    (heads types : Certificate) : Bool := (checkPrefix before middle after typing heads types).isSome

theorem validatePrefix_sound (h : validatePrefix before middle after typing heads types = true) :
    before.Matches typing ∧ Sound before middle after heads types := by
  unfold validatePrefix at h
  cases hc : checkPrefix before middle after typing heads types with
  | none => simp [hc] at h
  | some proof => exact proof.down

def validate (before middle after : Snapshot) (typing : Typing.Certificate)
    (heads types : Certificate) (q : Typing.Evidence.Claim) : Bool :=
  validatePrefix before middle after typing heads types && Typing.Evidence.observe after q

theorem validate_sound (h : validate before middle after typing heads types q = true) :
    before.Matches typing ∧ Sound before middle after heads types ∧ Typing.Evidence.Realized after q := by
  have hv := Bool.and_eq_true_iff.mp h
  have hs := validatePrefix_sound hv.1
  exact ⟨hs.1, hs.2, Typing.Evidence.observe_sound hs.2.2.2 hv.2⟩

/-- Both independent reductions are explicit: the term reduces at its original
type, then that original type reduces to the independently requested proposition. -/
theorem validate_lineage (h : validate before middle after typing heads types q = true) :
    ∃ t u A, decode before.graph before.termRoot = some t ∧
      decode before.graph before.typeRoot = some A ∧
      decode middle.graph middle.termRoot = some u ∧
      decode after.graph after.termRoot = some u ∧
      decode after.graph after.typeRoot = some q.asType ∧
      Beta.HasType (fun _ => none) u A ∧ Beta.HasType (fun _ => none) u q.asType ∧
      Beta.Steps t u ∧ Beta.Steps A q.asType ∧ q.Holds := by
  obtain ⟨_, sound, realized⟩ := validate_sound h
  obtain ⟨hh, trace, _⟩ := sound
  obtain ⟨t, A, ht, hA, typed, _⟩ := hh.1
  obtain ⟨u, hu, steps⟩ := hh.2.1.reduction ht
  have hA' := hh.2.1.original_type hA
  obtain ⟨B, hB, typeSteps⟩ := trace.reduction hA'
  obtain ⟨v, hv, hq, tv, _, _, truth⟩ := realized
  have hu' := trace.evidence hu
  have he : u = v := Option.some.inj (hu'.symm.trans hv)
  have heB : B = q.asType := Option.some.inj (hB.symm.trans hq)
  subst v; subst B
  exact ⟨t, u, A, ht, hA, hu, hu', hq, typed.preservation_steps steps,
    tv, steps, typeSteps, truth⟩

theorem validate_truth (h : validate before middle after typing heads types q = true) : q.Holds := by
  obtain ⟨_, _, _, _, _, _, _, _, truth⟩ := validate_sound h
  exact truth

theorem false_claim_rejected (hq : ¬ q.Holds) :
    validate before middle after typing heads types q = false := by
  cases hv : validate before middle after typing heads types q with
  | false => rfl
  | true => exact False.elim (hq (validate_truth hv))

end Jihoo.GraphCertificates.TypeIndexNormalization
