import Jihoo.TypingEvidence

/-! A bounded, data-only finite witness checker for deterministic function-spine
beta normalization. Success proves a trace and a head-normal endpoint, never
normalization of all typed programs or equivalence to Core.normal. -/
namespace Jihoo.GraphCertificates.HeadNormalization
open CoreBridge CoreBridge.Raw
open Typing.Wire

/-- Leftmost function-spine beta redex; no argument, annotation or body search. -/
def headPath : Raw → Option (List Nat)
  | .app (.lam _ _ _) _ => some []
  | .app f _ => (headPath f).map (0 :: ·)
  | _ => none

abbrev Certificate := List TypedBeta.Certificate

def stepLimit : Nat := 64
def totalNodeLimit : Nat := 32768
def workLimit : Nat := 2000000

/-- Each occurrence is charged, including identical graphs and roots repeated
in a chain. Measurements precede Raw expansion. Four endpoint charges cover
transition decoding plus final normality/observation; typing has its own budget. -/
private def charge (used : Nat × Nat) (s : Snapshot) : Option (Nat × Nat) := do
  if !graphValid s.graph then none else do
    let measures ← measureGraph s.graph
    let term ← measures[s.termRoot]?
    let type ← measures[s.typeRoot]?
    let nodes := used.1 + s.graph.size
    let work := used.2 + 4 * (term.size + type.size)
    if nodes ≤ totalNodeLimit ∧ work ≤ workLimit then some (nodes, work) else none

def budget (before after : Snapshot) (cs : Certificate) : Bool := (do
  if cs.length > stepLimit then none else do
    let used ← charge (0, 0) before
    let used ← charge used after
    cs.foldlM (fun (used : Nat × Nat) (c : TypedBeta.Certificate) => do
      if c.path.length > depthLimit then none else do
        let used ← charge used c.before
        charge used c.after) used).isSome

/-- Exact constructor-path contraction with an unchanged original type root
and decoded type. Typing is a conclusion of trace transport, not a field here. -/
def Transition (before after : Snapshot) (path : List Nat) : Prop :=
  before.typeRoot = after.typeRoot ∧
  ∃ t u A, decode before.graph before.termRoot = some t ∧
    decode before.graph before.typeRoot = some A ∧
    decode after.graph after.termRoot = some u ∧
    decode after.graph after.typeRoot = some A ∧
    headPath t = some path ∧
    (∃ result, TypedBeta.contract path t = some result ∧ result.val = u) ∧
    Beta.Step t u

def checkTransition (c : TypedBeta.Certificate) : Option (PLift (Transition c.before c.after c.path)) := do
  if ht : c.before.typeRoot = c.after.typeRoot then do
    match hi : decode c.before.graph c.before.termRoot,
        ha : decode c.before.graph c.before.typeRoot,
        ho : decode c.after.graph c.after.termRoot,
        hz : decode c.after.graph c.after.typeRoot with
    | some t, some A, some u, some B => do
        if he : A = B then do
          if hp : headPath t = some c.path then do
            match hc : TypedBeta.contract c.path t with
            | none => none
            | some result => do
                if hu : result.val = u then
                  pure ⟨⟨ht, t, u, A, hi, ha, ho, by simpa only [he] using hz,
                    hp, ⟨result, hc, hu⟩, hu ▸ result.property⟩⟩
                else none
          else none
        else none
    | _, _, _, _ => none
  else none

theorem Transition.preserve (h : Transition before after path) (hs : before.Sound) : after.Sound := by
  obtain ⟨_, t, u, A, ht, hA, hu, hA', _, _, step⟩ := h
  obtain ⟨t', A', ht', hA'', typed, formed⟩ := hs
  rw [ht] at ht'; cases ht'
  rw [hA] at hA''; cases hA''
  exact ⟨u, A, hu, hA', typed.preservation step, formed⟩

inductive Trace : Snapshot → Certificate → Snapshot → Prop where
  | nil : Trace s [] s
  | cons : before = c.before → Transition c.before c.after c.path →
      Trace c.after rest after → Trace before (c :: rest) after

theorem Trace.preserve (h : Trace before cs after) (hs : before.Sound) : after.Sound := by
  induction h with
  | nil => exact hs
  | cons he step _ ih => exact ih (step.preserve (he ▸ hs))

theorem Trace.typeRoot (h : Trace before cs after) : before.typeRoot = after.typeRoot := by
  induction h with
  | nil => rfl
  | cons he step _ ih => exact (congrArg Snapshot.typeRoot he).trans (step.1.trans ih)

theorem Trace.original_type (h : Trace before cs after)
    (hi : decode before.graph before.typeRoot = some A) :
    decode after.graph after.typeRoot = some A := by
  induction h with
  | nil => exact hi
  | cons he step _ ih =>
      obtain ⟨_, _, _, B, _, hB, _, hB', _, _, _⟩ := step
      rw [he, hB] at hi
      cases hi
      exact ih hB'

/-- Explicit reduction witness for the exact initial and final term roots. -/
theorem Trace.reduction (h : Trace before cs after)
    (hi : decode before.graph before.termRoot = some t) :
    ∃ u, decode after.graph after.termRoot = some u ∧ Beta.Steps t u := by
  induction h generalizing t with
  | nil => exact ⟨t, hi, .refl⟩
  | cons he step _ ih =>
      obtain ⟨_, t', u, _, ht', _, hu, _, _, _, hs⟩ := step
      rw [he, ht'] at hi
      cases hi
      obtain ⟨v, hv, hsteps⟩ := ih hu
      exact ⟨v, hv, .next hs hsteps⟩

def checkTrace (before : Snapshot) : (cs : Certificate) →
    Option {after : Snapshot // Trace before cs after}
  | [] => some ⟨before, .nil⟩
  | c :: rest => do
      if he : before = c.before then do
        let step ← checkTransition c
        let final ← checkTrace c.after rest
        pure ⟨final.val, .cons he step.down final.property⟩
      else none

def Normal (s : Snapshot) : Prop :=
  ∃ t, decode s.graph s.termRoot = some t ∧ Beta.headNormal t = true

def Sound (before after : Snapshot) (cs : Certificate) : Prop :=
  before.Sound ∧ Trace before cs after ∧ after.Sound ∧ Normal after

def PrefixSound (before after : Snapshot) (cs : Certificate) : Prop :=
  before.Sound ∧ Trace before cs after ∧ after.Sound

def checkPrefix (before after : Snapshot) (typing : Typing.Certificate) (cs : Certificate) :
    Option (PLift (before.Matches typing ∧ PrefixSound before after cs)) := do
  if !budget before after cs then none else do
    if hb : Typing.Wire.validateAgainst before typing = true then do
      let final ← checkTrace before cs
      if he : final.val = after then
        have hs := (Typing.Wire.validateAgainst_sound hb).2
        have trace : Trace before cs after := he ▸ final.property
        pure ⟨⟨(Typing.Wire.validateAgainst_sound hb).1, hs, trace, trace.preserve hs⟩⟩
      else none
    else none

def validatePrefix (before after : Snapshot) (typing : Typing.Certificate) (cs : Certificate) : Bool :=
  (checkPrefix before after typing cs).isSome

theorem validatePrefix_sound (h : validatePrefix before after typing cs = true) :
    before.Matches typing ∧ PrefixSound before after cs := by
  unfold validatePrefix at h
  cases hc : checkPrefix before after typing cs with
  | none => simp [hc] at h
  | some proof => exact proof.down

def check (before after : Snapshot) (typing : Typing.Certificate) (cs : Certificate) :
    Option (PLift (before.Matches typing ∧ Sound before after cs)) := do
  let checkedPrefix ← checkPrefix before after typing cs
  match ho : decode after.graph after.termRoot with
  | none => none
  | some t => do
      if hn : Beta.headNormal t = true then
        pure ⟨⟨checkedPrefix.down.1, checkedPrefix.down.2.1, checkedPrefix.down.2.2.1,
          checkedPrefix.down.2.2.2, t, ho, hn⟩⟩
      else none

def validate (before after : Snapshot) (typing : Typing.Certificate) (cs : Certificate) : Bool :=
  (check before after typing cs).isSome

theorem validate_sound (h : validate before after typing cs = true) :
    before.Matches typing ∧ Sound before after cs := by
  unfold validate at h
  cases hc : check before after typing cs with
  | none => simp [hc] at h
  | some proof => exact proof.down

theorem validate_original_type (h : validate before after typing cs = true) :
    ∃ t u A, decode before.graph before.termRoot = some t ∧
      decode before.graph before.typeRoot = some A ∧
      decode after.graph after.termRoot = some u ∧
      decode after.graph after.typeRoot = some A ∧
      Beta.HasType (fun _ => none) t A ∧ Beta.HasType (fun _ => none) u A ∧
      Beta.IsType (fun _ => none) A ∧ Beta.Steps t u ∧ Beta.headNormal u = true := by
  obtain ⟨_, hs, trace, _, v, hv, hn⟩ := validate_sound h
  obtain ⟨t, A, ht, hA, typed, formed⟩ := hs
  obtain ⟨u, hu, steps⟩ := trace.reduction ht
  have he : u = v := Option.some.inj (hu.symm.trans hv)
  exact ⟨t, u, A, ht, hA, hu, trace.original_type hA, typed,
    typed.preservation_steps steps, formed, steps, by simpa only [he] using hn⟩

def validateLiteral (before after : Snapshot) (typing : Typing.Certificate)
    (cs : Certificate) (q : Typing.Evidence.Claim) : Bool :=
  validate before after typing cs && Typing.Evidence.observe after q

theorem validateLiteral_sound (h : validateLiteral before after typing cs q = true) :
    before.Matches typing ∧ Sound before after cs ∧ Typing.Evidence.Realized after q := by
  have hv := Bool.and_eq_true_iff.mp h
  have hs := validate_sound hv.1
  exact ⟨hs.1, hs.2, Typing.Evidence.observe_sound hs.2.2.2.1 hv.2⟩

theorem validateLiteral_truth (h : validateLiteral before after typing cs q = true) : q.Holds := by
  obtain ⟨_, _, _, _, _, _, _, _, truth⟩ := validateLiteral_sound h
  exact truth

theorem false_literal_rejected (hq : ¬ q.Holds) :
    validateLiteral before after typing cs q = false := by
  cases hv : validateLiteral before after typing cs q with
  | false => rfl
  | true => exact False.elim (hq (validateLiteral_truth hv))

end Jihoo.GraphCertificates.HeadNormalization
