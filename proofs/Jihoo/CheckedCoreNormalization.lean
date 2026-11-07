import Jihoo.CoreBridgeComputation
import Jihoo.TypingCertificateCodec

/-! Bounded proof-producing normalization for a conservative pure fragment.
This is a validator for retained Core.normal output, not a proof of that
implementation's totality or general refinement. -/
namespace Jihoo.GraphCertificates.CoreNormal
open CoreBridge CoreBridge.Raw Typing.Wire

abbrev Reduction := CoreBridge.Raw.Computation.Step
abbrev Reductions := CoreBridge.Raw.Computation.Steps

def termLimit : Nat := 8192
def stepLimit : Nat := 64

/-- Supported normal forms: no remaining beta redex or addition. Symbolic sums,
subtraction, arrays-as-values, indexing and ZeroLe are outside this profile. -/
def normal : Raw → Bool
  | .var _ | .natural _ | .integer _ | .u64 | .i64 => true
  | .array a | .refl a => normal a
  | .lt a b | .eq a b | .pi _ a b | .lam _ a b | .decide a b => normal a && normal b
  | .app (.lam _ _ _) _ => false
  | .app f a => normal f && normal a
  | _ => false

/-- None rejects unsupported computation; some none denotes a completed scan.
A syntactic beta redex contracts before descending into its lambda or argument.
Other contexts are scanned left-to-right, with at most one contraction per scan.
Every beta expansion is guarded before substitution; no unused branch expands. -/
def next : (t : Raw) → Option (Option {u : Raw // Reduction t u})
  | .var _ | .natural _ | .integer _ | .u64 | .i64 => some none
  | .array a => do
      match ← next a with
      | some u => pure (some ⟨.array u.val, .array u.property⟩)
      | none => pure none
  | .refl a => do
      match ← next a with
      | some u => pure (some ⟨.refl u.val, .reflTerm u.property⟩)
      | none => pure none
  | .lt a b => do
      match ← next a with
      | some u => pure (some ⟨.lt u.val b, .ltLeft u.property⟩)
      | none =>
          match ← next b with
          | some u => pure (some ⟨.lt a u.val, .ltRight u.property⟩)
          | none => pure none
  | .eq a b => do
      match ← next a with
      | some u => pure (some ⟨.eq u.val b, .eqLeft u.property⟩)
      | none =>
          match ← next b with
          | some u => pure (some ⟨.eq a u.val, .eqRight u.property⟩)
          | none => pure none
  | .pi e a b => do
      match ← next a with
      | some u => pure (some ⟨.pi e u.val b, .piDomain u.property⟩)
      | none =>
          match ← next b with
          | some u => pure (some ⟨.pi e a u.val, .piCodomain u.property⟩)
          | none => pure none
  | .lam e a b => do
      match ← next a with
      | some u => pure (some ⟨.lam e u.val b, .lamDomain u.property⟩)
      | none =>
          match ← next b with
          | some u => pure (some ⟨.lam e a u.val, .lamBody u.property⟩)
          | none => pure none
  | .decide a b => do
      match ← next a with
      | some u => pure (some ⟨.decide u.val b, .decideLeft u.property⟩)
      | none =>
          match ← next b with
          | some u => pure (some ⟨.decide a u.val, .decideRight u.property⟩)
          | none => pure none
  | .app (.lam e A body) b =>
      if Typing.rawSize body * (Typing.rawSize b + 1) ≤ termLimit ∧
          Typing.rawDepth body + Typing.rawDepth b ≤ depthLimit then
        some (some ⟨body.subst (single b), Computation.Step.beta e A body b⟩)
      else none
  | .app a b => do
      match ← next a with
      | some u => pure (some ⟨.app u.val b, .appFunction u.property⟩)
      | none =>
          match ← next b with
          | some u => pure (some ⟨.app a u.val, .appArgument u.property⟩)
          | none => pure none
  | .uadd a b => do
      match ← next a with
      | some u => pure (some ⟨.uadd u.val b, .uaddLeft u.property⟩)
      | none =>
          match ← next b with
          | some u => pure (some ⟨.uadd a u.val, .uaddRight u.property⟩)
          | none => 
              match ha : a, hb : b with
              | .natural m, .natural n =>
                  if h : m + n < wordBound then
                    pure (some ⟨.natural (m + n), by simpa only [ha, hb] using (Computation.Step.add m n h)⟩)
                  else none
              | _, _ => none
  | _ => none

/-- Fuel counts total contractions, not depth per branch. Every scan is guarded
by total expanded tree size/depth, including duplicated references. -/
def run (fuel : Nat) (t : Raw) : Option {u : Raw // Reductions t u ∧ normal u = true} := do
  if Typing.rawSize t > termLimit ∨ Typing.rawDepth t > depthLimit then none else do
    match ← next t with
    | none => if hn : normal t = true then some ⟨t, .refl, hn⟩ else none
    | some step =>
        match fuel with
        | 0 => none
        | n + 1 => do
            let result ← run n step.val
            pure ⟨result.val, .next step.property result.property.1, result.property.2⟩
termination_by fuel

theorem run_sound (h : (run fuel t).isSome = true) :
    ∃ u, Reductions t u ∧ normal u = true := by
  cases hr : run fuel t with
  | none => simp [hr] at h
  | some result => exact ⟨result.val, result.property⟩

theorem run_typed (h : (run fuel t).isSome = true) (ht : Beta.HasType Γ t A) :
    ∃ u, Reductions t u ∧ normal u = true ∧ Beta.HasType Γ u A := by
  obtain ⟨u, steps, hn⟩ := run_sound h
  exact ⟨u, steps, hn, Computation.preservation_steps ht steps⟩

structure Certificate where
  before : Snapshot
  after : Snapshot
  depth : Nat
  fuel : Nat
  deriving DecidableEq, Repr

def Matches (before after : Snapshot) (depth fuel : Nat) (c : Certificate) : Prop :=
  c.before = before ∧ c.after = after ∧ c.depth = depth ∧ c.fuel = fuel
instance : Decidable (Matches before after depth fuel c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def parameters (depth fuel : Nat) : Bool := decide (0 < depth ∧ depth ≤ depthLimit ∧ fuel ≤ stepLimit)

/-- Input-only gate used before invoking actual Core.normal. It establishes that
this bounded proof search succeeds, not that Core will meet its own resource cap. -/
def admit (s : Snapshot) (typing : Typing.Certificate) (depth fuel : Nat) : Bool :=
  parameters depth fuel && Typing.Wire.validateAgainst s typing &&
    match decode s.graph s.termRoot with
    | some t => (run fuel t).isSome
    | none => false

theorem admit_typing (h : admit s typing depth fuel = true) : s.Matches typing ∧ s.Sound := by
  have hv : Typing.Wire.validateAgainst s typing = true := by
    unfold admit at h
    cases hp : parameters depth fuel <;>
      cases ht : Typing.Wire.validateAgainst s typing <;> simp_all
  exact Typing.Wire.validateAgainst_sound hv

def Sound (before after : Snapshot) : Prop :=
  before.typeRoot = after.typeRoot ∧ after.graph.toList.take before.graph.size = before.graph.toList ∧
  ∃ t u A, decode before.graph before.termRoot = some t ∧
    decode before.graph before.typeRoot = some A ∧ decode after.graph after.termRoot = some u ∧
    decode after.graph after.typeRoot = some A ∧ Reductions t u ∧ normal u = true ∧
    Beta.HasType (fun _ => none) t A ∧ Beta.HasType (fun _ => none) u A ∧ Beta.IsType (fun _ => none) A

def check (before after : Snapshot) (typing : Typing.Certificate) (depth fuel : Nat) (c : Certificate) :
    Option (PLift (Matches before after depth fuel c ∧ before.Matches typing ∧ Sound before after)) := do
  if hm : Matches before after depth fuel c then do
    if !parameters depth fuel then none else do
      if hv : Typing.Wire.validateAgainst before typing = true then do
        if ht : before.typeRoot = after.typeRoot then do
          if hg : after.graph.toList.take before.graph.size = before.graph.toList then do
            match hi : decode before.graph before.termRoot, ha : decode before.graph before.typeRoot,
                ho : decode after.graph after.termRoot, hz : decode after.graph after.typeRoot with
            | some t, some A, some u, some B => do
                if he : A = B then do
                  let result ← run fuel t
                  if hr : result.val = u then
                    have steps : Reductions t u := hr ▸ result.property.1
                    have hn : normal u = true := hr ▸ result.property.2
                    have hb := Typing.Wire.validateAgainst_sound hv
                    have hs : Beta.HasType (fun _ => none) t A ∧ Beta.IsType (fun _ => none) A := by
                      obtain ⟨t', A', hi', ha', typed, formed⟩ := hb.2
                      rw [hi] at hi'; cases hi'
                      rw [ha] at ha'; cases ha'
                      exact ⟨typed, formed⟩
                    pure ⟨hm, hb.1, ht, hg, t, u, A, hi, ha, ho, by simpa only [he] using hz,
                      steps, hn, hs.1, Computation.preservation_steps hs.1 steps, hs.2⟩
                  else none
                else none
            | _, _, _, _ => none
          else none
        else none
      else none
  else none

def validate (before after : Snapshot) (typing : Typing.Certificate) (depth fuel : Nat) (c : Certificate) : Bool :=
  (check before after typing depth fuel c).isSome

theorem validate_sound (h : validate before after typing depth fuel c = true) :
    Matches before after depth fuel c ∧ before.Matches typing ∧ Sound before after := by
  unfold validate at h
  cases hc : check before after typing depth fuel c with
  | none => simp [hc] at h
  | some proof => exact proof.down

end Jihoo.GraphCertificates.CoreNormal
