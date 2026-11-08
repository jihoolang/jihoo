import Jihoo.LinearNaturals
import Jihoo.CheckedCoreNormalizationCodec

/-! Per-run semantic validation of actual ghost Core.normal symbolic sums.
The caller supplies the number of available U64 variables. No dependent
conversion, general normalizer refinement, or runtime arithmetic is asserted. -/
namespace Jihoo.GraphCertificates.LinearNormal
open CoreBridge LinearNaturals Typing.Wire

/-- Charge repeated references before expanding any selected term. The sum
also charges unreachable nodes. These operational limits are not a complexity
proof about Lean's runtime or the compiler. -/
def bounded (s : Snapshot) : Bool :=
  if s.graph.size > nodeLimit then false else
    match measureGraph s.graph with
    | none => false
    | some ms =>
        decide ((ms.toList.map Measure.size).sum ≤ 131072) &&
        match ms[s.termRoot]?, ms[s.typeRoot]? with
        | some t, some a => decide (t.size ≤ 8192 ∧ a.size ≤ 8192)
        | _, _ => false

def admit (s : Snapshot) (arity depth fuel : Nat) : Bool :=
  decide (arity ≤ 128) && CoreNormal.parameters depth fuel && bounded s &&
    match decode s.graph s.termRoot, decode s.graph s.typeRoot with
    | some t, some .u64 => (extract arity t).isSome
    | _, _ => false

/-- Admission already establishes the restricted input typing, before Core is
invoked. It does not promise success within Core's independent resource caps. -/
theorem admit_sound (h : admit s arity depth fuel = true) :
    ∃ t, decode s.graph s.termRoot = some t ∧ decode s.graph s.typeRoot = some .u64 ∧
      Raw.Beta.HasType (context arity) t .u64 := by
  unfold admit at h
  have hs := (Bool.and_eq_true_iff.mp h).2
  cases hi : decode s.graph s.termRoot with
  | none => simp [hi] at hs
  | some t =>
      cases ha : decode s.graph s.typeRoot with
      | none => simp [ha] at hs
      | some A =>
          cases A <;> simp only [hi, ha, Bool.false_eq_true] at hs
          case u64 =>
            cases he : extract arity t with
            | none => simp [he] at hs
            | some e =>
                exact ⟨t, rfl, rfl, by simpa only [e.property] using e.val.typed⟩

def Sound (arity : Nat) (before after : Snapshot) : Prop :=
  before.typeRoot = after.typeRoot ∧ after.graph.toList.take before.graph.size = before.graph.toList ∧
  ∃ t u, decode before.graph before.termRoot = some t ∧
    decode after.graph after.termRoot = some u ∧
    decode before.graph before.typeRoot = some .u64 ∧
    decode after.graph after.typeRoot = some .u64 ∧
    Raw.Beta.HasType (context arity) t .u64 ∧ Raw.Beta.HasType (context arity) u .u64 ∧
    ∀ ρ, ∃ v, Evaluates ρ t v ∧ Evaluates ρ u v

/-- The retained exact operation record binds complete graphs and both roots.
Equal semantic values do not prove that an operation was actually executed;
execution provenance remains an IO/driver assumption, as in the beta bridge. -/
def check (before after : Snapshot) (arity depth fuel : Nat) (c : CoreNormal.Certificate) :
    Option (PLift (CoreNormal.Matches before after depth fuel c ∧ Sound arity before after)) := do
  if hm : CoreNormal.Matches before after depth fuel c then do
    if !(admit before arity depth fuel && bounded after) then none else do
      if ht : before.typeRoot = after.typeRoot then do
        if hg : after.graph.toList.take before.graph.size = before.graph.toList then do
          match hi : decode before.graph before.termRoot, ho : decode after.graph after.termRoot,
              ha : decode before.graph before.typeRoot, hz : decode after.graph after.typeRoot with
          | some t, some u, some .u64, some .u64 => do
              let proof ← equivalent arity t u
              pure ⟨hm, ht, hg, t, u, hi, ho, ha, hz, proof.down⟩
          | _, _, _, _ => none
        else none
      else none
  else none

def validate (before after : Snapshot) (arity depth fuel : Nat) (c : CoreNormal.Certificate) : Bool :=
  (check before after arity depth fuel c).isSome

theorem validate_sound (h : validate before after arity depth fuel c = true) :
    CoreNormal.Matches before after depth fuel c ∧ Sound arity before after := by
  unfold validate at h
  cases hc : check before after arity depth fuel c with
  | none => simp [hc] at h
  | some proof => exact proof.down

def validateBytes (beforeBytes afterBytes recordBytes : ByteArray) (arity depth fuel : Nat) : Bool :=
  match decodeSnapshot beforeBytes, decodeSnapshot afterBytes, CoreNormal.Wire.decode recordBytes with
  | some before, some after, some record => validate before after arity depth fuel record
  | _, _, _ => false

theorem validateBytes_sound (h : validateBytes bb ab rb arity depth fuel = true) :
    ∃ before after record,
      encodeSnapshot before = bb ∧ encodeSnapshot after = ab ∧ CoreNormal.Wire.encode record = rb ∧
      CoreNormal.Matches before after depth fuel record ∧ Sound arity before after := by
  cases hb : decodeSnapshot bb <;> cases ha : decodeSnapshot ab <;> cases hr : CoreNormal.Wire.decode rb <;>
    simp only [validateBytes, hb, ha, hr, Bool.false_eq_true] at h
  case some.some.some before after record =>
    exact ⟨before, after, record, decodeSnapshot_exact hb, decodeSnapshot_exact ha,
      CoreNormal.Wire.decode_exact hr, validate_sound h⟩

end Jihoo.GraphCertificates.LinearNormal
