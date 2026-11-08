import Jihoo.CorePrincipalEvidence
import Jihoo.CheckedLinearEvidence

/-! Exact principal-type validation of a jointly retained Core.infer/require
artifact pair. Graph/export/execution fidelity remains an external boundary. -/
namespace Jihoo.GraphCertificates.CorePrincipalCheck
open CoreBridge LinearNaturals LinearEvidence CorePrincipal Typing.Wire

structure Sound (requested inferred : Snapshot) : Prop where
  graph : requested.graph = inferred.graph
  term : requested.termRoot = inferred.termRoot
  realization : ∃ t, ∃ p q : Formula 0,
    decode requested.graph requested.termRoot = some t ∧
    decode requested.graph requested.typeRoot = some q.encode ∧
    decode inferred.graph inferred.typeRoot = some p.encode ∧
    Principal t p ∧ Converts p q ∧ Derives t q ∧ DecisionBounded t ∧
    (∀ ρ, q.Holds ρ) ∧ Raw.Beta.IsType (context 0) q.encode

def check (requested inferred : Snapshot) (termRoot requestedRoot inferredRoot : Nat) :
    Option (PLift (requested.termRoot = termRoot ∧ requested.typeRoot = requestedRoot ∧
      inferred.typeRoot = inferredRoot ∧ Sound requested inferred)) := do
  if ht : requested.termRoot = termRoot then do
    if hr : requested.typeRoot = requestedRoot then do
      if hi : inferred.typeRoot = inferredRoot then do
        if hg : requested.graph = inferred.graph then do
          if hm : requested.termRoot = inferred.termRoot then do
            if !(LinearNormal.bounded requested && LinearNormal.bounded inferred) then none else do
              match hterm : decode requested.graph requested.termRoot,
                  hreq : decode requested.graph requested.typeRoot,
                  hinf : decode inferred.graph inferred.typeRoot with
              | some t, some A, some B => do
                  let p ← CorePrincipal.infer 0 t
                  if he : p.val.encode = B then do
                    let q ← parseFormula 0 A
                    let hc ← conversion p.val q.val
                    have hd : Derives t q.val := .convert p.property.derives hc.down
                    pure ⟨ht, hr, hi, hg, hm, t, p.val, q.val, hterm,
                      by simpa only [q.property] using hreq,
                      by simpa only [he] using hinf,
                      p.property, hc.down, hd, p.property.bounded, hd.sound, q.val.formed⟩
                  else none
              | _, _, _ => none
          else none
        else none
      else none
    else none
  else none

def validate (requested inferred : Snapshot) (termRoot requestedRoot inferredRoot : Nat) : Bool :=
  (check requested inferred termRoot requestedRoot inferredRoot).isSome

theorem validate_sound (h : validate requested inferred termRoot requestedRoot inferredRoot = true) :
    requested.termRoot = termRoot ∧ requested.typeRoot = requestedRoot ∧
      inferred.typeRoot = inferredRoot ∧ Sound requested inferred := by
  unfold validate at h
  cases hc : check requested inferred termRoot requestedRoot inferredRoot with
  | none => simp [hc] at h
  | some p => exact p.down

def validateBytes (requestedBytes inferredBytes : ByteArray) (termRoot requestedRoot inferredRoot : Nat) : Bool :=
  match decodeSnapshot requestedBytes, decodeSnapshot inferredBytes with
  | some requested, some inferred => validate requested inferred termRoot requestedRoot inferredRoot
  | _, _ => false

theorem validateBytes_sound (h : validateBytes rb ib termRoot requestedRoot inferredRoot = true) :
    ∃ requested inferred, encodeSnapshot requested = rb ∧ encodeSnapshot inferred = ib ∧
      requested.termRoot = termRoot ∧ requested.typeRoot = requestedRoot ∧
      inferred.typeRoot = inferredRoot ∧ Sound requested inferred := by
  cases hr : decodeSnapshot rb <;> cases hi : decodeSnapshot ib <;>
    simp only [validateBytes, hr, hi, Bool.false_eq_true] at h
  case some.some r i =>
    exact ⟨r, i, decodeSnapshot_exact hr, decodeSnapshot_exact hi, validate_sound h⟩

end Jihoo.GraphCertificates.CorePrincipalCheck
