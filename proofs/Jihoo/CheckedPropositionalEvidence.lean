import Jihoo.PropositionalEvidence
import Jihoo.CheckedLinearEvidence

/-! Closed higher-order propositional validation of a retained Core.infer/require
artifact pair. Graph/export/execution fidelity remains an external boundary. -/
namespace Jihoo.GraphCertificates.PropositionalCheck
open CoreBridge PropositionalEvidence Typing.Wire

structure Sound (requested inferred : Snapshot) : Prop where
  graph : requested.graph = inferred.graph
  term : requested.termRoot = inferred.termRoot
  realization : ∃ t, ∃ p q : PropositionalEvidence.Ty,
    decode requested.graph requested.termRoot = some t ∧
    decode requested.graph requested.typeRoot = some q.encode ∧
    decode inferred.graph inferred.typeRoot = some p.encode ∧
    Derives [] t p ∧ Converts p q ∧ Derives [] t q ∧ q.Holds ∧
    Raw.Beta.IsType (fun _ => none) q.encode

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
                  let p ← PropositionalEvidence.infer 128 32768 [] t
                  if he : p.type.encode = B then do
                    let q ← parse A
                    let hc ← conversion p.type q.val
                    have hd : Derives [] t q.val := .convert p.derives hc.down
                    pure ⟨ht, hr, hi, hg, hm, t, p.type, q.val, hterm,
                      by simpa only [q.property] using hreq,
                      by simpa only [he] using hinf,
                      p.derives, hc.down, hd, hd.closed_sound, q.val.formed _⟩
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

end Jihoo.GraphCertificates.PropositionalCheck
