import Jihoo.LinearSubstitution
import Jihoo.CheckedCorePrincipal

/-! Validate one selected closed first-order application using retained actual
function inference, type normalization, application inference and require data.
The theorem checks observations; it does not verify their execution provenance. -/
namespace Jihoo.GraphCertificates.FirstOrderApplication
open CoreBridge LinearNaturals LinearEvidence CorePrincipal Typing.Wire

structure Trace where
  function : Snapshot
  normalized : Snapshot
  inferred : Snapshot
  requested : Snapshot
  deriving DecidableEq, Repr

structure Roots where
  function : Nat
  functionType : Nat
  normalizedType : Nat
  application : Nat
  inferredType : Nat
  requestedType : Nat
  deriving DecidableEq, Repr

def Matches (c : Trace) (r : Roots) : Prop :=
  c.function.termRoot = r.function ∧ c.function.typeRoot = r.functionType ∧
  c.normalized.termRoot = r.function ∧ c.normalized.typeRoot = r.normalizedType ∧
  c.inferred.termRoot = r.application ∧ c.inferred.typeRoot = r.inferredType ∧
  c.requested.termRoot = r.application ∧ c.requested.typeRoot = r.requestedType
instance : Decidable (Matches c r) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def GraphsAgree (c : Trace) : Prop :=
  c.function.graph = c.normalized.graph ∧ c.function.graph = c.inferred.graph ∧
  c.function.graph = c.requested.graph
instance : Decidable (GraphsAgree c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Conservative expansion guard, checked before constructing the substituted
formula. This charges repeated argument occurrences, not only DAG nodes. -/
def substitutionSafe (body argument : Raw) : Bool :=
  decide ((Typing.rawSize body + 1) * (Typing.rawSize argument + 1) ≤ 8192 ∧
    Typing.rawDepth body + Typing.rawDepth argument ≤ depthLimit)

structure Sound (c : Trace) : Prop where
  graphs : GraphsAgree c
  selected : ∃ argumentRoot, c.inferred.graph[c.inferred.termRoot]? =
    some (.app c.function.termRoot argumentRoot)
  realization : ∃ f, ∃ a : Expr 0, ∃ p : Formula 0, ∃ q : Formula 1, ∃ r : Formula 0,
    decode c.function.graph c.function.termRoot = some f ∧
    decode c.function.graph c.function.typeRoot = some p.encode ∧
    decode c.normalized.graph c.normalized.typeRoot = some (Formula.all q).encode ∧
    decode c.inferred.graph c.inferred.termRoot = some (.app f a.encode) ∧
    decode c.inferred.graph c.inferred.typeRoot = some (q.encode.subst (Raw.single a.encode)) ∧
    decode c.requested.graph c.requested.typeRoot = some r.encode ∧
    Principal f p ∧ Converts p (.all q) ∧ Converts (q.instantiate a) r ∧
    Applied (.app f a.encode) r ∧ (∀ ρ, r.Holds ρ) ∧
    Raw.Beta.HasType (context 0) a.encode .u64 ∧ Raw.Beta.IsType (context 0) r.encode

def check (c : Trace) (roots : Roots) : Option (PLift (Matches c roots ∧ Sound c)) := do
  if hm : Matches c roots then do
    if hg : GraphsAgree c then do
      if !(LinearNormal.bounded c.function && LinearNormal.bounded c.normalized &&
          LinearNormal.bounded c.inferred && LinearNormal.bounded c.requested) then none else do
        match hn : c.inferred.graph[c.inferred.termRoot]? with
        | some (.app functionRoot argumentRoot) => do
          if hfroot : functionRoot = c.function.termRoot then do
            match hf : decode c.function.graph c.function.termRoot,
                hft : decode c.function.graph c.function.typeRoot,
                hnt : decode c.normalized.graph c.normalized.typeRoot,
                happ : decode c.inferred.graph c.inferred.termRoot,
                hit : decode c.inferred.graph c.inferred.typeRoot,
                hrt : decode c.requested.graph c.requested.typeRoot with
            | some f, some F, some N, some (.app f' a), some I, some R => do
              if he : f' = f then do
                let p ← CorePrincipal.infer 0 f
                if hp : p.val.encode = F then do
                  let normalized ← parseFormula 0 N
                  let hc ← conversion p.val normalized.val
                  match hq : normalized.val with
                  | .all q => do
                    let argument ← extract 0 a
                    if !substitutionSafe q.encode a then none else do
                      let result := q.instantiate argument.val
                      if hi : result.encode = I then do
                        let requested ← parseFormula 0 R
                        let conv ← conversion result requested.val
                        have hfunction : Applied f (.all q) := .convert (.base p.property.derives)
                          (by simpa only [hq] using hc.down)
                        have ha : Applied (.app f argument.val.encode) requested.val :=
                          .convert (.app hfunction argument.val) conv.down
                        pure ⟨hm, hg, ⟨argumentRoot, by simpa only [hfroot] using hn⟩,
                          f, argument.val, p.val, q, requested.val, hf,
                          by simpa only [hp] using hft,
                          by simpa only [← normalized.property, hq] using hnt,
                          by simpa only [he, argument.property] using happ,
                          by rw [← q.encode_instantiate argument.val]; simpa only [result, hi] using hit,
                          by simpa only [requested.property] using hrt,
                          p.property, by simpa only [hq] using hc.down,
                          conv.down, ha, ha.sound, argument.val.typed, requested.val.formed⟩
                      else none
                  | _ => none
                else none
              else none
            | _, _, _, _, _, _ => none
          else none
        | _ => none
    else none
  else none

def validate (c : Trace) (roots : Roots) : Bool := (check c roots).isSome

theorem validate_sound (h : validate c roots = true) : Matches c roots ∧ Sound c := by
  unfold validate at h
  cases hc : check c roots with
  | none => simp [hc] at h
  | some p => exact p.down

def validateBytes (fb nb ib rb : ByteArray) (roots : Roots) : Bool :=
  match decodeSnapshot fb, decodeSnapshot nb, decodeSnapshot ib, decodeSnapshot rb with
  | some f, some n, some i, some r => validate ⟨f, n, i, r⟩ roots
  | _, _, _, _ => false

theorem validateBytes_sound (h : validateBytes fb nb ib rb roots = true) :
    ∃ c, encodeSnapshot c.function = fb ∧ encodeSnapshot c.normalized = nb ∧
      encodeSnapshot c.inferred = ib ∧ encodeSnapshot c.requested = rb ∧ Matches c roots ∧ Sound c := by
  cases hf : decodeSnapshot fb <;> cases hn : decodeSnapshot nb <;>
    cases hi : decodeSnapshot ib <;> cases hr : decodeSnapshot rb <;>
    simp only [validateBytes, hf, hn, hi, hr, Bool.false_eq_true] at h
  case some.some.some.some f n i r =>
    exact ⟨⟨f, n, i, r⟩, decodeSnapshot_exact hf, decodeSnapshot_exact hn,
      decodeSnapshot_exact hi, decodeSnapshot_exact hr, validate_sound h⟩

end Jihoo.GraphCertificates.FirstOrderApplication
