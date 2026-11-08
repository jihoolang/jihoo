import Jihoo.CheckedFirstOrderApplication

/-! A bounded, proof-carrying application spine. Each next function is the exact
previous inferred snapshot, including its graph and both roots. No intermediate
output typing is assumed or re-seeded from an unrelated principal certificate. -/
namespace Jihoo.GraphCertificates.ApplicationSpine
open CoreBridge LinearNaturals LinearEvidence CorePrincipal Typing.Wire

def linkLimit : Nat := 16
def workLimit : Nat := 32768

def charge (body argument : Raw) : Nat :=
  (Typing.rawSize body + 1) * (Typing.rawSize argument + 1)

structure State where
  snapshot : Snapshot
  term : Raw
  formula : Formula 0
  remaining : Nat
  termDecoded : decode snapshot.graph snapshot.termRoot = some term
  typeDecoded : decode snapshot.graph snapshot.typeRoot = some formula.encode
  evidence : Applied term formula

structure Transition (before : State) (normalized : Snapshot) (after : State) : Prop where
  normalGraph : normalized.graph = before.snapshot.graph
  outputGraph : after.snapshot.graph = before.snapshot.graph
  normalRoot : normalized.termRoot = before.snapshot.termRoot
  selected : ∃ argumentRoot, after.snapshot.graph[after.snapshot.termRoot]? =
    some (.app before.snapshot.termRoot argumentRoot)
  observation : ∃ q : Formula 1, ∃ a : Expr 0,
    decode normalized.graph normalized.typeRoot = some (Formula.all q).encode ∧
    Converts before.formula (.all q) ∧
    after.term = .app before.term a.encode ∧ after.formula = q.instantiate a ∧
    after.remaining = before.remaining - charge q.encode a.encode ∧
    charge q.encode a.encode ≤ before.remaining ∧
    FirstOrderApplication.substitutionSafe q.encode a.encode = true

inductive Chain : State → List (Snapshot × Snapshot) → State → Prop where
  | nil : Chain s [] s
  | next : Transition s n next → next.snapshot = i → Chain next rest final →
      Chain s ((n, i) :: rest) final

theorem Chain.remaining_le (h : Chain s steps final) : final.remaining ≤ s.remaining := by
  induction h with
  | nil => exact Nat.le_refl _
  | next ht _ _ ih =>
      obtain ⟨q, a, _, _, _, _, hc, _, _⟩ := ht.observation
      exact Nat.le_trans ih (by rw [hc]; exact Nat.sub_le _ _)

def seed (snapshot : Snapshot) :
    Option {s : State // s.snapshot = snapshot ∧ s.remaining = workLimit ∧ Principal s.term s.formula} := do
  if !LinearNormal.bounded snapshot then none else do
    match ht : decode snapshot.graph snapshot.termRoot, hA : decode snapshot.graph snapshot.typeRoot with
    | some t, some A => do
      let p ← CorePrincipal.infer 0 t
      if he : p.val.encode = A then
        pure ⟨⟨snapshot, t, p.val, workLimit, ht, by simpa only [he] using hA,
          .base p.property.derives⟩, rfl, rfl, p.property⟩
      else none
    | _, _ => none

def advance (before : State) (normalized inferred : Snapshot) :
    Option {after : State // Transition before normalized after ∧ after.snapshot = inferred} := do
  if hn : normalized.graph = before.snapshot.graph then do
    if hi : inferred.graph = before.snapshot.graph then do
      if hr : normalized.termRoot = before.snapshot.termRoot then do
        if !(LinearNormal.bounded normalized && LinearNormal.bounded inferred) then none else do
          match hnode : inferred.graph[inferred.termRoot]? with
          | some (.app fRoot aRoot) => do
            if hroot : fRoot = before.snapshot.termRoot then do
              match hN : decode normalized.graph normalized.typeRoot,
                  ht : decode inferred.graph inferred.termRoot,
                  hI : decode inferred.graph inferred.typeRoot with
              | some N, some (.app f a), some I => do
                if hf : f = before.term then do
                  let normal ← parseFormula 0 N
                  let hc ← conversion before.formula normal.val
                  match hq : normal.val with
                  | .all q => do
                    let argument ← extract 0 a
                    if hs : FirstOrderApplication.substitutionSafe q.encode a = true then do
                      if hb : charge q.encode a ≤ before.remaining then do
                        let result := q.instantiate argument.val
                        if he : result.encode = I then do
                          have converted : Applied before.term (.all q) := .convert before.evidence
                            (by simpa only [hq] using hc.down)
                          let after : State := ⟨inferred, .app before.term argument.val.encode, result,
                            before.remaining - charge q.encode a,
                            by simpa only [hf, argument.property] using ht,
                            by simpa only [he] using hI, .app converted argument.val⟩
                          pure ⟨after, ⟨hn, hi, hr,
                            ⟨aRoot, by simpa only [hroot] using hnode⟩,
                            q, argument.val, by simpa only [← normal.property, hq] using hN,
                            by simpa only [hq] using hc.down, rfl, rfl,
                            by simp only [after, argument.property],
                            by simpa only [argument.property] using hb,
                            by simpa only [argument.property] using hs⟩, rfl⟩
                        else none
                      else none
                    else none
                  | _ => none
                else none
              | _, _, _ => none
            else none
          | _ => none
      else none
    else none
  else none

def run (s : State) : (steps : List (Snapshot × Snapshot)) → Option {final : State // Chain s steps final}
  | [] => some ⟨s, .nil⟩
  | (normalized, inferred) :: rest => do
      let next ← advance s normalized inferred
      let final ← run next.val rest
      pure ⟨final.val, .next next.property.1 next.property.2 final.property⟩

structure Trace where
  initial : Snapshot
  steps : List (Snapshot × Snapshot)
  requested : Snapshot
  deriving DecidableEq, Repr

structure Roots where
  initialTerm : Nat
  initialType : Nat
  finalTerm : Nat
  finalInferredType : Nat
  requestedType : Nat
  deriving DecidableEq, Repr

def Sound (c : Trace) (roots : Roots) : Prop :=
  0 < c.steps.length ∧ c.steps.length ≤ linkLimit ∧
  c.initial.termRoot = roots.initialTerm ∧ c.initial.typeRoot = roots.initialType ∧
  c.requested.termRoot = roots.finalTerm ∧ c.requested.typeRoot = roots.requestedType ∧
  ∃ initial final : State, ∃ q : Formula 0,
    initial.snapshot = c.initial ∧ initial.remaining = workLimit ∧ Principal initial.term initial.formula ∧
    Chain initial c.steps final ∧ final.snapshot.termRoot = roots.finalTerm ∧
    final.snapshot.typeRoot = roots.finalInferredType ∧
    c.requested.graph = final.snapshot.graph ∧
    decode c.requested.graph c.requested.typeRoot = some q.encode ∧
    Converts final.formula q ∧ Applied final.term q ∧ (∀ ρ, q.Holds ρ)

def check (c : Trace) (roots : Roots) : Option (PLift (Sound c roots)) := do
  if hl : 0 < c.steps.length ∧ c.steps.length ≤ linkLimit then do
    if hstart : c.initial.termRoot = roots.initialTerm ∧ c.initial.typeRoot = roots.initialType then do
      if hend : c.requested.termRoot = roots.finalTerm ∧ c.requested.typeRoot = roots.requestedType then do
        if !LinearNormal.bounded c.requested then none else do
          let initial ← seed c.initial
          let final ← run initial.val c.steps
          if hf : final.val.snapshot.termRoot = roots.finalTerm ∧
              final.val.snapshot.typeRoot = roots.finalInferredType then do
            if hg : c.requested.graph = final.val.snapshot.graph then do
              match hA : decode c.requested.graph c.requested.typeRoot with
              | some A => do
                let q ← parseFormula 0 A
                let hc ← conversion final.val.formula q.val
                have hproof : Applied final.val.term q.val := .convert final.val.evidence hc.down
                pure ⟨hl.1, hl.2, hstart.1, hstart.2, hend.1, hend.2,
                  initial.val, final.val, q.val, initial.property.1, initial.property.2.1,
                  initial.property.2.2, final.property, hf.1, hf.2, hg,
                  by simpa only [q.property] using hA, hc.down, hproof, hproof.sound⟩
              | none => none
            else none
          else none
      else none
    else none
  else none

def validate (c : Trace) (roots : Roots) : Bool := (check c roots).isSome

theorem validate_sound (h : validate c roots = true) : Sound c roots := by
  unfold validate at h
  cases hc : check c roots with
  | none => simp [hc] at h
  | some p => exact p.down

def decodeSteps : (bytes : List (ByteArray × ByteArray)) →
    Option {steps : List (Snapshot × Snapshot) //
      steps.map (fun (n, i) => (encodeSnapshot n, encodeSnapshot i)) = bytes}
  | [] => some ⟨[], rfl⟩
  | (nb, ib) :: rest => do
      match hn : decodeSnapshot nb, hi : decodeSnapshot ib with
      | some n, some i => do
          let tail ← decodeSteps rest
          pure ⟨(n, i) :: tail.val, by
            simp only [List.map_cons, decodeSnapshot_exact hn, decodeSnapshot_exact hi, tail.property]⟩
      | _, _ => none

def validateBytes (initial : ByteArray) (steps : List (ByteArray × ByteArray))
    (requested : ByteArray) (roots : Roots) : Bool :=
  if steps.length > linkLimit then false else
    match decodeSnapshot initial, decodeSteps steps, decodeSnapshot requested with
    | some s, some pairs, some r => validate ⟨s, pairs.val, r⟩ roots
    | _, _, _ => false

theorem validateBytes_sound (h : validateBytes initial steps requested roots = true) :
    ∃ c, encodeSnapshot c.initial = initial ∧
      c.steps.map (fun (n, i) => (encodeSnapshot n, encodeSnapshot i)) = steps ∧
      encodeSnapshot c.requested = requested ∧ Sound c roots := by
  unfold validateBytes at h
  split at h
  · contradiction
  · cases hs : decodeSnapshot initial <;> cases hp : decodeSteps steps <;>
      cases hr : decodeSnapshot requested <;>
      simp only [hs, hp, hr, Bool.false_eq_true] at h
    case some.some.some s pairs r =>
      exact ⟨⟨s, pairs.val, r⟩, decodeSnapshot_exact hs, pairs.property,
        decodeSnapshot_exact hr, validate_sound h⟩

end Jihoo.GraphCertificates.ApplicationSpine
