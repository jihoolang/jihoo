import Jihoo.TypingCertificateCodec
import Jihoo.CoreBridgeBetaPreservation

/-! Single requested contextual beta contraction, with independently bound input
and output snapshots. No output typing premise, source acceptance premise, or
normalizer equivalence is used. IO/importer fidelity remains outside this model. -/
namespace Jihoo.GraphCertificates.TypedBeta
open CoreBridge CoreBridge.Raw
open Typing.Wire

/-- Zero-based constructor child indices; binder flags are not children.
The empty path requests exactly one head contraction, never normalization. -/
def contract : (path : List Nat) → (t : Raw) → Option {u : Raw // Raw.Beta.Step t u}
  | [], .app (.lam e A body) a =>
      if Typing.substitutionSafe body a then
        some ⟨body.subst (single a), .beta e A body a⟩ else none
  | [], _ => none
  | 0 :: path, .array a => do
      let u ← contract path a
      pure ⟨.array u.val, .array u.property⟩
  | 0 :: path, .lt a b => do
      let u ← contract path a
      pure ⟨.lt u.val b, .ltLeft u.property⟩
  | 1 :: path, .lt a b => do
      let u ← contract path b
      pure ⟨.lt a u.val, .ltRight u.property⟩
  | 0 :: path, .eq a b => do
      let u ← contract path a
      pure ⟨.eq u.val b, .eqLeft u.property⟩
  | 1 :: path, .eq a b => do
      let u ← contract path b
      pure ⟨.eq a u.val, .eqRight u.property⟩
  | 0 :: path, .pi e A B => do
      let u ← contract path A
      pure ⟨.pi e u.val B, .piDomain u.property⟩
  | 1 :: path, .pi e A B => do
      let u ← contract path B
      pure ⟨.pi e A u.val, .piCodomain u.property⟩
  | 0 :: path, .lam e A b => do
      let u ← contract path A
      pure ⟨.lam e u.val b, .lamDomain u.property⟩
  | 1 :: path, .lam e A b => do
      let u ← contract path b
      pure ⟨.lam e A u.val, .lamBody u.property⟩
  | 0 :: path, .app f a => do
      let u ← contract path f
      pure ⟨.app u.val a, .appFunction u.property⟩
  | 1 :: path, .app f a => do
      let u ← contract path a
      pure ⟨.app f u.val, .appArgument u.property⟩
  | 0 :: path, .index a i p => do
      let u ← contract path a
      pure ⟨.index u.val i p, .indexArray u.property⟩
  | 1 :: path, .index a i p => do
      let u ← contract path i
      pure ⟨.index a u.val p, .indexIndex u.property⟩
  | 2 :: path, .index a i p => do
      let u ← contract path p
      pure ⟨.index a i u.val, .indexProof u.property⟩
  | 0 :: path, .refl a => do
      let u ← contract path a
      pure ⟨.refl u.val, .reflTerm u.property⟩
  | 0 :: path, .zeroLe a => do
      let u ← contract path a
      pure ⟨.zeroLe u.val, .zeroLe u.property⟩
  | 0 :: path, .decide a b => do
      let u ← contract path a
      pure ⟨.decide u.val b, .decideLeft u.property⟩
  | 1 :: path, .decide a b => do
      let u ← contract path b
      pure ⟨.decide a u.val, .decideRight u.property⟩
  | 0 :: path, .uadd a b => do
      let u ← contract path a
      pure ⟨.uadd u.val b, .uaddLeft u.property⟩
  | 1 :: path, .uadd a b => do
      let u ← contract path b
      pure ⟨.uadd a u.val, .uaddRight u.property⟩
  | 0 :: path, .usub a b p => do
      let u ← contract path a
      pure ⟨.usub u.val b p, .usubLeft u.property⟩
  | 1 :: path, .usub a b p => do
      let u ← contract path b
      pure ⟨.usub a u.val p, .usubRight u.property⟩
  | 2 :: path, .usub a b p => do
      let u ← contract path p
      pure ⟨.usub a b u.val, .usubProof u.property⟩
  | i :: path, .elements xs => do
      match h : xs.drop i with
      | [] => none
      | a :: post =>
          let u ← contract path a
          have he : xs = xs.take i ++ a :: post := by
            rw [← h, List.take_append_drop]
          pure ⟨.elements (xs.take i ++ u.val :: post),
            by simpa only [← he] using (Raw.Beta.Step.elements (xs.take i) post u.property)⟩
  | _ :: _, _ => none

structure Certificate where
  before : Snapshot
  after : Snapshot
  path : List Nat
  deriving DecidableEq, Repr

/-- Literal snapshot equality includes unreachable nodes and both root IDs. -/
def Matches (before after : Snapshot) (requested : List Nat) (c : Certificate) : Prop :=
  c.before = before ∧ c.after = after ∧ c.path = requested

instance (before after : Snapshot) (requested : List Nat) (c : Certificate) :
    Decidable (Matches before after requested c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The original type root ID is retained and must still decode to the exact
original type. A different but convertible output type is not the interface. -/
def Sound (before after : Snapshot) (requested : List Nat) : Prop :=
  before.typeRoot = after.typeRoot ∧
  ∃ t u A, decode before.graph before.termRoot = some t ∧
    decode before.graph before.typeRoot = some A ∧
    decode after.graph after.termRoot = some u ∧
    decode after.graph after.typeRoot = some A ∧
    (∃ result, contract requested t = some result ∧ result.val = u) ∧
    Raw.Beta.Step t u ∧ Raw.Beta.HasType (fun _ => none) t A ∧
    Raw.Beta.HasType (fun _ => none) u A ∧ Raw.Beta.IsType (fun _ => none) A

/-- Fixed number of decoded endpoints; graph measurement counts repeated DAG
edges before unfolding. No chains or producer-chosen extra roots are expanded. -/
def check (before after : Snapshot) (typing : Typing.Certificate)
    (requested : List Nat) (c : Certificate) :
    Option (PLift (Matches before after requested c ∧ Sound before after requested)) := do
  if hm : Matches before after requested c then do
    if requested.length > depthLimit then none else do
      if ht : before.typeRoot = after.typeRoot then do
        if hb : Typing.Wire.validateAgainst before typing = true then do
          match hi : decode before.graph before.termRoot,
              ha : decode before.graph before.typeRoot,
              ho : decode after.graph after.termRoot,
              hz : decode after.graph after.typeRoot with
          | some t, some A, some u, some B => do
              if he : A = B then do
                match hc : contract requested t with
                | none => none
                | some result => do
                    if hu : result.val = u then do
                      have hs : Raw.Beta.HasType (fun _ => none) t A ∧
                          Raw.Beta.IsType (fun _ => none) A := by
                        obtain ⟨t', A', hi', ha', typed, formed⟩ :=
                          (Typing.Wire.validateAgainst_sound hb).2
                        rw [hi] at hi'; cases hi'
                        rw [ha] at ha'; cases ha'
                        exact ⟨typed, formed⟩
                      have step : Raw.Beta.Step t u := hu ▸ result.property
                      pure ⟨⟨hm, ht, t, u, A, hi, ha, ho, by simpa only [he] using hz,
                        ⟨result, hc, hu⟩, step, hs.1, hs.1.preservation step, hs.2⟩⟩
                    else none
              else none
          | _, _, _, _ => none
        else none
      else none
  else none

def validate (before after : Snapshot) (typing : Typing.Certificate)
    (requested : List Nat) (c : Certificate) : Bool :=
  (check before after typing requested c).isSome

theorem validate_sound {before after : Snapshot} {typing : Typing.Certificate}
    {requested : List Nat} {c : Certificate}
    (h : validate before after typing requested c = true) :
    Matches before after requested c ∧ Sound before after requested := by
  unfold validate at h
  cases hc : check before after typing requested c with
  | none => simp [hc] at h
  | some proof => exact proof.down

end Jihoo.GraphCertificates.TypedBeta
