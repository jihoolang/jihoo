import Jihoo.MixedProofInference
import Jihoo.MixedRawAdmission

/-! Exact snapshot admission for mixed natural/proof functions. Successful
independent admission, not arbitrary Core acceptance, supplies semantic evidence. -/
namespace Jihoo.MixedProofFunctions.Checked.Snapshot
open CoreBridge (Raw Layout)
open GraphCertificates
open Bridge

def indexCandidate (fuel : Nat) (layout : Layout) (r : Raw) : Option Arithmetic.Expr :=
  (CoreBridge.Checked.Admission.indexCandidate fuel layout r).map CoreBridge.Index.erase

def formulaCandidate : Nat → Layout → Raw → Option Formula
  | 0, _, _ => none
  | fuel + 1, layout, r => match r with
    | .eq a b => do return .eq (← indexCandidate fuel layout a) (← indexCandidate fuel layout b)
    | .lt a b => do return .lt (← indexCandidate fuel layout a) (← indexCandidate fuel layout b)
    | .pi false .u64 B => (formulaCandidate fuel (.index :: layout) B).map Formula.all
    | .pi true A B => do
        return .arrow (← formulaCandidate fuel layout A)
          (← formulaCandidate fuel (.value :: layout) B)
    | _ => none

def termCandidate : Nat → Layout → Raw → Option Term
  | 0, _, _ => none
  | fuel + 1, layout, r => match r with
    | .var x => (CoreBridge.Checked.Admission.position .value x layout).map Term.hyp
    | .refl a => (indexCandidate fuel layout a).map Term.refl
    | .zeroLe a => (indexCandidate fuel layout a).map Term.zeroLe
    | .decide (.natural m) (.natural n) => some (.decide m n)
    | .lam false .u64 body => (termCandidate fuel (.index :: layout) body).map Term.naturalLam
    | .lam true A body => do
        return .proofLam (← formulaCandidate fuel layout A)
          (← termCandidate fuel (.value :: layout) body)
    | .app f a => do
        let f ← termCandidate fuel layout f
        match indexCandidate fuel layout a with
        | some a' => if CoreBridge.Checked.Admission.atomic a then some (.naturalApp f a') else none
        | none => return .proofApp f (← termCandidate fuel layout a)
    | _ => none

structure Accepted (r R : Raw) where
  value : Term
  type : Formula
  typed : Derives 0 [] value type
  admitted : TermAdmitted value
  type_admitted : FormulaAdmitted type
  type_decoded : formulaCandidate 32 [] R = some type
  term_exact : term id id value = r
  type_exact : formula id type = R

/-- Parse the input type as well as inferring it, and compare exact syntax.
This fixes the semantic interpretation to the supplied type tree. -/
def admit (r R : Raw) : Option (Accepted r R) := do
  if CoreBridge.Checked.Admission.cost 33 r > 512 || CoreBridge.Checked.Admission.cost 33 R > 512 then none else do
    let t ← termCandidate 32 [] r
    match hd : formulaCandidate 32 [] R with
    | none => none
    | some P => do
      let ⟨A, ht⟩ ← infer 0 [] t
      if he : A = P then
        if ha : TermAdmitted t then
          if hP : FormulaAdmitted P then
            if hr : rawEqual (term id id t) r = true then
              if hR : rawEqual (formula id P) R = true then
                some ⟨t, P, he ▸ ht, ha, hP, hd,
                  (rawEqual_iff _ _).mp hr, (rawEqual_iff _ _).mp hR⟩
              else none
            else none
          else none
        else none
      else none

theorem Accepted.raw_typed (a : Accepted r R) : Raw.Beta.HasType (fun _ => none) r R := by
  have h := translate_closed a.typed a.admitted
  simpa only [a.term_exact, a.type_exact] using h

theorem Accepted.type_formed (a : Accepted r R) : Raw.Beta.IsType (fun _ => none) R := by
  have h := formula_formed a.type a.typed.scoped a.type_admitted
    (ix := id) (Δ := fun _ => none) (by intro x hx; omega)
  simpa only [a.type_exact] using h

theorem Accepted.truth (a : Accepted r R) (ρ : Arithmetic.Env) : a.type.Holds ρ :=
  a.typed.sound (by intro x P hx; simp at hx)

/-- Truth of the uniquely parsed INPUT proposition, not merely a producer's
claimed type or a beta-convertible alternative. -/
theorem Accepted.parsed_truth (a : Accepted r R)
    (hp : formulaCandidate 32 [] R = some P) (ρ : Arithmetic.Env) : P.Holds ρ := by
  have same : a.type = P := Option.some.inj (a.type_decoded.symm.trans hp)
  exact same ▸ a.truth ρ

structure GraphAccepted (s : Typing.Wire.Snapshot) where
  rawTerm : Raw
  rawType : Raw
  term_decoded : decode s.graph s.termRoot = some rawTerm
  type_decoded : decode s.graph s.typeRoot = some rawType
  accepted : Accepted rawTerm rawType

def admitSnapshot (s : Typing.Wire.Snapshot) : Option (GraphAccepted s) :=
  match hr : decode s.graph s.termRoot with
  | none => none
  | some r => match hR : decode s.graph s.typeRoot with
    | none => none
    | some R => do
        let a ← admit r R
        return ⟨r, R, hr, hR, a⟩

theorem GraphAccepted.sound (a : GraphAccepted s) :
    Represents s.graph s.termRoot a.rawTerm ∧ Represents s.graph s.typeRoot a.rawType ∧
      Raw.Beta.HasType (fun _ => none) a.rawTerm a.rawType ∧
      Raw.Beta.IsType (fun _ => none) a.rawType :=
  ⟨decode_sound a.term_decoded, decode_sound a.type_decoded,
    a.accepted.raw_typed, a.accepted.type_formed⟩

theorem GraphAccepted.input_truth (a : GraphAccepted s)
    (hd : decode s.graph s.typeRoot = some R)
    (hp : formulaCandidate 32 [] R = some P) (ρ : Arithmetic.Env) : P.Holds ρ := by
  have same : a.rawType = R := Option.some.inj (a.type_decoded.symm.trans hd)
  apply a.accepted.parsed_truth (ρ := ρ)
  simpa only [same] using hp

theorem false_bound_excluded (hk : k < CoreBridge.wordBound) :
    ¬ Nonempty (Accepted r (.lt (.natural k) (.natural k))) := by
  rintro ⟨a⟩
  have hp : formulaCandidate 32 [] (.lt (.natural k) (.natural k)) =
      some (.lt (.lit k) (.lit k)) := by
    simp [formulaCandidate, indexCandidate, CoreBridge.Checked.Admission.indexCandidate, CoreBridge.word?, hk,
      CoreBridge.Index.erase]
  exact Nat.lt_irrefl k (a.parsed_truth hp (fun _ => 0))

theorem false_equality_excluded (hm : m < CoreBridge.wordBound) (hn : n < CoreBridge.wordBound)
    (hne : m ≠ n) : ¬ Nonempty (Accepted r (.eq (.natural m) (.natural n))) := by
  rintro ⟨a⟩
  have hp : formulaCandidate 32 [] (.eq (.natural m) (.natural n)) =
      some (.eq (.lit m) (.lit n)) := by
    simp [formulaCandidate, indexCandidate, CoreBridge.Checked.Admission.indexCandidate, CoreBridge.word?, hm, hn,
      CoreBridge.Index.erase]
  exact hne (a.parsed_truth hp (fun _ => 0))

end Jihoo.MixedProofFunctions.Checked.Snapshot
