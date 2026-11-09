import Jihoo.MixedInference
import Jihoo.GraphCertificates
import Jihoo.TypingCertificateCodec

/-! Restricted Raw admission by candidate reconstruction, exact round trip and
proved inference. No candidate decoder correctness is assumed. -/
namespace Jihoo.CoreBridge.Checked.Admission
open GraphCertificates

/-- Recover an index in one of the two source namespaces. -/
def position (kind : BinderKind) (slot : Nat) : Layout → Option Nat
  | [] => none
  | k :: ks =>
      match slot with
      | 0 => if k = kind then some 0 else none
      | j + 1 => (position kind j ks).map (fun x => if k = kind then x + 1 else x)

def indexCandidate : Nat → Layout → Raw → Option Index
  | 0, _, _ => none
  | fuel + 1, layout, r =>
      match r with
      | .var x => (position .index x layout).map Index.var
      | .natural n => (word? n).map Index.lit
      | .uadd a b => do return .add (← indexCandidate fuel layout a) (← indexCandidate fuel layout b)
      | _ => none

def typeCandidate : Nat → Layout → Raw → Option Ty
  | 0, _, _ => none
  | fuel + 1, layout, r =>
      match r with
      | .u64 => some .u64
      | .i64 => some .i64
      | .array a => (indexCandidate fuel layout a).map Ty.array
      | .lt a b => do return .lt (← indexCandidate fuel layout a) (← indexCandidate fuel layout b)
      | .eq a b => do return .eq (← indexCandidate fuel layout a) (← indexCandidate fuel layout b)
      | .pi false .u64 B => (typeCandidate fuel (.index :: layout) B).map Ty.pi
      | _ => none

def signed? (n : Int) : Option Signed :=
  if h : -signedBound ≤ n ∧ n < signedBound then some ⟨n, h⟩ else none

/-- Atomic application arguments ensure source inference's index substitutions
do not expand index trees. Other arithmetic remains available inside types. -/
def atomic (r : Raw) : Bool := match r with
  | .var _ | .natural _ => true
  | _ => false

def termCandidate : Nat → Layout → Raw → Option Term
  | 0, _, _ => none
  | fuel + 1, layout, r =>
      match r with
      | .var x =>
          match position .value x layout with
          | some x => some (.var x)
          | none => (indexCandidate fuel layout r).map Term.natural
      | .natural _ | .uadd _ _ => (indexCandidate fuel layout r).map Term.natural
      | .integer n => (signed? n).map Term.integer
      | .elements xs => do
          let xs ← xs.mapM fun r => match r with
            | .integer n => signed? n
            | _ => none
          return .elements xs
      | .refl a => (indexCandidate fuel layout a).map Term.refl
      | .decide (.natural a) (.natural b) => do
          let a ← word? a
          let b ← word? b
          if h : a.val < b.val then some (.decide a b h) else none
      | .index a i p => do
          return .index (← termCandidate fuel layout a)
            (← indexCandidate fuel layout i) (← termCandidate fuel layout p)
      | .app (.lam false .u64 body) a => if atomic a then do
          return .app (.lam (← termCandidate fuel (.index :: layout) body))
            (← indexCandidate fuel layout a)
          else none
      | .lam false .u64 body => (termCandidate fuel (.index :: layout) body).map Term.lam
      | .app (.lam erased A body) v => do
          let A ← typeCandidate fuel layout A
          if erased != A.proposition then none else do
            let v ← termCandidate fuel layout v
            let body ← termCandidate fuel (.value :: layout) body
            return .letValue A v body
      | .app f a => if atomic a then do
          return .app (← termCandidate fuel layout f) (← indexCandidate fuel layout a)
          else none
      | _ => none

/-- Saturating tree-work guard before reconstruction, inference or equality.
Numeric payload magnitude does not contribute to this structural size. -/
def cost : Nat → Raw → Nat
  | 0, _ => 513
  | fuel + 1, r =>
      let one := fun a => min 513 (1 + cost fuel a)
      let two := fun a b => min 513 (1 + cost fuel a + cost fuel b)
      let three := fun a b c => min 513 (1 + cost fuel a + cost fuel b + cost fuel c)
      match r with
      | .array a | .refl a | .zeroLe a => one a
      | .lt a b | .eq a b | .app a b | .decide a b | .uadd a b
      | .lam _ a b | .pi _ a b => two a b
      | .index a b c | .usub a b c => three a b c
      | .elements xs => if xs.length > 512 then 513 else
          xs.foldl (fun total a => min 513 (total + cost fuel a)) 1
      | _ => 1

/-- Successful admission retains the exact original term and type trees. -/
structure Accepted (r R : Raw) where
  term : Term
  type : Ty
  typed : SourceTyping 0 [] term type
  term_exact : term.encode id id = r
  type_exact : type.encode id = R

def admit (r R : Raw) : Option (Accepted r R) := do
  if cost 33 r > 512 || cost 33 R > 512 then none else do
   let t ← termCandidate 32 [] r
   let ⟨A, ht⟩ ← infer 0 [] t
   if hr : rawEqual (t.encode id id) r = true then
     if hR : rawEqual (A.encode id) R = true then
       some ⟨t, A, ht, (rawEqual_iff _ _).mp hr, (rawEqual_iff _ _).mp hR⟩
     else none
   else none

theorem Accepted.raw_typed (a : Accepted r R) : Raw.HasType (fun _ => none) r R := by
  have h := a.typed.translate_closed
  simpa only [a.term_exact, a.type_exact] using h

theorem Accepted.type_formed (a : Accepted r R) : Raw.IsType (fun _ => none) R := by
  have h := a.typed.closed_type_formed
  simpa only [a.type_exact] using h

theorem Accepted.realizes (a : Accepted r R) (ρ : Arithmetic.Env) :
    Nonempty (a.type.erase.denote ρ) := a.typed.erases.realize ρ (Indexed.empty_valuation ρ)

/-- Input graph/root identity is retained in the theorem's parameters. All graph
nodes, including unreachable ones, pass the existing bounded graph decoder. -/
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
    Represents s.graph s.termRoot a.rawTerm ∧
    Represents s.graph s.typeRoot a.rawType ∧ Raw.HasType (fun _ => none) a.rawTerm a.rawType :=
  ⟨decode_sound a.term_decoded, decode_sound a.type_decoded, a.accepted.raw_typed⟩

end Jihoo.CoreBridge.Checked.Admission
