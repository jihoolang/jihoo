import Jihoo.NativeACUForwardConfluence
import Jihoo.NativeSchema
import Init.Data.List.Sort.Lemmas

/-! Compact full-Term ACU canonicalization. Every non-additive tree is an atom,
including arbitrary applications, dependent types, proof fields and malformed
nodes. Only valid U64 leaves contribute to the collected constant. Executable
code never constructs a unary literal replica list. -/
namespace Jihoo.NativeKernel.ACU.Canonical

open Conversion (ListRel)
open AffineSum (wordLimit naturalSum)

/-- Source Core.compare rank, kept separate from native serialization tags. -/
def rank : Op → Nat
  | .global _ => 1 | .universe _ => 2 | .prop => 3 | .u64 => 4 | .i64 => 5
  | .array => 6 | .lt => 7 | .eq => 8 | .refl => 9 | .transport => 10
  | .ind _ _ => 11 | .con _ _ _ => 12 | .elim _ _ => 13 | .arith _ => 14
  | .fold => 15 | .strict => 16 | .uadd => 17 | .ltAdd => 18 | .ltCancel => 19
  | .ltLe => 20 | .usub => 21 | .zeroLe => 22 | .refine => 23 | .pack => 24
  | .witness => 25 | .proof => 26 | .buffer => 27 | .alloc => 28 | .load => 29
  | .store => 30 | .free => 31 | .caseOf _ _ => 32 | .pi _ => 33 | .lam _ => 34
  | .app => 35 | .natural _ => 36 | .integer _ => 37 | .elements _ => 38
  | .index => 39 | .decide => 40 | .ifLt => 41 | .ifEq => 42 | .drop _ => 43
  | .ref => 44 | .lend => 45 | .view _ _ _ => 46 | .borrow => 47 | .deref => 48
  | .absurd => 49 | .loop => 50 | .back _ => 51 | .give _ => 52 | .take => 53

private def flag : Bool → Int | false => 0 | true => 1

/-- Core's scalar payload order, before child comparison. Complete native
payloads remain a final tie-breaker for malformed vector-length metadata. -/
def payload : Op → List Int
  | .global n | .universe n | .ind n _ | .elim n _ | .caseOf n _ | .drop n => [n]
  | .natural n => [n]
  | .integer n => [n]
  | .con f k _ => [f,k]
  | .arith .add => [0] | .arith .sub => [1] | .arith .mul => [2]
  | .pi e | .lam e | .back e | .give e => [flag e]
  | .view r f _ => [flag r,f]
  | _ => []

private def compareInts : List Int → List Int → Ordering
  | [],[] => .eq | [],_::_ => .lt | _::_,[] => .gt
  | a::as,b::bs => match compare a b with | .eq => compareInts as bs | o => o

mutual
  /-- Structural order retains every child, including evidence omitted by
  Core.conversion_children. Strict nodes also retain both of their children. -/
  def compareTerm : Term → Term → Ordering
    | .var x,.var y => compare x y
    | .var _,.node _ _ => .lt
    | .node _ _,.var _ => .gt
    | .node op xs,.node op' ys =>
        match compare (rank op) (rank op') with
        | .lt => .lt | .gt => .gt
        | .eq => match compareInts (payload op) (payload op') with
          | .lt => .lt | .gt => .gt
          | .eq => match compareArgs xs ys with
            | .lt => .lt | .gt => .gt
            | .eq => compareInts ((NativeSchema.payload op).map Int.ofNat)
                ((NativeSchema.payload op').map Int.ofNat)
  termination_by a _ => sizeOf a
  decreasing_by all_goals simp_wf; all_goals omega

  def compareArgs : List Term → List Term → Ordering
    | [],[] => .eq | [],_::_ => .lt | _::_,[] => .gt
    | a::as,b::bs => match compareTerm a b with | .eq => compareArgs as bs | o => o
  termination_by xs _ => sizeOf xs
  decreasing_by all_goals simp_wf; all_goals omega
end

/-- Stable deterministic merge sort of all native atoms, not only variables. -/
def sortAtoms (xs : List Term) : List Term := xs.mergeSort (fun a b => (compareTerm a b).isLE)

theorem sortAtoms_perm (xs : List Term) : (sortAtoms xs).Perm xs := List.mergeSort_perm _ _

structure Pieces where
  atoms : List Term
  constant : Nat
  deriving Repr

def Pieces.append (a b : Pieces) : Pieces := ⟨a.atoms ++ b.atoms,a.constant+b.constant⟩

/-- Invalid oversized payloads stay opaque atoms, never interpreted as a
balanced mathematical sum. Collection traverses binary UAdd only. -/
def collect : Term → Pieces
  | .node .uadd [a,b] => (collect a).append (collect b)
  | .node (.natural n) [] => if n < wordLimit then ⟨[],n⟩ else ⟨[.node (.natural n) []],0⟩
  | t => ⟨[t],0⟩
termination_by t => sizeOf t
decreasing_by all_goals simp_wf; all_goals omega

/-- Balanced valid-U64 leaves; no literal-width-sized loop or allocation. -/
def constantTree (n : Nat) : Term := (naturalSum n).toTerm

/-- Source Core.canonical folds its sorted atoms from the left. -/
def atomTree (first : Term) (rest : List Term) : Term := rest.foldl (fun a b => .node .uadd [a,b]) first

def Pieces.emit (f : Pieces) : Term :=
  match sortAtoms f.atoms with
  | [] => constantTree f.constant
  | x::xs => if f.constant = 0 then atomTree x xs else .node .uadd [atomTree x xs,constantTree f.constant]

def sum (t : Term) : Term := (collect t).emit

/-- A proof-only linear presentation. It is never called by canonicalization. -/
private def linear (p : Pieces) : Term := sumTerms (p.atoms ++ List.replicate p.constant (.node (.natural 1) []))

private theorem shuffle (as bs cs ds : List Term) :
    ((as ++ bs) ++ (cs ++ ds)).Perm ((as ++ cs) ++ (bs ++ ds)) := by
  simpa only [List.append_assoc] using
    ((List.perm_append_comm (l₁ := bs) (l₂ := cs)).append_right ds).append_left as

/-- Constructive arithmetic derivation for complete native atoms. The proof
uses symbolic replicas, while the executable collector stores one Nat. -/
theorem collect_sound (t : Term) : Arithmetic t (linear (collect t)) := by
  fun_induction collect t with
  | case1 a b ia ib =>
      apply (Arithmetic.addCong ia ib).trans
      apply (Arithmetic.sumTerms_append _ _).trans
      apply Arithmetic.sumTerms_perm
      simpa only [linear,Pieces.append,List.replicate_append_replicate] using
        shuffle (collect a).atoms (List.replicate (collect a).constant (.node (.natural 1) []))
          (collect b).atoms (List.replicate (collect b).constant (.node (.natural 1) []))
  | case2 n bound => exact Arithmetic.literal_ones n bound
  | case3 n bound => exact (Arithmetic.zero _).symm
  | case4 t h₁ h₂ => exact (Arithmetic.zero t).symm

private theorem naturalSum_variables (n : Nat) : (naturalSum n).variables = [] := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      rw [naturalSum]
      split
      · rfl
      · rename_i large
        have low : 2 ≤ wordLimit := by decide
        simp only [AffineSum.Expr.variables,ih (n/2) (by omega),ih (n-n/2) (by omega),List.nil_append]

private theorem naturalSum_constant (n : Nat) : (naturalSum n).constant = n := by
  have eval := (AffineSum.naturalSum_spec n).1 (fun _ => 0)
  rw [AffineSum.Expr.eval_collect,naturalSum_variables] at eval
  simpa only [List.map_nil,List.sum_nil,Nat.zero_add] using eval

theorem constantTree_valid (n : Nat) : (naturalSum n).Valid := (AffineSum.naturalSum_spec n).2

theorem constantTree_sound (n : Nat) :
    Arithmetic (constantTree n) (sumTerms (List.replicate n (.node (.natural 1) []))) := by
  have collected := Arithmetic.affine_collect (naturalSum n) (constantTree_valid n)
  simpa only [constantTree,naturalSum_variables,naturalSum_constant,List.map_nil,List.nil_append] using collected

private theorem atomTree_sound (first : Term) (rest : List Term) :
    Arithmetic (atomTree first rest) (sumTerms (first::rest)) := by
  induction rest generalizing first with
  | nil => exact (Arithmetic.zero first).symm
  | cons x xs ih => exact (ih (.node .uadd [first,x])).trans (Arithmetic.assoc first x (sumTerms xs))

private theorem emit_linear (p : Pieces) :
    Arithmetic p.emit (sumTerms (sortAtoms p.atoms ++ List.replicate p.constant (.node (.natural 1) []))) := by
  cases h : sortAtoms p.atoms with
  | nil => simpa only [Pieces.emit,h,List.nil_append] using constantTree_sound p.constant
  | cons x xs =>
      by_cases zero : p.constant = 0
      · simpa only [Pieces.emit,h,zero,↓reduceIte,List.replicate_zero,List.append_nil] using atomTree_sound x xs
      · simpa only [Pieces.emit,h,zero,↓reduceIte] using
          (Arithmetic.addCong (atomTree_sound x xs) (constantTree_sound p.constant)).trans
            (Arithmetic.sumTerms_append _ _)

/-- Actual full native ACU conversion soundness of compact additive sorting. -/
theorem sum_arithmetic (t : Term) : Arithmetic t (sum t) := by
  apply (collect_sound t).trans
  apply (Arithmetic.sumTerms_perm (((sortAtoms_perm (collect t).atoms).symm).append_right _)).trans
  exact (emit_linear (collect t)).symm

theorem sum_sound (t : Term) : Conv t (sum t) := (sum_arithmetic t).toConv

/-- Equality after additive canonicalization is sound on arbitrary full native
terms. Proof slots are compared structurally; no raw irrelevance is assumed. -/
def equal (a b : Term) : Bool := (sum a).equal (sum b)

theorem equal_sound (h : equal a b = true) : Conv a b := by
  have same : sum a = sum b := (Term.equal_iff _ _).mp h
  exact (sum_sound a).trans (same ▸ (sum_sound b).symm)

end Jihoo.NativeKernel.ACU.Canonical
