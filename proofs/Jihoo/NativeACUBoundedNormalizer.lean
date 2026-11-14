import Jihoo.NativeACUNormalizerForward

/-! Executable bounded full-native normalization and comparison for actual
ACU.Conv. Each node recursively normalizes every child in declaration order,
then canonicalizes addition and attempts one guarded legacy root contraction.
Failure is explicit; neither proof erasure nor Strict erasure is performed. -/
namespace Jihoo.NativeKernel.ACU.Bounded

open Conversion (ListRel treeSize treeDepth)

/-- Public hard caps match the existing substitution expansion and depth guards. -/
def maxNodes : Nat := 200000
def maxFuel : Nat := 128

def within (limit : Nat) (t : Term) : Bool := decide (treeSize t ≤ limit ∧ treeDepth t ≤ 128)

def keep (limit : Nat) (t : Term) : Option Term := if within limit t then some t else none

/-- Child outputs share the parent's node allowance. An oversized prefix fails
before further children are evaluated or a large parent tree is constructed. -/
def arguments (f : Term → Option Term) : Nat → List Term → Option (List Term)
  | _,[] => some []
  | remaining,x::xs => (f x).bind fun y =>
      if treeSize y ≤ remaining then (arguments f (remaining-treeSize y) xs).map (y::·) else none

def children (f : Term → Option Term) (limit : Nat) : Term → Option Term
  | .var x => some (.var x)
  | .node op xs => (arguments f (limit-1) xs).map (Term.node op)

/-- Bounded residual computation. Every recursive normalizer invocation uses
strictly less fuel; child output allocation additionally shares a node bound. -/
def normalize : Nat → Nat → Term → Option Term
  | 0,limit,t => keep limit t
  | fuel+1,limit,t => (keep limit t).bind fun start =>
      (children (normalize fuel limit) limit start).bind fun residual =>
      (keep limit (Canonical.sum residual)).bind fun canonical =>
      match Conversion.contract canonical with
      | some result => normalize fuel limit result
      | none => some canonical

/-- Refuse unsupported budgets instead of allocating an unbounded normal form.
All raw terms are supported when they fit these syntactic resource guards. -/
def run (fuel limit : Nat) (t : Term) : Option Term :=
  if fuel ≤ maxFuel ∧ 0 < limit ∧ limit ≤ maxNodes then normalize fuel limit t else none

private theorem keep_eq (h : keep limit t = some u) : t = u ∧ within limit t = true := by
  unfold keep at h
  split at h
  · exact ⟨Option.some.inj h,by assumption⟩
  · contradiction

private theorem arguments_forward
    (hf : ∀ x y, f x = some y → MixedRed x y)
    (h : arguments f remaining xs = some ys) : ListRel MixedRed xs ys := by
  induction xs generalizing remaining ys with
  | nil => cases h; exact .nil
  | cons x xs ih =>
      cases hx : f x with
      | none => simp only [arguments,hx,Option.bind_none] at h; contradiction
      | some y =>
          by_cases bound : treeSize y ≤ remaining
          · simp only [arguments,hx,Option.bind_some,bound,↓reduceIte,Option.map_eq_some_iff] at h
            obtain ⟨ys,hy,rfl⟩ := h
            exact .cons (hf x y hx) (ih hy)
          · simp only [arguments,hx,Option.bind_some,bound,↓reduceIte] at h; contradiction

private theorem children_forward
    (hf : ∀ x y, f x = some y → MixedRed x y)
    (h : children f limit t = some u) : MixedRed t u := by
  cases t with
  | var x => cases h; exact .refl _
  | node op xs =>
      simp only [children,Option.map_eq_some_iff] at h
      obtain ⟨ys,hy,rfl⟩ := h
      exact .node op (arguments_forward hf hy)

/-- Independent forward meaning of the existing guarded root computer. -/
theorem contract_forward (h : Conversion.contract t = some u) : MixedRed t u := by
  fun_cases Conversion.contract t <;> simp_all [Conversion.contract]
  all_goals try (split at h <;> simp_all <;> try (exact False.elim (by omega)))
  all_goals try (rcases h with ⟨hbound,h⟩)
  all_goals try subst u
  all_goals first
    | exact .compute (.beta _ _ _ _)
    | exact .arithmetic (.literalAdd _ _ (by change _ < 2^64; omega))
    | exact .compute (.sub _ _ _ (by omega) (by omega))
    | exact .compute (.read _ _ _ _ _ (by assumption))
    | exact .compute (.witnessPack _ _ _)
    | exact .compute (.proofPack _ _ _)
    | exact .compute (.derefBorrow _)
    | exact .compute (.borrowDeref _)
    | exact .compute (.transportRefl _ _ _)
    | exact .compute (.ifLtTrue _ _ _ _ (by omega))
    | exact .compute (.ifLtFalse _ _ _ _ (by omega))
    | exact .compute (.ifEqTrue _ _ _)
    | exact .compute (.ifEqFalse _ _ _ _ (by assumption))

/-- The exact executable output is an actual forward reduct. This proof uses
only local forward steps for children, ACU canonicalization and contraction;
it does not obtain reachability by applying Church–Rosser to soundness. -/
theorem normalize_forward (h : normalize fuel limit t = some u) : MixedRed t u := by
  induction fuel generalizing t u with
  | zero =>
      have eq := (keep_eq h).1
      subst u
      exact .refl _
  | succ fuel ih =>
      simp only [normalize,Option.bind_eq_some_iff] at h
      obtain ⟨start,hstart,residual,hresidual,canonical,hcanonical,last⟩ := h
      have eqStart := (keep_eq hstart).1
      subst start
      have eqCanonical := (keep_eq hcanonical).1
      subst canonical
      have first := (children_forward (fun x y h => ih h) hresidual).trans
        (.arithmetic (Canonical.sum_forward residual))
      cases hc : Conversion.contract (Canonical.sum residual) with
      | none => simp only [hc,Option.some.injEq] at last; subst u; exact first
      | some result =>
          simp only [hc] at last
          exact first.trans ((contract_forward hc).trans (ih last))

theorem normalize_sound (h : normalize fuel limit t = some u) : Conv t u := (normalize_forward h).toConv

theorem run_forward (h : run fuel limit t = some u) : MixedRed t u := by
  unfold run at h
  split at h
  · exact normalize_forward h
  · contradiction

theorem run_sound (h : run fuel limit t = some u) : Conv t u := (run_forward h).toConv

/-- All child and evidence positions participate in the final structural
comparison. A failed budget never turns into a successful equality result. -/
def equal (fuel limit : Nat) (a b : Term) : Bool :=
  match run fuel limit a,run fuel limit b with
  | some x,some y => x.equal y
  | _,_ => false

theorem equal_common_reduct (h : equal fuel limit a b = true) :
    ∃ u, MixedRed a u ∧ MixedRed b u := by
  unfold equal at h
  split at h
  · rename_i x y hx hy
    have same : x = y := (Term.equal_iff _ _).mp h
    subst y
    exact ⟨x,run_forward hx,run_forward hy⟩
  · contradiction

theorem equal_sound (h : equal fuel limit a b = true) : Conv a b := by
  obtain ⟨u,ha,hb⟩ := equal_common_reduct h
  exact ha.toConv.trans hb.toConv.symm

/-- Successful normalization respects both the requested node allowance and
the fixed capture-safe depth limit. -/
theorem normalize_within (h : normalize fuel limit t = some u) : within limit u = true := by
  induction fuel generalizing t u with
  | zero =>
      obtain ⟨eq,bound⟩ := keep_eq h
      simpa only [eq] using bound
  | succ fuel ih =>
      simp only [normalize,Option.bind_eq_some_iff] at h
      obtain ⟨start,hstart,residual,hresidual,canonical,hcanonical,last⟩ := h
      cases hc : Conversion.contract canonical with
      | none =>
          simp only [hc,Option.some.injEq] at last
          subst u
          simpa only [(keep_eq hcanonical).1] using (keep_eq hcanonical).2
      | some result =>
          simp only [hc] at last
          exact ih last

theorem run_within (h : run fuel limit t = some u) :
    treeSize u ≤ limit ∧ treeDepth u ≤ 128 := by
  unfold run at h
  split at h
  · exact of_decide_eq_true (normalize_within h)
  · contradiction

/-- A concrete proof-carrying API for the existing actual ACU conversion.
This record introduces no alternate conversion relation, basis, or reflection
assumption. Every field is filled below by the executable implementation. -/
structure NormalizerKit where
  normalize : Nat → Nat → Term → Option Term
  equal : Nat → Nat → Term → Term → Bool
  normalizationForward : ∀ {fuel limit t u}, normalize fuel limit t = some u → MixedRed t u
  normalizationSound : ∀ {fuel limit t u}, normalize fuel limit t = some u → Conv t u
  equalityCommonReduct : ∀ {fuel limit a b}, equal fuel limit a b = true →
    ∃ u, MixedRed a u ∧ MixedRed b u
  equalitySound : ∀ {fuel limit a b}, equal fuel limit a b = true → Conv a b

/-- The actual bounded full-Term implementation and all of its derived proofs. -/
def kit : NormalizerKit where
  normalize := run
  equal := Bounded.equal
  normalizationForward := run_forward
  normalizationSound := run_sound
  equalityCommonReduct := equal_common_reduct
  equalitySound := equal_sound

end Jihoo.NativeKernel.ACU.Bounded
