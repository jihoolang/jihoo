import Jihoo.NativeSyntax
import Init.Data.List.Sort.Lemmas
import Init.Data.List.Nat.Sum

/-! An independent executable affine-sum model for the Var/Natural/UAdd fragment
of Core.sum. Equalities here are mathematical natural-number equalities, not new
rules of the untyped Conversion.Conv. Effects, Strict, USub cancellation, native
allocation/sharing and budget failures are deliberately outside this fragment.

The source boundary is Core.sum/canonical/natural_sum/collect in compiler/core.jh
(currently lines 1174–1375). Within this profile there are no non-variable atoms,
Strict prefixes or subtraction rounds. Native variable insertion sort and this
merge sort yield the same ascending multiset; balanced halving and the final
left fold mirror the source tree layout. Input admission checks native u32
variable IDs and u64 literal payloads. Expressions can have unbounded ghost
values; emitted leaves remain u64. The u128 accumulator theorem assumes the
native collect occurrence cap, not an unproved graph or source-step simulation.

runtimeCanonical reports only the source constant-overflow refusal condition;
Core.normal itself retains the original normalized UAdd at that boundary. The
actual-source snapshot differential test is separate from these universal Lean
semantic, completeness, payload, substitution and typing theorems. -/
namespace Jihoo.NativeKernel.AffineSum

def wordLimit : Nat := 2^64
def variableLimit : Nat := 2^32
def wideLimit : Nat := 2^128
def workLimit : Nat := 1000000

inductive Expr where
  | var (index : Nat)
  | literal (value : Nat)
  | add (left right : Expr)
  deriving Repr, DecidableEq

namespace Expr

def toTerm : Expr → Term
  | .var x => .var x
  | .literal n => .node (.natural n) []
  | .add a b => .node .uadd [a.toTerm, b.toTerm]

def eval (ρ : Nat → Nat) : Expr → Nat
  | .var x => ρ x
  | .literal n => n
  | .add a b => a.eval ρ + b.eval ρ

def Valid : Expr → Prop
  | .var x => x < variableLimit
  | .literal n => n < wordLimit
  | .add a b => a.Valid ∧ b.Valid

def decValid : (e : Expr) → Decidable e.Valid
  | .var x => inferInstanceAs (Decidable (x < variableLimit))
  | .literal n => inferInstanceAs (Decidable (n < wordLimit))
  | .add a b => @instDecidableAnd a.Valid b.Valid (decValid a) (decValid b)

instance (e : Expr) : Decidable e.Valid := decValid e

def variables : Expr → List Nat
  | .var x => [x]
  | .literal _ => []
  | .add a b => a.variables ++ b.variables

def constant : Expr → Nat
  | .var _ => 0
  | .literal n => n
  | .add a b => a.constant + b.constant

def literalCount : Expr → Nat
  | .var _ => 0
  | .literal _ => 1
  | .add a b => a.literalCount + b.literalCount

/-- Counts tree occurrences, as Core.collect does even when graph IDs repeat. -/
def visits : Expr → Nat
  | .var _ | .literal _ => 1
  | .add a b => 1 + a.visits + b.visits

theorem eval_collect (e : Expr) (ρ : Nat → Nat) :
    e.eval ρ = (e.variables.map ρ).sum + e.constant := by
  induction e with
  | var x => simp [eval, variables, constant]
  | literal n => simp [eval, variables, constant]
  | add a b ia ib => simp [eval, variables, constant, List.sum_append, ia, ib, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm]

theorem toTerm_wellFormed (e : Expr) : e.toTerm.WellFormed := by
  induction e with
  | var x => simp [toTerm, Term.WellFormed]
  | literal n => simp [toTerm, Term.WellFormed, Op.arity]
  | add a b ia ib => simp [toTerm, Term.WellFormed, Op.arity, ia, ib]

theorem literalCount_le_visits (e : Expr) : e.literalCount ≤ e.visits := by
  induction e <;> simp_all [literalCount, visits] <;> omega

theorem constant_bound {e : Expr} (h : e.Valid) :
    e.constant ≤ e.literalCount * (wordLimit - 1) := by
  induction e with
  | var x => simp [constant, literalCount]
  | literal n => simpa [constant, literalCount] using (show n ≤ wordLimit - 1 by
      change n < wordLimit at h; omega)
  | add a b ia ib =>
      have := Nat.add_le_add (ia h.1) (ib h.2)
      simpa [constant, literalCount, Nat.add_mul] using this

theorem constant_wide_bound {e : Expr} (h : e.Valid) (budget : e.visits ≤ workLimit) :
    e.constant < wideLimit := by
  have count := e.literalCount_le_visits
  have low := constant_bound h
  have high : workLimit * (wordLimit - 1) < wideLimit := by decide
  have mul := Nat.mul_le_mul_right (wordLimit - 1) (Nat.le_trans count budget)
  exact Nat.lt_of_le_of_lt (Nat.le_trans low mul) high

end Expr

structure Form where
  variables : List Nat
  constant : Nat
  deriving Repr, DecidableEq

namespace Form

def eval (f : Form) (ρ : Nat → Nat) : Nat := (f.variables.map ρ).sum + f.constant

def Sorted (f : Form) : Prop := f.variables.Pairwise (· ≤ ·)

end Form

def sortVariables (xs : List Nat) : List Nat := xs.mergeSort (fun a b => decide (a ≤ b))

theorem sortVariables_perm (xs : List Nat) : (sortVariables xs).Perm xs :=
  List.mergeSort_perm _ _

theorem sortVariables_sorted (xs : List Nat) : (sortVariables xs).Pairwise (· ≤ ·) := by
  have h := List.pairwise_mergeSort
    (le := fun (a b : Nat) => decide (a ≤ b))
    (by intro a b c hab hbc; simpa using Nat.le_trans (by simpa using hab) (by simpa using hbc))
    (by intro a b; simp; omega) xs
  simpa [sortVariables] using h

/-- Canonical multiset of variable occurrences, with the unbounded constant last. -/
def normalize (e : Expr) : Form := ⟨sortVariables e.variables, e.constant⟩

theorem normalize_sorted (e : Expr) : (normalize e).Sorted := sortVariables_sorted _

theorem normalize_sound (e : Expr) (ρ : Nat → Nat) : (normalize e).eval ρ = e.eval ρ := by
  have h := ((sortVariables_perm e.variables).map ρ).sum_nat
  simpa [normalize, Form.eval, Expr.eval_collect] using congrArg (· + e.constant) h

/-- Word-valued observations include zero and every coordinate unit valuation. -/
def WordValuation (ρ : Nat → Nat) : Prop := ∀ x, ρ x < wordLimit

def unitValuation (index : Nat) (x : Nat) : Nat := if x = index then 1 else 0

private theorem map_unit_sum (xs : List Nat) (i : Nat) :
    (xs.map (unitValuation i)).sum = xs.count i := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases h : x = i <;> simp [unitValuation, h, ih, Nat.add_comm]

private theorem map_zero_sum (xs : List Nat) : (xs.map (fun _ => 0)).sum = 0 := by
  induction xs <;> simp_all

/-- Constructive uniqueness of sorted Nat multisets, using coordinate counts. -/
private theorem sorted_eq_of_counts {xs ys : List Nat} (hx : xs.Pairwise (· ≤ ·))
    (hy : ys.Pairwise (· ≤ ·)) (counts : ∀ i, xs.count i = ys.count i) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => have := counts y; simp at this
  | cons x xs ih =>
      cases ys with
      | nil => have := counts x; simp at this
      | cons y ys =>
          have xm : x ∈ y :: ys := List.count_pos_iff.mp (by rw [← counts]; simp)
          have ym : y ∈ x :: xs := List.count_pos_iff.mp (by rw [counts]; simp)
          have xy : x ≤ y := by
            rcases List.mem_cons.mp ym with eq | mem
            · subst y; exact Nat.le_refl x
            · exact List.rel_of_pairwise_cons hx mem
          have yx : y ≤ x := by
            rcases List.mem_cons.mp xm with eq | mem
            · subst x; exact Nat.le_refl y
            · exact List.rel_of_pairwise_cons hy mem
          have eq : x = y := Nat.le_antisymm xy yx
          subst y
          have tails : ∀ i, xs.count i = ys.count i := by
            intro i
            have h := counts i
            simp only [List.count_cons] at h
            exact Nat.add_right_cancel h
          exact congrArg (x :: ·) (ih hx.tail hy.tail tails)

theorem Form.eq_of_word_evaluations {a b : Form} (ha : a.Sorted) (hb : b.Sorted)
    (same : ∀ ρ, WordValuation ρ → a.eval ρ = b.eval ρ) : a = b := by
  have zero : WordValuation (fun _ => 0) := by intro; exact (show 0 < wordLimit by decide)
  have constants : a.constant = b.constant := by
    simpa [Form.eval, map_zero_sum] using same _ zero
  have counts : ∀ i, a.variables.count i = b.variables.count i := by
    intro i
    have unit : WordValuation (unitValuation i) := by
      intro x; unfold unitValuation; split
      · exact (show 1 < wordLimit by decide)
      · exact (show 0 < wordLimit by decide)
    have h := same _ unit
    simp only [Form.eval, map_unit_sum, constants] at h
    exact Nat.add_right_cancel h
  have vars : a.variables = b.variables := sorted_eq_of_counts ha hb counts
  cases a; cases b; simp_all

/-- Complete for all affine equations, even when observers are restricted to
U64-valued variables. No finite sample set or semantic oracle is used. -/
theorem normalize_eq_iff (a b : Expr) : normalize a = normalize b ↔
    ∀ ρ, WordValuation ρ → a.eval ρ = b.eval ρ := by
  constructor
  · intro h ρ _
    rw [← normalize_sound a ρ, ← normalize_sound b ρ, h]
  · intro h
    exact Form.eq_of_word_evaluations (normalize_sorted a) (normalize_sorted b)
      (fun ρ hv => by simpa only [normalize_sound] using h ρ hv)

/-- Native natural_sum: oversized pure constants are split into balanced U64
literal trees. This models trees; the native arena may share equal halves. -/
def naturalSum (n : Nat) : Expr :=
  if n < wordLimit then .literal n
  else .add (naturalSum (n / 2)) (naturalSum (n - n / 2))
termination_by n
decreasing_by
  all_goals have positive : 2 ≤ wordLimit := by decide
  all_goals omega

theorem naturalSum_spec (n : Nat) :
    (∀ ρ, (naturalSum n).eval ρ = n) ∧ (naturalSum n).Valid := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      unfold naturalSum
      split
      · rename_i h
        exact ⟨fun _ => rfl, h⟩
      · rename_i h
        have positive : 2 ≤ wordLimit := by decide
        have left : n / 2 < n := by omega
        have right : n - n / 2 < n := by omega
        obtain ⟨lv, lp⟩ := ih _ left
        obtain ⟨rv, rp⟩ := ih _ right
        refine ⟨fun ρ => ?_, lp, rp⟩
        simp only [Expr.eval, lv, rv]
        omega

namespace Form

/-- Fold the variable sequence from left to right, exactly as Core.canonical. -/
def variableTree (first : Nat) (rest : List Nat) : Expr :=
  rest.foldl (fun t x => .add t (.var x)) (.var first)

def emitExpr (f : Form) : Expr :=
  match f.variables with
  | [] => naturalSum f.constant
  | x :: xs =>
      if f.constant = 0 then variableTree x xs
      else .add (variableTree x xs) (naturalSum f.constant)

/-- Frozen differential-test interface: native constructor trees, not a codec. -/
def emit (f : Form) : Term := f.emitExpr.toTerm

def WellPayloaded (f : Form) : Prop := ∀ x ∈ f.variables, x < variableLimit

private theorem eval_variable_fold (xs : List Nat) (acc : Expr) (ρ : Nat → Nat) :
    (xs.foldl (fun t x => Expr.add t (.var x)) acc).eval ρ =
      acc.eval ρ + (xs.map ρ).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih, Expr.eval, Nat.add_assoc]

private theorem valid_variable_fold (xs : List Nat) (acc : Expr)
    (ha : acc.Valid) (hx : ∀ x ∈ xs, x < variableLimit) :
    (xs.foldl (fun t x => Expr.add t (.var x)) acc).Valid := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x xs ih =>
      exact ih _ ⟨ha, hx x (by simp)⟩ (fun y hy => hx y (by simp [hy]))

theorem emitExpr_sound (f : Form) (ρ : Nat → Nat) : f.emitExpr.eval ρ = f.eval ρ := by
  cases f with
  | mk xs c =>
      cases xs with
      | nil => simp [emitExpr, eval, (naturalSum_spec c).1]
      | cons x xs =>
          simp only [emitExpr, eval, variableTree]
          split <;> simp_all [eval_variable_fold, Expr.eval, (naturalSum_spec c).1, Nat.add_assoc]

theorem emitExpr_valid (f : Form) (h : f.WellPayloaded) : f.emitExpr.Valid := by
  cases f with
  | mk xs c =>
      cases xs with
      | nil => exact (naturalSum_spec c).2
      | cons x xs =>
          have hv := valid_variable_fold xs (.var x) (h x (by simp))
            (fun y hy => h y (by simp [hy]))
          simp only [emitExpr]
          split
          · exact hv
          · exact ⟨hv, (naturalSum_spec c).2⟩

theorem emit_wellFormed (f : Form) : f.emit.WellFormed := f.emitExpr.toTerm_wellFormed

end Form

theorem Expr.variables_payload {e : Expr} (h : e.Valid) :
    ∀ x ∈ e.variables, x < variableLimit := by
  induction e with
  | var i => simpa [Expr.variables, Expr.Valid] using h
  | literal n => simp [Expr.variables]
  | add a b ia ib =>
      intro x hx
      simp only [Expr.variables, List.mem_append] at hx
      exact hx.elim (ia h.1 x) (ib h.2 x)

theorem normalize_payload {e : Expr} (h : e.Valid) : (normalize e).WellPayloaded := by
  intro x hx
  exact Expr.variables_payload h x ((sortVariables_perm e.variables).mem_iff.mp hx)

theorem normalize_emitExpr (f : Form) (h : f.Sorted) : normalize f.emitExpr = f :=
  Form.eq_of_word_evaluations (normalize_sorted _) h (fun ρ _ => by
    rw [normalize_sound, Form.emitExpr_sound])

/-- Shape parser for actual full native trees. Malformed arities and every
operator outside this fragment are rejected, rather than treated as atoms. -/
def parse : Term → Option Expr
  | .var x => some (.var x)
  | .node (.natural n) [] => some (.literal n)
  | .node .uadd [a, b] => do
      let a' ← parse a
      let b' ← parse b
      pure (.add a' b')
  | _ => none
termination_by t => sizeOf t
decreasing_by all_goals simp_wf; all_goals omega

theorem parse_toTerm (e : Expr) : parse e.toTerm = some e := by
  induction e <;> simp_all [Expr.toTerm, parse]

theorem parse_sound {t : Term} {e : Expr} (h : parse t = some e) : e.toTerm = t := by
  fun_induction parse t generalizing e with
  | case1 x =>
      simp only [Option.some.injEq] at h
      subst e
      rfl
  | case2 n =>
      simp only [Option.some.injEq] at h
      subst e
      rfl
  | case3 a b ia ib =>
      change (parse a).bind (fun ea => (parse b).bind (fun eb => some (.add ea eb))) = some e at h
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ea, ha, eb, hb, rfl⟩ := h
      simp only [Expr.toTerm, ia ha, ib hb]
  | case4 t _ _ _ => simp at h

/-- Executable strict profile admission. Payload checking is distinct from
shape parsing so the parser theorem covers all mathematical expressions. -/
def read (t : Term) : Option Expr := do
  let e ← parse t
  if e.Valid then some e else none

/-- Frozen differential-test interface. None means outside the proved profile. -/
def canonical (t : Term) : Option Form := (read t).map normalize

theorem read_toTerm {e : Expr} (h : e.Valid) : read e.toTerm = some e := by
  simp [read, parse_toTerm, h]

theorem read_sound {t : Term} {e : Expr} (h : read t = some e) :
    e.toTerm = t ∧ e.Valid := by
  change (parse t).bind (fun p => if p.Valid then some p else none) = some e at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, hi⟩ := h
  by_cases hv : p.Valid
  · simp only [hv, ↓reduceIte, Option.some.injEq] at hi
    subst e
    exact ⟨parse_sound hp, hv⟩
  · simp [hv] at hi

theorem canonical_toTerm {e : Expr} (h : e.Valid) : canonical e.toTerm = some (normalize e) := by
  simp [canonical, read_toTerm h]

theorem canonical_spec {t : Term} {f : Form} (h : canonical t = some f) :
    ∃ e, read t = some e ∧ e.toTerm = t ∧ e.Valid ∧ normalize e = f := by
  unfold canonical at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨e, he, hf⟩ := h
  exact ⟨e, he, (read_sound he).1, (read_sound he).2, hf⟩

theorem canonical_sorted {t : Term} {f : Form} (h : canonical t = some f) : f.Sorted := by
  obtain ⟨e, _, _, _, rfl⟩ := canonical_spec h
  exact normalize_sorted e

theorem canonical_payload {t : Term} {f : Form} (h : canonical t = some f) : f.WellPayloaded := by
  obtain ⟨e, _, _, he, rfl⟩ := canonical_spec h
  exact normalize_payload he

/-- Native syntax evaluation within the admitted affine fragment. This carries
an executable shape/payload admission witness, not a typing assumption. -/
def Evaluates (ρ : Nat → Nat) (t : Term) (n : Nat) : Prop :=
  ∃ e, read t = some e ∧ e.eval ρ = n

theorem Evaluates.deterministic {ρ : Nat → Nat} {t : Term} {m n : Nat}
    (hm : Evaluates ρ t m) (hn : Evaluates ρ t n) : m = n := by
  obtain ⟨a, ha, hva⟩ := hm
  obtain ⟨b, hb, hvb⟩ := hn
  have : a = b := Option.some.inj (ha.symm.trans hb)
  subst b
  omega

theorem canonical_sound {t : Term} {f : Form} (h : canonical t = some f) (ρ : Nat → Nat) :
    Evaluates ρ t (f.eval ρ) := by
  obtain ⟨e, he, _, _, rfl⟩ := canonical_spec h
  exact ⟨e, he, (normalize_sound e ρ).symm⟩

theorem canonical_emit_sound {t : Term} {f : Form} (h : canonical t = some f) (ρ : Nat → Nat) :
    Evaluates ρ f.emit (f.eval ρ) := by
  exact ⟨f.emitExpr, read_toTerm (f.emitExpr_valid (canonical_payload h)), f.emitExpr_sound ρ⟩

/-- Every literal in an admitted canonical output is a valid U64 leaf, including
when the total constant exceeds U64. Output is valid native syntax. -/
theorem canonical_emit_valid {t : Term} {f : Form} (h : canonical t = some f) :
    f.emitExpr.Valid ∧ f.emit.WellFormed :=
  ⟨f.emitExpr_valid (canonical_payload h), f.emit_wellFormed⟩

theorem canonical_idempotent {t : Term} {f : Form} (h : canonical t = some f) :
    canonical f.emit = some f := by
  rw [Form.emit, canonical_toTerm (f.emitExpr_valid (canonical_payload h)),
    normalize_emitExpr f (canonical_sorted h)]

/-- Native equality is decided only after both trees pass the affine profile. -/
def equal (a b : Term) : Bool :=
  match canonical a, canonical b with
  | some fa, some fb => decide (fa = fb)
  | _, _ => false

/-- Agreement under every U64-valued assignment, with both operands admitted. -/
def Equivalent (a b : Term) : Prop :=
  ∀ ρ, WordValuation ρ → ∃ n, Evaluates ρ a n ∧ Evaluates ρ b n

theorem equal_sound {a b : Term} (h : equal a b = true) : Equivalent a b := by
  unfold equal at h
  split at h
  · rename_i fa fb ha hb
    have hf : fa = fb := of_decide_eq_true h
    subst fb
    intro ρ _
    exact ⟨fa.eval ρ, canonical_sound ha ρ, canonical_sound hb ρ⟩
  · simp at h

theorem equal_complete {a b : Term} (h : Equivalent a b) : equal a b = true := by
  have zero : WordValuation (fun _ => 0) := by intro; exact (show 0 < wordLimit by decide)
  obtain ⟨n, ⟨ea, ha, _⟩, ⟨eb, hb, _⟩⟩ := h _ zero
  have ca : canonical a = some (normalize ea) := by simp [canonical, ha]
  have cb : canonical b = some (normalize eb) := by simp [canonical, hb]
  have same : normalize ea = normalize eb := normalize_eq_iff ea eb |>.mpr (by
    intro ρ hv
    obtain ⟨n, eva, evb⟩ := h ρ hv
    exact (Evaluates.deterministic ⟨ea, ha, rfl⟩ eva).trans
      (Evaluates.deterministic evb ⟨eb, hb, rfl⟩))
  simp [equal, ca, cb, same]

theorem equal_iff (a b : Term) : equal a b = true ↔ Equivalent a b :=
  ⟨equal_sound, equal_complete⟩

/-- Runtime overflow refusal, separately from ghost canonicalization. None is a
refusal to fold, not a claim that native Core.normal fails: native retains UAdd. -/
def runtimeCanonical (t : Term) : Option Form := do
  let f ← canonical t
  if f.constant < wordLimit then some f else none

theorem runtime_refuses_oversized {t : Term} {f : Form}
    (h : canonical t = some f) (large : wordLimit ≤ f.constant) : runtimeCanonical t = none := by
  simp [runtimeCanonical, h, Nat.not_lt.mpr large]

theorem runtime_accepts_small {t : Term} {f : Form}
    (h : canonical t = some f) (small : f.constant < wordLimit) : runtimeCanonical t = some f := by
  simp [runtimeCanonical, h, small]

theorem normalize_eq_iff_all (a b : Expr) : normalize a = normalize b ↔
    ∀ ρ, a.eval ρ = b.eval ρ := by
  constructor
  · intro h ρ
    rw [← normalize_sound a ρ, ← normalize_sound b ρ, h]
  · intro h
    exact (normalize_eq_iff a b).mpr (fun ρ _ => h ρ)

namespace Expr

def rename (ρ : Nat → Nat) : Expr → Expr
  | .var x => .var (ρ x)
  | .literal n => .literal n
  | .add a b => .add (a.rename ρ) (b.rename ρ)

def subst (σ : Nat → Expr) : Expr → Expr
  | .var x => σ x
  | .literal n => .literal n
  | .add a b => .add (a.subst σ) (b.subst σ)

theorem rename_eval (e : Expr) (σ : Nat → Nat) (ρ : Nat → Nat) :
    (e.rename σ).eval ρ = e.eval (fun x => ρ (σ x)) := by
  induction e <;> simp_all [rename, eval]

theorem subst_eval (e : Expr) (σ : Nat → Expr) (ρ : Nat → Nat) :
    (e.subst σ).eval ρ = e.eval (fun x => (σ x).eval ρ) := by
  induction e <;> simp_all [subst, eval]

theorem rename_toTerm (e : Expr) (ρ : Nat → Nat) :
    (e.rename ρ).toTerm = e.toTerm.rename ρ := by
  induction e <;> simp_all [rename, toTerm, Term.rename, renameArgs, Op.binders, liftRenaming]

theorem subst_toTerm (e : Expr) (σ : Nat → Expr) :
    (e.subst σ).toTerm = e.toTerm.subst (fun x => (σ x).toTerm) := by
  induction e <;> simp_all [subst, toTerm, Term.subst, substArgs, Op.binders, liftSub]

theorem valid_rename {e : Expr} (he : e.Valid) (ρ : Nat → Nat)
    (bound : ∀ x, x < variableLimit → ρ x < variableLimit) : (e.rename ρ).Valid := by
  induction e with
  | var x => exact bound x he
  | literal n => exact he
  | add a b ia ib => exact ⟨ia he.1, ib he.2⟩

theorem valid_subst {e : Expr} (he : e.Valid) (σ : Nat → Expr)
    (bound : ∀ x, x < variableLimit → (σ x).Valid) : (e.subst σ).Valid := by
  induction e with
  | var x => exact bound x he
  | literal n => exact he
  | add a b ia ib => exact ⟨ia he.1, ib he.2⟩

end Expr

/-- Canonical equality survives any affine substitution. Re-canonicalizing is
necessary because replacements and renamings can change variable ordering. -/
theorem normalize_subst_congr {a b : Expr} (h : normalize a = normalize b) (σ : Nat → Expr) :
    normalize (a.subst σ) = normalize (b.subst σ) := by
  apply (normalize_eq_iff_all _ _).mpr
  intro ρ
  simp only [Expr.subst_eval]
  exact (normalize_eq_iff_all a b).mp h _

theorem normalize_rename_congr {a b : Expr} (h : normalize a = normalize b) (ρ : Nat → Nat) :
    normalize (a.rename ρ) = normalize (b.rename ρ) := by
  apply (normalize_eq_iff_all _ _).mpr
  intro σ
  simp only [Expr.rename_eval]
  exact (normalize_eq_iff_all a b).mp h _

end Jihoo.NativeKernel.AffineSum
