import Jihoo.SizedErasedRuntime
import Jihoo.BoundedMir

/-! Structural operand lowering for compact sized-buffer terms. Natural lets
substitute pure operand aliases. Correctness is forward from a compact operand
evaluation; it does not assert evaluation of discarded, ill-typed arguments. -/
namespace Jihoo.SizedMir
open BoundedMir

/-- Owners and borrows share a physical base-pointer representation. Their
logical authority remains in the source typing and heap relations. -/
def toMir : SizedErasure.Value → Value
  | .nat n => .u64 n
  | .scalar v => .i64 v
  | .owner x | .borrow x => .pointer x 0

/-- Every compact environment entry has an operand denoting its encoded value. -/
inductive EnvRel : SizedErasure.Env → List Operand → Frame → Prop where
  | nil : EnvRel [] [] f
  | keep : operand f op = some (toMir value) → EnvRel env inputs f →
      EnvRel (value :: env) (op :: inputs) f

theorem EnvRel.lookup (related : EnvRel env inputs f)
    (source : env[(k : Nat)]? = some value) (target : inputs[k]? = some op) :
    operand f op = some (toMir value) := by
  induction related generalizing k with
  | nil => simp at source
  | keep head tail ih =>
    cases k with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at source target
              subst value; subst op; exact head
    | succ k => exact ih source target

theorem EnvRel.cons (related : EnvRel env inputs f)
    (head : operand f op = some (toMir value)) :
    EnvRel (value :: env) (op :: inputs) f := .keep head related

def lowerNat (inputs : List Operand) : SizedErasure.NatTerm → Option Operand
  | .literal n => if n < wordBound then some (.constant (.u64 n)) else none
  | .var k => inputs[k]?
  | .letE argument body => do
      let op ← lowerNat inputs argument
      lowerNat (op :: inputs) body

def lowerScalar (inputs : List Operand) : SizedErasure.ScalarTerm → Option Operand
  | .literal value => if value < scalarBound then some (.constant (.i64 value)) else none
  | .var k => inputs[k]?

theorem lowerNat_correct (run : SizedErasure.NatEval env term n)
    (related : EnvRel env inputs f) (lowered : lowerNat inputs term = some op) :
    operand f op = some (.u64 n) := by
  induction run generalizing inputs op with
  | literal =>
    simp only [lowerNat] at lowered
    split at lowered
    · cases lowered
      simp [operand, constant, *]
    · contradiction
  | var lookup => exact related.lookup lookup lowered
  | @letE env argument n body result argumentRun bodyRun first last =>
    simp only [lowerNat] at lowered
    cases ha : lowerNat inputs argument with
    | none => simp [ha] at lowered
    | some arg =>
      simp only [ha] at lowered
      exact last (related.cons (first related ha)) lowered

theorem lowerScalar_correct (run : SizedErasure.ScalarEval env term value)
    (related : EnvRel env inputs f) (lowered : lowerScalar inputs term = some op) :
    operand f op = some (.i64 value) := by
  cases run with
  | literal =>
    simp only [lowerScalar] at lowered
    split at lowered
    · cases lowered
      simp [operand, constant, *]
    · contradiction
  | var lookup => exact related.lookup lookup lowered

/-- Operands read only original local slots. Dereferences are excluded, so
changing scratch locals or the heap cannot affect their evaluation. -/
def Before (bound : Nat) : Operand → Prop
  | .constant _ => True
  | .copy place => place.deref = false ∧ place.slot < bound

instance (bound : Nat) (op : Operand) : Decidable (Before bound op) := by
  cases op <;> unfold Before <;> infer_instance

def InputsBefore (bound : Nat) (inputs : List Operand) : Prop :=
  ∀ op ∈ inputs, Before bound op

theorem Before.mono (before : Before small op) (larger : small ≤ large) : Before large op := by
  cases op with
  | constant => trivial
  | copy place => exact ⟨before.1, Nat.lt_of_lt_of_le before.2 larger⟩

theorem InputsBefore.mono (before : InputsBefore small inputs) (larger : small ≤ large) :
    InputsBefore large inputs := by
  intro op member
  exact (before op member).mono larger

theorem lowerNat_before (before : InputsBefore bound inputs)
    (lowered : lowerNat inputs term = some op) : Before bound op := by
  induction term generalizing inputs op with
  | literal n =>
    simp only [lowerNat] at lowered
    split at lowered
    · cases lowered; trivial
    · contradiction
  | var k => exact before op (List.mem_of_getElem? lowered)
  | letE argument body first last =>
    simp only [lowerNat] at lowered
    cases ha : lowerNat inputs argument with
    | none => simp [ha] at lowered
    | some arg =>
      simp only [ha] at lowered
      apply last _ lowered
      intro x member
      rcases List.mem_cons.mp member with rfl | rest
      · exact first before ha
      · exact before x rest

theorem lowerScalar_before (before : InputsBefore bound inputs)
    (lowered : lowerScalar inputs term = some op) : Before bound op := by
  cases term with
  | literal value =>
    simp only [lowerScalar] at lowered
    split at lowered
    · cases lowered; trivial
    · contradiction
  | var k => exact before op (List.mem_of_getElem? lowered)

theorem operand_frame (before : Before bound op)
    (same : ∀ slot, slot < bound → f.locals[slot]? = g.locals[slot]?) :
    operand f op = operand g op := by
  cases op with
  | constant c => rfl
  | copy place =>
    obtain ⟨plain, old⟩ := before
    simp [operand, same _ old, plain]

theorem EnvRel.frame (related : EnvRel env inputs f)
    (before : InputsBefore bound inputs)
    (same : ∀ slot, slot < bound → f.locals[slot]? = g.locals[slot]?) :
    EnvRel env inputs g := by
  induction related with
  | nil => exact .nil
  | keep head tail ih =>
    apply EnvRel.keep
    · exact (operand_frame (before _ (by simp)) same).symm.trans head
    · exact ih (by intro x member; exact before x (by simp [member])) same

theorem natural_overflow_rejected (h : wordBound ≤ n) :
    lowerNat inputs (.literal n) = none := by simp [lowerNat, Nat.not_lt_of_ge h]

theorem scalar_overflow_rejected (h : scalarBound ≤ value) :
    lowerScalar inputs (.literal value) = none := by simp [lowerScalar, Nat.not_lt_of_ge h]

end Jihoo.SizedMir
