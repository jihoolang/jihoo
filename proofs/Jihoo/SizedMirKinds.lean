import Jihoo.SizedMirOperands

/-! Representation-kind inference for compact branch result slots. This checks
only result representations, not ownership or full source typing. -/
namespace Jihoo.SizedMir
open BoundedMir

inductive Kind where
  | scalar | natural | pointer
  deriving DecidableEq, Repr

def Kind.ty : Kind → Ty
  | .scalar => .i64
  | .natural => .u64
  | .pointer => .ptr

def toKind : Ty → Option Kind
  | .i64 => some .scalar
  | .u64 => some .natural
  | .ptr => some .pointer
  | _ => none

def kindOf : SizedErasure.Value → Kind
  | .scalar _ => .scalar
  | .nat _ => .natural
  | .owner _ | .borrow _ => .pointer

def EnvKinds (env : SizedErasure.Env) (kinds : List Kind) : Prop :=
  env.map kindOf = kinds

theorem EnvKinds.cons (related : EnvKinds env kinds) :
    EnvKinds (value :: env) (kindOf value :: kinds) := by
  exact congrArg (List.cons (kindOf value)) related

theorem EnvKinds.lookup (related : EnvKinds env kinds)
    (source : env[(k : Nat)]? = some value) : kinds[k]? = some (kindOf value) := by
  rw [← related]
  simp [List.getElem?_map, source]

def inferKind (kinds : List Kind) : SizedErasure.Term → Option Kind
  | .scalar _ => some .scalar
  | .natural _ => some .natural
  | .var k => kinds[k]?
  | .allocate _ _ => some .pointer
  | .app argument body => do
      let first ← inferKind kinds argument
      inferKind (first :: kinds) body
  | .free _ body => inferKind kinds body
  | .lend _ _ body => inferKind (.pointer :: .scalar :: kinds) body
  | .ownedLend _ _ _ body => inferKind (.pointer :: .pointer :: kinds) body
  | .ifLt _ _ yes no => do
      let first ← inferKind kinds yes
      let last ← inferKind kinds no
      if first = last then some first else none

theorem inferKind_app (success : inferKind kinds (.app argument body) = some k) :
    ∃ first, inferKind kinds argument = some first ∧ inferKind (first :: kinds) body = some k := by
  cases h : inferKind kinds argument with
  | none => simp [inferKind, h] at success
  | some first => exact ⟨first, rfl, by simpa [inferKind, h] using success⟩

theorem inferKind_branch (success : inferKind kinds (.ifLt left right yes no) = some k) :
    inferKind kinds yes = some k ∧ inferKind kinds no = some k := by
  cases hy : inferKind kinds yes with
  | none => simp [inferKind, hy] at success
  | some a =>
    cases hn : inferKind kinds no with
    | none => simp [inferKind, hy, hn] at success
    | some b =>
      by_cases same : a = b
      · subst b
        simp [inferKind, hy, hn] at success
        subst k
        exact ⟨rfl, rfl⟩
      · simp [inferKind, hy, hn, same] at success

theorem inferKind_correct (success : inferKind kinds term = some k)
    (related : EnvKinds env kinds)
    (run : SizedErasure.Eval env term s value events t) : kindOf value = k := by
  induction run generalizing kinds k with
  | scalar => simpa [inferKind, kindOf] using success
  | natural => simpa [inferKind, kindOf] using success
  | var lookup =>
    exact Option.some.inj ((related.lookup lookup).symm.trans success)
  | allocate => simpa [inferKind, kindOf] using success
  | app first last firstIH lastIH =>
    obtain ⟨argKind, arg, body⟩ := inferKind_app success
    have hk := firstIH arg related
    apply lastIH body
    rw [← hk]
    exact related.cons
  | free lookup body ih => exact ih success related
  | yes left right bound body ih => exact ih (inferKind_branch success).1 related
  | no left right bound body ih => exact ih (inferKind_branch success).2 related
  | lend lookup index body ih =>
    exact ih success (by simpa [kindOf] using (related.cons (value := .scalar _)).cons (value := .owner _))
  | ownedLend lookup index length body ih =>
    exact ih success (by simpa [kindOf] using (related.cons (value := .owner _)).cons (value := .owner _))

@[simp] theorem toMir_valueType : valueType (toMir value) = (kindOf value).ty := by
  cases value <;> rfl

/-- Kinds of the initial operand aliases, using only input declarations. -/
def inputKinds (inputTypes : Array Ty) (inputs : List Operand) : Option (List Kind) :=
  inputs.mapM fun op => do
    let ty ← operandType ⟨inputTypes, #[]⟩ op
    toKind ty

/-- A narrow input condition: declared operand kinds agree with represented
source values. It does not assert typing of unrelated frame slots. -/
def InputKindsAgree (inputTypes : Array Ty) (inputs : List Operand)
    (env : SizedErasure.Env) : Prop :=
  inputKinds inputTypes inputs = some (env.map kindOf)

theorem InputKindsAgree.envKinds (agree : InputKindsAgree inputTypes inputs env)
    (success : inputKinds inputTypes inputs = some kinds) : EnvKinds env kinds :=
  Option.some.inj (agree.symm.trans success)

end Jihoo.SizedMir
