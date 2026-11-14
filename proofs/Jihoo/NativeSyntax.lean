import Jihoo.Indexed

/-! Binding-aware trees for every constructor of compiler/core.jh's Term enum.
Native graph references become child trees; family/definition identifiers,
universe levels, flags, literal values and vector lengths remain Op payloads.
Vectors are flattened in declaration order. Elim, Case and View have motive,
then their cases, then the scrutinee. This representation does not assume that
an arbitrary tree is well formed or well typed. -/
namespace Jihoo.NativeKernel

inductive Arith where
  | add | sub | mul
  deriving Repr, DecidableEq

/-- Every non-variable native constructor, including runtime ownership forms.
Vector lengths are explicit so arity and child layout are independently checked. -/
inductive Op where
  | global (id : Nat)
  | universe (level : Nat)
  | prop | u64 | i64
  | array | lt | eq | refl | transport
  | ind (family count : Nat)
  | con (family constructor count : Nat)
  | elim (family cases : Nat)
  | arith (op : Arith)
  | fold | strict | uadd | ltAdd | ltCancel | ltLe | usub | zeroLe
  | refine | pack | witness | proof | buffer | alloc | load | store | free
  | drop (family : Nat)
  | ref | lend
  | back (erased : Bool)
  | give (erased : Bool)
  | take | borrow | deref
  | view (recursive : Bool) (family cases : Nat)
  | loop | absurd
  | caseOf (family cases : Nat)
  | pi (erased : Bool)
  | lam (erased : Bool)
  | app
  | natural (value : Nat)
  | integer (value : Int)
  | elements (count : Nat)
  | index | decide | ifLt | ifEq
  deriving Repr, DecidableEq

/-- Constructor spelling in the native source enum, for conformance tooling. -/
def Op.nativeName : Op → String
  | .global _ => "Global"
  | .universe _ => "Universe"
  | .prop => "Prop"
  | .u64 => "U64"
  | .i64 => "I64"
  | .array => "Array"
  | .lt => "Lt"
  | .eq => "Eq"
  | .refl => "Refl"
  | .transport => "Transport"
  | .ind _ _ => "Ind"
  | .con _ _ _ => "Con"
  | .elim _ _ => "Elim"
  | .arith _ => "Arith"
  | .fold => "Fold"
  | .strict => "Strict"
  | .uadd => "UAdd"
  | .ltAdd => "LtAdd"
  | .ltCancel => "LtCancel"
  | .ltLe => "LtLe"
  | .usub => "USub"
  | .zeroLe => "ZeroLe"
  | .refine => "Refine"
  | .pack => "Pack"
  | .witness => "Witness"
  | .proof => "Proof"
  | .buffer => "Buffer"
  | .alloc => "Alloc"
  | .load => "Load"
  | .store => "Store"
  | .free => "Free"
  | .drop _ => "Drop"
  | .ref => "Ref"
  | .lend => "Lend"
  | .back _ => "Back"
  | .give _ => "Give"
  | .take => "Take"
  | .borrow => "Borrow"
  | .deref => "Deref"
  | .view _ _ _ => "View"
  | .loop => "Loop"
  | .absurd => "Absurd"
  | .caseOf _ _ => "Case"
  | .pi _ => "Pi"
  | .lam _ => "Lam"
  | .app => "App"
  | .natural _ => "Natural"
  | .integer _ => "Integer"
  | .elements _ => "Elements"
  | .index => "Index"
  | .decide => "Decide"
  | .ifLt => "IfLt"
  | .ifEq => "IfEq"

/-- Number of graph references in declaration order, after flattening vectors. -/
def Op.arity : Op → Nat
  | .global _ | .universe _ | .prop | .u64 | .i64 | .natural _ | .integer _ => 0
  | .array | .refl | .zeroLe | .refine | .witness | .proof | .buffer | .ref |
      .borrow | .deref => 1
  | .lt | .eq | .arith _ | .strict | .uadd | .alloc | .free | .back _ | .take |
      .absurd | .pi _ | .lam _ | .app | .decide => 2
  | .transport | .fold | .usub | .pack | .lend | .give _ | .index => 3
  | .ltAdd | .ltCancel | .load | .store | .loop | .ifLt | .ifEq => 4
  | .ltLe => 5
  | .drop _ => 2
  | .ind _ count | .con _ _ count | .elements count => count
  | .elim _ cases | .caseOf _ cases | .view _ _ cases => cases + 2

/-- Exactly the four binder-sensitive cases of Core.transform. Functions in
other fields (Fold/Loop bodies, eliminator cases and continuations) carry their
binders as explicit Lam nodes; their child edges introduce no hidden binder. -/
def Op.binders : Op → Nat → Nat
  | .pi _, 1 | .lam _, 1 | .ifLt, 2 | .ifEq, 2 => 1
  | _, _ => 0

inductive Term where
  | var : Nat → Term
  | node : Op → List Term → Term
  deriving Repr

mutual
  /-- Executable structural comparison, including all native payloads/children. -/
  def Term.equal : Term → Term → Bool
    | .var x, .var y => decide (x = y)
    | .node op xs, .node op' ys => decide (op = op') && equalArgs xs ys
    | _, _ => false
  termination_by t _ => sizeOf t
  decreasing_by all_goals simp_wf; all_goals omega

  def equalArgs : List Term → List Term → Bool
    | [], [] => true
    | x :: xs, y :: ys => x.equal y && equalArgs xs ys
    | _, _ => false
  termination_by xs _ => sizeOf xs
  decreasing_by all_goals simp_wf; all_goals omega
end

theorem Term.equal_iff (t u : Term) : t.equal u = true ↔ t = u := by
  induction t using Term.rec
    (motive_2 := fun xs => ∀ ys, equalArgs xs ys = true ↔ xs = ys) generalizing u with
  | var x => cases u <;> simp [Term.equal]
  | node op xs ih => cases u <;> simp [Term.equal, ih]
  | nil => rename_i ys; cases ys <;> simp [equalArgs]
  | cons x xs ihx ihxs => rename_i ys; cases ys <;> simp [equalArgs, ihx, ihxs]

instance : DecidableEq Term := fun t u =>
  if h : t.equal u = true then isTrue ((Term.equal_iff t u).mp h)
  else isFalse (fun he => h ((Term.equal_iff t u).mpr he))

instance : BEq Term := ⟨Term.equal⟩

instance : LawfulBEq Term where
  eq_of_beq := (Term.equal_iff _ _).mp
  rfl := (Term.equal_iff _ _).mpr rfl

/-- Lift a variable renaming through the indicated number of local binders. -/
def liftRenaming : Nat → (Nat → Nat) → Nat → Nat
  | 0, ρ => ρ
  | n + 1, ρ => Indexed.liftRenaming (liftRenaming n ρ)

mutual
  /-- Capture-avoiding renaming across every native constructor's binding edges. -/
  def Term.rename (ρ : Nat → Nat) : Term → Term
    | .var x => .var (ρ x)
    | .node op args => .node op (renameArgs op ρ 0 args)
  termination_by t => sizeOf t
  decreasing_by all_goals simp_wf; all_goals omega

  def renameArgs (op : Op) (ρ : Nat → Nat) (offset : Nat) : List Term → List Term
    | [] => []
    | t :: ts => t.rename (liftRenaming (op.binders offset) ρ) :: renameArgs op ρ (offset + 1) ts
  termination_by ts => sizeOf ts
  decreasing_by all_goals simp_wf; all_goals omega
end

/-- Lift simultaneous substitution under one local binder. -/
def liftSubOne (σ : Nat → Term) : Nat → Term
  | 0 => .var 0
  | x + 1 => (σ x).rename Nat.succ

/-- Lift simultaneous substitution under an arbitrary binder count. -/
def liftSub : Nat → (Nat → Term) → Nat → Term
  | 0, σ => σ
  | n + 1, σ => liftSubOne (liftSub n σ)

/-- Substitute variable zero and remove its binder. -/
def single (a : Term) : Nat → Term
  | 0 => a
  | x + 1 => .var x

mutual
  /-- Capture-avoiding simultaneous substitution, using exactly Op.binders. -/
  def Term.subst (σ : Nat → Term) : Term → Term
    | .var x => σ x
    | .node op args => .node op (substArgs op σ 0 args)
  termination_by t => sizeOf t
  decreasing_by all_goals simp_wf; all_goals omega

  def substArgs (op : Op) (σ : Nat → Term) (offset : Nat) : List Term → List Term
    | [] => []
    | t :: ts => t.subst (liftSub (op.binders offset) σ) :: substArgs op σ (offset + 1) ts
  termination_by ts => sizeOf ts
  decreasing_by all_goals simp_wf; all_goals omega
end

/-- Arity well-formedness is separate from payload bounds, scope and typing. -/
def Term.WellFormed : Term → Prop
  | .var _ => True
  | .node op args => args.length = op.arity ∧ ∀ t ∈ args, t.WellFormed

/-- Finite variable scope follows each native binding edge independently. -/
inductive Term.Scoped : Nat → Term → Prop where
  | var : x < depth → Scoped depth (.var x)
  | node : (∀ i t, args[i]? = some t → Scoped (depth + op.binders i) t) →
      Scoped depth (.node op args)

end Jihoo.NativeKernel
