import Jihoo.NativeEnvironmentChecker
import Jihoo.NativeEnvironmentExtension
import Jihoo.NativeOwnership

/-! Family-case quantities use the existing Control semantics. The finite table
is compiled from actual checked family lookups, and remains a checked witness
under environment extension. It supplies no typing or conversion oracle. -/
namespace Jihoo.NativeKernel.EnvironmentCaseQuantity
open Environment Jihoo.Quantity NativeQuantity

abbrev Table := List (Nat × CheckedFamily)

def TableValid (env : Environment) (table : Table) : Prop :=
  ∀ family entry, (family, entry) ∈ table → env.families[family]? = some entry

def compileTable (env : Environment) : Table :=
  (List.range env.families.size).filterMap fun family =>
    (env.families[family]?).map fun entry => (family, entry)

theorem compileTable_valid : TableValid env (compileTable env) := by
  intro family entry member
  obtain ⟨index, _, mapped⟩ := List.mem_filterMap.mp member
  cases found : env.families[index]? with
  | none => simp [found] at mapped
  | some value =>
      simp only [found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at mapped
      obtain ⟨rfl, rfl⟩ := mapped
      exact found

theorem TableValid.extend (extension : Environment.Extends before after)
    (valid : TableValid before table) : TableValid after table :=
  fun family entry member => extension.families family entry (valid family entry member)

def findFamily : Table → Nat → Option CheckedFamily
  | [], _ => none
  | (family, entry) :: rest, requested =>
      if family = requested then some entry else findFamily rest requested

theorem findFamily_sound (valid : TableValid env table)
    (h : findFamily table family = some entry) : env.families[family]? = some entry := by
  induction table with
  | nil => simp [findFamily] at h
  | cons pair rest ih =>
      rcases pair with ⟨index, value⟩
      simp only [findFamily] at h
      split at h
      · rename_i same; subst index; cases h
        exact valid _ _ (List.mem_cons_self)
      · exact ih (fun f e member => valid f e (List.mem_cons_of_mem _ member)) h

/-- Exactly one branch runs; the empty family has no branch contribution. -/
def alternatives : List Control → Control
  | [] => .pure
  | [c] => c
  | c :: cs => .branch c (alternatives cs)

/-- Native case_arity: parameters do not run. Recursive hypotheses follow fields.
Each recursive case runs repeatedly and therefore captures no outer owner. -/
def caseControls (visit : Term → Option Control) (params : Nat) (recursion : Bool) :
    List Signature → List Term → Option (List Control)
  | [], [] => some []
  | signature :: signatures, branch :: branches => do
      let control ← visit branch
      let rest ← caseControls visit params recursion signatures branches
      let count := signature.fields.length - params +
        (if recursion then (recursiveFields signature.fields).length else 0)
      let body := caseBody count control
      pure ((if recursion then .repeat body else .once body) :: rest)
  | _, _ => none

def project : Nat → List (Nat × CheckedFamily) → Term → Option Control
  | 0, _, _ => none
  | _ + 1, _, .var x => some (.use x)
  | fuel + 1, table, .node op args => do
      if args.length != op.arity then none else
      match op with
      | .global _ | .con _ _ _ | .lend => none
      | .elim family count | .caseOf family count => do
          let entry ← findFamily table family
          if !entry.declaration.data then none else
          let recursion := entry.boxed && match op with | .elim _ _ => true | _ => false
          let (cases, scrutinee) ← Environment.Checker.splitCases count (args.drop 1)
          let first ← project fuel table scrutinee
          let controls ← caseControls (project fuel table) entry.declaration.params recursion entry.signatures cases
          pure (.seq first (alternatives controls))
      | .view recursion family count => do
          let entry ← findFamily table family
          if !entry.boxed then none else
          let (cases, scrutinee) ← Environment.Checker.splitCases count (args.drop 1)
          let first ← project fuel table scrutinee
          let controls ← caseControls (project fuel table) entry.declaration.params recursion entry.signatures cases
          pure (.seq first (alternatives controls))
      | .app => projectCall fuel (project fuel table) (.node .app args)
      | .universe _ | .prop | .u64 | .i64 | .array | .lt | .eq | .refl |
          .transport | .ind _ _ | .ltAdd | .ltCancel | .ltLe | .zeroLe |
          .refine | .proof | .buffer | .ref | .back _ | .borrow | .deref |
          .absurd | .pi _ | .natural _ | .integer _ | .decide => some .pure
      | .arith _ | .strict | .uadd | .usub | .alloc | .free | .drop _ | .index =>
          fields (project fuel table) args [0, 1]
      | .store => fields (project fuel table) args [0, 1, 2]
      | .elements count => fields (project fuel table) args (List.range count)
      | .pack => fetch (project fuel table) args 1
      | .witness => fetch (project fuel table) args 0
      | .give erased => fields (project fuel table) args (if erased then [1] else [1, 2])
      | .lam erased => do
          let domain ← args[0]?
          let mode ← binderMode erased domain
          let bodyTerm ← args[1]?
          let body ← project fuel table bodyTerm
          pure (.closure (.scope mode (functionTail bodyTerm body)))
      | .ifLt | .ifEq => do
          let first ← fields (project fuel table) args [0, 1]
          let yes ← fetch (project fuel table) args 2
          let no ← fetch (project fuel table) args 3
          pure (.seq first (.branch (.scope .erased yes) no))
      | .fold => do
          let first ← fields (project fuel table) args [0, 1]
          let body ← fetch (project fuel table) args 2
          pure (.seq first (.repeat (caseBody 3 body)))
      | .loop => do
          let first ← fields (project fuel table) args [0, 2]
          let body ← fetch (project fuel table) args 3
          pure (.seq first (.repeat (caseBody 3 body)))
      | .load => do
          let first ← fields (project fuel table) args [0, 1]
          let body ← fetch (project fuel table) args 3
          pure (.seq first (.once (caseBody 2 body)))
      | .take => do
          let first ← fetch (project fuel table) args 0
          let body ← fetch (project fuel table) args 1
          pure (.seq first (.once (caseBody 2 body)))

/-- The result is a finite authentic projection with all local scope checks. -/
def ClosedSafe (table : Table) (term : Term) : Prop :=
  ∃ fuel control, project fuel table term = some control ∧ control.demand 0 = some 0

def checkClosed (fuel : Nat) (table : Table) (term : Term) : Bool :=
  (project fuel table term).any fun control => control.demand 0 == some 0

theorem checkClosed_sound (h : checkClosed fuel table term = true) : ClosedSafe table term := by
  cases hp : project fuel table term with
  | none => simp [checkClosed, hp] at h
  | some control =>
      exact ⟨fuel, control, hp, by simpa only [checkClosed,hp,Option.any_some,beq_iff_eq] using h⟩

theorem ClosedSafe.localScopes (safe : ClosedSafe table term) :
    ∃ fuel control, project fuel table term = some control ∧ NativeQuantity.LocalScopes control := by
  obtain ⟨fuel, control, projected, checked⟩ := safe
  exact ⟨fuel, control, projected, NativeQuantity.demand_localScopes control checked⟩

end Jihoo.NativeKernel.EnvironmentCaseQuantity
