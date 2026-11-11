import Jihoo.OwnedCallContext

/-! Concrete runtime lexical bindings are not ownership slots. Static masks and
consumption remove authority but do not pretend that an old machine binding is
deleted. Agreement is one-way for the static entries that remain accessible. -/
namespace Jihoo.CoreLexicalContext
open HeapLeases ScopedLend LinearHeapPrograms OwnedScalarContext

inductive Value where
  | owner (identity : Nat)
  | scalar (value : Nat)
  | borrow (identity : Nat)
  /-- An unavailable/ghost placeholder, not a mutation performed by Free or move. -/
  | dead
  deriving DecidableEq, Repr
abbrev Env := List Value

structure Agrees (ctx : Context) (owners values : List Nat) (env : Env) : Prop where
  owner : ∀ (i k x : Nat), ctx[i]? = some (.owner k) → owners[k]? = some x → env[i]? = some (.owner x)
  scalar : ∀ (i k x : Nat), ctx[i]? = some (.scalar k) → values[k]? = some x → env[i]? = some (.scalar x)

variable {ctx : Context} {owners values owners' values' : List Nat} {env : Env}

def materialize (ctx : Context) (owners values : List Nat) : Env := ctx.map fun b => match b with
  | .owner k => (owners[k]?).map Value.owner |>.getD .dead
  | .scalar k => (values[k]?).map Value.scalar |>.getD .dead
  | .dead => .dead

theorem materialize_agrees : Agrees ctx owners values (materialize ctx owners values) := by
  constructor <;> intro i k x lookup value <;> simp [materialize, List.getElem?_map, lookup, value]

/-- Generic static remapping only needs to preserve the values of surviving
entries. A binding that becomes dead imposes no condition on the runtime slot. -/
theorem remap (agree : Agrees ctx owners values env) (f : Binding → Binding)
    (owner : ∀ (b : Binding) (k x : Nat), f b = .owner k → owners'[k]? = some x →
      ∃ j, b = .owner j ∧ owners[j]? = some x)
    (scalar : ∀ (b : Binding) (k x : Nat), f b = .scalar k → values'[k]? = some x →
      ∃ j, b = .scalar j ∧ values[j]? = some x) :
    Agrees (ctx.map f) owners' values' env := by
  constructor
  · intro i k x lookup value
    cases old : ctx[i]? with
    | none => simp [List.getElem?_map, old] at lookup
    | some b =>
      have mapped : f b = .owner k := by simpa [List.getElem?_map, old] using lookup
      obtain ⟨j, rfl, val⟩ := owner b k x mapped value
      exact agree.owner i j x old val
  · intro i k x lookup value
    cases old : ctx[i]? with
    | none => simp [List.getElem?_map, old] at lookup
    | some b =>
      have mapped : f b = .scalar k := by simpa [List.getElem?_map, old] using lookup
      obtain ⟨j, rfl, val⟩ := scalar b k x mapped value
      exact agree.scalar i j x old val

theorem prepend_owner (agree : Agrees ctx owners values env) (lookup : owners[k]? = some x) :
    Agrees (.owner k :: ctx) owners values (.owner x :: env) := by
  constructor
  · intro i j y binding val
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq, ScalarCoreCallers.Binding.owner.injEq] at binding
              subst j; have eq := lookup.symm.trans val; cases eq; rfl
    | succ i => exact agree.owner i j y binding val
  · intro i j y binding val
    cases i with
    | zero => simp at binding
    | succ i => exact agree.scalar i j y binding val

theorem prepend_scalar (agree : Agrees ctx owners values env) (lookup : values[k]? = some x) :
    Agrees (.scalar k :: ctx) owners values (.scalar x :: env) := by
  constructor
  · intro i j y binding val
    cases i with
    | zero => simp at binding
    | succ i => exact agree.owner i j y binding val
  · intro i j y binding val
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq, ScalarCoreCallers.Binding.scalar.injEq] at binding
              subst j; have eq := lookup.symm.trans val; cases eq; rfl
    | succ i => exact agree.scalar i j y binding val

theorem fresh (agree : Agrees ctx owners values env) :
    Agrees (OwnedScalarContext.fresh ctx) (x :: owners) values (.owner x :: env) := by
  apply prepend_owner (k := 0) (lookup := rfl)
  apply remap agree
  · intro b k y mapped val
    cases b with
    | owner j => simp only [ScalarCoreCallers.Binding.owner.injEq] at mapped; subst k; exact ⟨j, rfl, val⟩
    | scalar | dead => contradiction
  · intro b k y mapped val
    cases b with
    | scalar j => simp only [ScalarCoreCallers.Binding.scalar.injEq] at mapped; subst k; exact ⟨j, rfl, val⟩
    | owner | dead => contradiction

theorem consumed (agree : Agrees ctx owners values env) (selected : Select owners slot x rest) :
    Agrees (OwnedScalarContext.consumed slot ctx) rest values env := by
  apply remap agree
  · intro b k y mapped val
    cases b with
    | owner j =>
      by_cases eq : j = slot
      · simp [eq] at mapped
      · simp only [ite_eq_right eq, ScalarCoreCallers.Binding.owner.injEq] at mapped
        subst k
        exact ⟨j, rfl, (LinearCoreCallers.Select.lookup_other selected eq).symm.trans val⟩
    | scalar | dead => contradiction
  · intro b k y mapped val
    cases b with
    | scalar j => simp only [ScalarCoreCallers.Binding.scalar.injEq] at mapped; subst k; exact ⟨j, rfl, val⟩
    | owner j => by_cases eq : j = slot <;> simp [eq] at mapped
    | dead => contradiction

theorem scalar_shift (agree : Agrees ctx owners values env) :
    Agrees (scalarShift ctx) owners (v :: values) env := by
  apply remap agree
  · intro b k y mapped val
    cases b with
    | owner j => simp only [ScalarCoreCallers.Binding.owner.injEq] at mapped; subst k; exact ⟨j, rfl, val⟩
    | scalar | dead => contradiction
  · intro b k y mapped val
    cases b with
    | scalar j => simp only [ScalarCoreCallers.Binding.scalar.injEq] at mapped; subst k; exact ⟨j, rfl, val⟩
    | owner | dead => contradiction

theorem bind_scalar (agree : Agrees ctx owners values env) :
    Agrees (PureOwnedScalar.bindScalar ctx) owners (v :: values) (.scalar v :: env) :=
  prepend_scalar (scalar_shift agree) rfl

theorem transferred (agree : Agrees ctx owners values env) (selected : Select owners slot x rest) :
    Agrees (OwnedArgumentBinding.transferred ctx slot) owners values (.owner x :: env) := by
  apply prepend_owner (lookup := LinearCoreCallers.Select.lookup_selected selected)
  apply remap agree
  · intro b k y mapped val
    by_cases eq : b = .owner slot
    · simp [eq] at mapped
    · simp only [ite_eq_right eq] at mapped; subst b; exact ⟨k, rfl, val⟩
  · intro b k y mapped val
    by_cases eq : b = .owner slot
    · simp [eq] at mapped
    · simp only [ite_eq_right eq] at mapped; subst b; exact ⟨k, rfl, val⟩

theorem owned_returned (agree : Agrees ctx owners values env) (selected : Select owners slot x rest) :
    Agrees (ownedReturned ctx slot) (new :: owners) values (.owner x :: .owner new :: env) :=
  prepend_owner (fresh agree) (LinearCoreCallers.Select.lookup_selected (.there selected))

theorem scalar_returned (agree : Agrees ctx owners values env) (selected : Select owners slot x rest) :
    Agrees (scalarReturned ctx slot) owners (v :: values) (.owner x :: .scalar v :: env) :=
  prepend_owner (bind_scalar agree) (LinearCoreCallers.Select.lookup_selected selected)

theorem producer (agree : Agrees ctx owners values env) :
    Agrees (OwnedCallContext.producer ctx p) (owners.take p) values env := by
  apply remap agree
  · intro b k y mapped val
    cases b with
    | owner j =>
      by_cases bound : j < p
      · simp only [ite_eq_left bound, ScalarCoreCallers.Binding.owner.injEq] at mapped; subst k
        exact ⟨j, rfl, by simpa [bound] using val⟩
      · simp [bound] at mapped
    | scalar | dead => contradiction
  · intro b k y mapped val
    cases b with
    | scalar j => simp only [ScalarCoreCallers.Binding.scalar.injEq] at mapped; subst k; exact ⟨j, rfl, val⟩
    | owner j => by_cases bound : j < p <;> simp [bound] at mapped
    | dead => contradiction

theorem body (agree : Agrees ctx owners values env) :
    Agrees (OwnedCallContext.body ctx p) (returned :: owners.drop p) values (.owner returned :: env) := by
  apply prepend_owner (k := 0) (lookup := rfl)
  apply remap agree
  · intro b k y mapped val
    cases b with
    | owner j =>
      by_cases bound : j < p
      · simp [bound] at mapped
      · simp only [ite_eq_right bound, ScalarCoreCallers.Binding.owner.injEq] at mapped; subst k
        exact ⟨j, rfl, by simpa [List.getElem?_drop, show p + (j-p) = j by omega] using val⟩
    | scalar | dead => contradiction
  · intro b k y mapped val
    cases b with
    | scalar j => simp only [ScalarCoreCallers.Binding.scalar.injEq] at mapped; subst k; exact ⟨j, rfl, val⟩
    | owner j => by_cases bound : j < p <;> simp [bound] at mapped
    | dead => contradiction

theorem owner_lookup (agree : Agrees ctx owners values env)
    (resolved : ownerSlot g ctx root = some slot) (selected : Select owners slot x rest) :
    ∃ k, Graph.nodeAt g root = .var k ∧ env[k]? = some (.owner x) := by
  obtain ⟨k, shape, lookup⟩ := OwnedArgumentBinding.ownerSlot_variable resolved
  exact ⟨k, shape, agree.owner k slot x lookup (LinearCoreCallers.Select.lookup_selected selected)⟩

theorem scalar_lookup (agree : Agrees ctx owners values env)
    (resolved : resultAt g ctx root = some result) (value : result.eval values = some v) :
    Graph.nodeAt g root = .integer v ∨ ∃ k, Graph.nodeAt g root = .var k ∧ env[k]? = some (.scalar v) := by
  cases shape : Graph.nodeAt g root <;> simp [resultAt, ScalarCoreCallers.resultAt, shape] at resolved
  case integer n =>
    subst result
    simp only [ScalarCoreCallers.Result.eval, Option.some.injEq] at value
    subst n; exact Or.inl rfl
  case var k =>
    cases lookup : ctx[k]? with
    | none => simp [lookup] at resolved
    | some b =>
      cases b with
      | owner | dead => simp [lookup] at resolved
      | scalar slot =>
        simp [lookup] at resolved; subst result
        exact Or.inr ⟨k, rfl, agree.scalar k slot v lookup value⟩

/-- Only the distinguished borrow and selected owner's aliases carry reader
authority. Ghost/scalar roles impose no claim about the concrete value. -/
def ReaderAgrees (roles : List Graph.Role) (env : Env) (x : Nat) : Prop :=
  (∀ (i : Nat), roles[i]? = some .borrow → env[i]? = some (.borrow x)) ∧
  (∀ (i : Nat), roles[i]? = some .owner → env[i]? = some (.owner x))

theorem reader_roles (agree : Agrees ctx owners values env) (selected : Select owners slot x rest) :
    ReaderAgrees (readerRoles ctx slot) (.borrow x :: env) x := by
  constructor
  · intro i role
    have zero := (OwnedLendContext.reader_borrow_iff).mp role
    subst i; rfl
  · intro i role
    cases i with
    | zero => simp [readerRoles, OwnedLendContext.readerRoles] at role
    | succ i =>
      have view := (OwnedLendContext.reader_selected_iff).mp role
      cases lookup : ctx[i]? with
      | none => simp [ownerView, ScalarCoreCallers.ownerView, List.getElem?_map, lookup] at view
      | some b =>
        cases b with
        | owner k =>
          have eq : k = slot := by simpa [ownerView, ScalarCoreCallers.ownerView, List.getElem?_map, lookup] using view
          subst k
          exact agree.owner i slot x lookup (LinearCoreCallers.Select.lookup_selected selected)
        | scalar | dead => simp [ownerView, ScalarCoreCallers.ownerView, List.getElem?_map, lookup] at view

theorem reader_scalar (agree : ReaderAgrees roles env x) :
    ReaderAgrees (.scalar :: roles) (.scalar v :: env) x := by
  constructor
  · intro i role; cases i with
    | zero => simp at role
    | succ i => exact agree.1 i role
  · intro i role; cases i with
    | zero => simp at role
    | succ i => exact agree.2 i role

theorem reader_ghost (agree : ReaderAgrees roles env x) :
    ReaderAgrees (.ghost :: roles) (.dead :: env) x := by
  constructor
  · intro i role; cases i with
    | zero => simp at role
    | succ i => exact agree.1 i role
  · intro i role; cases i with
    | zero => simp at role
    | succ i => exact agree.2 i role

end Jihoo.CoreLexicalContext
