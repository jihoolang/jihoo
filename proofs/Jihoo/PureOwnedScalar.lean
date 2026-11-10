import Jihoo.OwnedScalarReader
import Jihoo.CorePayloadAdequacy

/-! Pure scalar computation on the existing original graph and mixed context.
Only integer, lexical scalar, and I64 let/application are executable here. The
translation preserves de Bruijn indices and reuses the existing Raw typing,
substitution and strict evaluation, rather than postulating convergence. -/
namespace Jihoo.PureOwnedScalar
open HeapLeases ScopedLend OwnedScalarContext
open CoreBridge (Raw)

def bindScalar (ctx : Context) : Context := .scalar 0 :: scalarShift ctx

theorem bindScalar_ownerView : ownerView (bindScalar ctx) = none :: ownerView ctx := by
  change none :: ownerView (scalarShift ctx) = _
  rw [scalarShift_ownerView]

theorem bindScalar_scalarBindings : scalarBindings (bindScalar ctx) (v :: values) =
    some v :: scalarBindings ctx values := by
  change some v :: scalarBindings (scalarShift ctx) (v :: values) = _
  rw [scalarShift_scalarBindings]

inductive Shape (g : Graph.Graph) (root arg body : Nat) : Prop where
  | intro (function ty : Nat) : Graph.nodeAt g root = .app function arg →
      Graph.nodeAt g function = .lam false ty body → Graph.nodeAt g ty = .i64 →
      Shape g root arg body

theorem Shape.head (h : Shape g root arg body) : ∃ f, Graph.nodeAt g root = .app f arg := by
  cases h with | intro f _ head _ _ => exact ⟨f, head⟩

theorem Shape.unique (a : Shape g root arg body) (b : Shape g root arg' body') :
    arg = arg' ∧ body = body' := by
  cases a with
  | intro f ty h hf _ =>
    cases b with
    | intro f' ty' h' hf' _ =>
      have eq := h.symm.trans h'; cases eq
      have eq := hf.symm.trans hf'; cases eq
      exact ⟨rfl, rfl⟩

inductive Represents (g : Graph.Graph) : Context → Nat → Nat → Raw → Prop where
  | integer : Graph.nodeAt g root = .integer v → Represents g ctx m root (.integer (Int.ofNat v))
  | scalar : Graph.nodeAt g root = .var k → ctx[k]? = some (.scalar slot) → slot < m →
      Represents g ctx m root (.var k)
  | app : Shape g root arg body → Represents g ctx m arg a →
      Represents g (bindScalar ctx) (m + 1) body b →
      Represents g ctx m root (.app (.lam false .i64 b) a)

inductive Eval (g : Graph.Graph) : Context → Nat → List Nat → Nat → Prop where
  | integer : Graph.nodeAt g root = .integer v → Eval g ctx root values v
  | scalar : Graph.nodeAt g root = .var k → ctx[k]? = some (.scalar slot) →
      values[slot]? = some v → Eval g ctx root values v
  | app : Shape g root arg body → Eval g ctx arg values a →
      Eval g (bindScalar ctx) body (a :: values) v → Eval g ctx root values v

theorem total (represented : Represents g ctx m root t) (length : values.length = m) :
    ∃ v, Eval g ctx root values v := by
  induction represented generalizing values with
  | integer shape => exact ⟨_, .integer shape⟩
  | scalar shape lookup bound =>
      have inside := bound
      rw [← length] at inside
      exact ⟨_, .scalar shape lookup (List.getElem?_eq_getElem inside)⟩
  | app shape _ _ ia ib =>
      obtain ⟨a, ha⟩ := ia length
      obtain ⟨v, hv⟩ := ib (values := a :: values) (by simp [length])
      exact ⟨v, .app shape ha hv⟩

theorem Eval.deterministic (a : Eval g ctx root values v) (b : Eval g ctx root values w) : v = w := by
  induction a generalizing w with
  | integer shape =>
      cases b with
      | integer other => have eq := shape.symm.trans other; cases eq; rfl
      | scalar other _ _ => have := shape.symm.trans other; contradiction
      | app other _ _ => obtain ⟨_, h⟩ := other.head; have := shape.symm.trans h; contradiction
  | scalar shape lookup value =>
      cases b with
      | integer other => have := shape.symm.trans other; contradiction
      | scalar other lookup' value' =>
          have eq := shape.symm.trans other; cases eq
          have eq := lookup.symm.trans lookup'; cases eq
          exact Option.some.inj (value.symm.trans value')
      | app other _ _ => obtain ⟨_, h⟩ := other.head; have := shape.symm.trans h; contradiction
  | app shape _ _ ia ib =>
      cases b with
      | integer other => obtain ⟨_, h⟩ := shape.head; have := h.symm.trans other; contradiction
      | scalar other _ _ => obtain ⟨_, h⟩ := shape.head; have := h.symm.trans other; contradiction
      | app shape' arg body =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          obtain rfl := ia arg
          exact ib body

def pureContext (ctx : Context) : CoreBridge.Raw.Context := fun k =>
  match ctx[k]? with | some (.scalar _) => some .i64 | _ => none

/-- Missing/owner/dead entries map to an arbitrary open placeholder, not their
original slot. These entries are absent from pureContext, so typed scalar lookup
cannot use the placeholder; no unavailable owner is converted to a scalar. -/
def closing (ctx : Context) (values : List Nat) : Nat → Raw := fun k =>
  match (scalarBindings ctx values)[k]? with
  | some (some v) => .integer (Int.ofNat v)
  | _ => .var 0

def Ready (ctx : Context) (values : List Nat) : Prop :=
  ∀ (k slot : Nat), ctx[k]? = some (.scalar slot) → ∃ v, values[slot]? = some v ∧ v < 2^63

theorem closing_scalar {ctx : Context} {values : List Nat} (lookup : ctx[k]? = some (.scalar slot)) (value : values[slot]? = some v) :
    closing ctx values k = .integer (Int.ofNat v) := by
  simp [closing, scalarBindings, ScalarCoreCallers.scalarBindings, List.getElem?_map, lookup, value]

theorem closing_substitution (ready : Ready ctx values) :
    CoreBridge.Raw.Beta.Substitution (pureContext ctx) (fun _ => none) (closing ctx values) := by
  intro k A typed
  cases lookup : ctx[k]? with
  | none => simp [pureContext, lookup] at typed
  | some binding =>
      cases binding with
      | owner | dead => simp [pureContext, lookup] at typed
      | scalar slot =>
          simp only [pureContext, lookup, Option.some.injEq] at typed
          subst A
          obtain ⟨v, hv, bound⟩ := ready k slot lookup
          rw [closing_scalar lookup hv]
          simpa only [Raw.subst] using CoreBridge.Raw.Beta.HasType.integer (Γ := fun _ => none) (n := Int.ofNat v) (by change -(2^63 : Int) ≤ (v : Int); omega)
            (by change (v : Int) < (2^63 : Int); omega)

/-- Generic over every existing Raw term and dependent result type, not just
our executable first-order scalar grammar. -/
theorem close_typed (typed : CoreBridge.Raw.Beta.HasType (pureContext ctx) t A)
    (ready : Ready ctx values) :
    CoreBridge.Raw.Beta.HasType (fun _ => none) (t.subst (closing ctx values)) (A.subst (closing ctx values)) :=
  typed.substitution (closing_substitution ready)

theorem Eval.bounded (graphValid : Graph.valid g = true)
    (bounds : ∀ v ∈ values, v < 2^63) (run : Eval g ctx root values v) : v < 2^63 := by
  induction run with
  | integer shape => exact OwnedScalarReader.graph_integer_bound graphValid shape
  | scalar _ _ lookup => exact bounds _ (List.mem_of_getElem? lookup)
  | app _ _ _ ia ib =>
      exact ib (by simpa using And.intro (ia bounds) bounds)

end Jihoo.PureOwnedScalar
