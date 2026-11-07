import Jihoo.GraphEquality

/-! Validation of a bounded, serialized constructor graph. This module proves
facts about decoded snapshots, not about the JSON parser, exporter, compiler
execution, typing checker, or machine arithmetic semantics. -/
namespace Jihoo.GraphCertificates

open CoreBridge

/-- Selected constructor payloads, with mathematical numbers before validation.
Administrative sorts are transported exactly but have no Raw interpretation.
Other unsupported compiler constructors have no encoding in this datatype. -/
inductive Node where
  | var (index : Nat)
  | natural (value : Nat)
  | integer (value : Int)
  | u64 | i64
  | array (length : Nat)
  | lt (left right : Nat)
  | eq (left right : Nat)
  | pi (erased : Bool) (type body : Nat)
  | lam (erased : Bool) (type body : Nat)
  | app (function argument : Nat)
  | elements (items : List Nat)
  | index (array index proof : Nat)
  | refl (value : Nat)
  | zeroLe (value : Nat)
  | decide (left right : Nat)
  | uadd (left right : Nat)
  | usub (left right proof : Nat)
  | prop
  | universe (level : Nat)
  deriving DecidableEq, Repr

abbrev Graph := Array Node

def nodeLimit : Nat := 4096
def treeLimit : Nat := 200000
def depthLimit : Nat := 128
def idBound : Nat := 2^32

/-- Source levels are below 32; inference of level 31 appends level 32.
Transporting that final administrative sort does not authorize typing it. -/
def universeBound : Nat := 33

def Node.children : Node → List Nat
  | .var _ | .natural _ | .integer _ | .u64 | .i64 | .prop | .universe _ => []
  | .array a | .refl a | .zeroLe a => [a]
  | .lt a b | .eq a b | .app a b | .decide a b | .uadd a b => [a, b]
  | .pi _ a b | .lam _ a b => [a, b]
  | .elements xs => xs
  | .index a b c | .usub a b c => [a, b, c]

def Node.payloadBounded : Node → Prop
  | .var k => k < idBound
  | .natural n => n < wordBound
  | .integer n => -signedBound ≤ n ∧ n < signedBound
  | .universe level => level < universeBound
  | _ => True

instance (n : Node) : Decidable n.payloadBounded := by
  cases n <;> unfold Node.payloadBounded <;> infer_instance

/-- Every edge, including an unused edge, points strictly backwards. -/
def Node.valid (id : Nat) (n : Node) : Bool :=
  Decidable.decide n.payloadBounded && Decidable.decide (n.children.length ≤ nodeLimit) &&
    n.children.all (fun child => Decidable.decide (child < id ∧ child < idBound))

theorem Node.valid_payload {n : Node} {id : Nat} (h : n.valid id = true) : n.payloadBounded := by
  simpa only [Node.valid, Bool.and_eq_true, decide_eq_true_eq] using
    (show Decidable.decide n.payloadBounded = true from (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1)

theorem Node.valid_backward {n : Node} {id child : Nat} (h : n.valid id = true) (hc : child ∈ n.children) :
    child < id ∧ child < idBound := by
  have ha := (Bool.and_eq_true_iff.mp h).2
  exact of_decide_eq_true ((List.all_eq_true.mp ha) child hc)

/-- Constructor interpretation is separate from recursive graph traversal. The
list must have exactly the arity of the constructor. -/
def Node.assemble : Node → List Raw → Option Raw
  | .var k, [] => some (.var k)
  | .natural n, [] => some (.natural n)
  | .integer n, [] => some (.integer n)
  | .u64, [] => some .u64
  | .i64, [] => some .i64
  | .array _, [a] => some (.array a)
  | .lt _ _, [a, b] => some (.lt a b)
  | .eq _ _, [a, b] => some (.eq a b)
  | .pi e _ _, [a, b] => some (.pi e a b)
  | .lam e _ _, [a, b] => some (.lam e a b)
  | .app _ _, [a, b] => some (.app a b)
  | .elements _, xs => some (.elements xs)
  | .index _ _ _, [a, b, c] => some (.index a b c)
  | .refl _, [a] => some (.refl a)
  | .zeroLe _, [a] => some (.zeroLe a)
  | .decide _ _, [a, b] => some (.decide a b)
  | .uadd _ _, [a, b] => some (.uadd a b)
  | .usub _ _ _, [a, b, c] => some (.usub a b c)
  | .prop, _ | .universe _, _ => none
  | _, _ => none

/-- Inert sorts cannot be smuggled into the interpreted fragment at any arity. -/
theorem Node.assemble_prop (ts : List Raw) : Node.prop.assemble ts = none := rfl

theorem Node.assemble_universe (level : Nat) (ts : List Raw) :
    (Node.universe level).assemble ts = none := rfl

inductive Related (R : α → β → Prop) : List α → List β → Prop where
  | nil : Related R [] []
  | cons : R x y → Related R xs ys → Related R (x :: xs) (y :: ys)

/- Independent structural interpretation: the exact node is present at the
claimed identifier, payloads and edges are valid, and all children denote the
corresponding subtrees. It neither calls the decoder nor mentions transforms. -/
mutual
inductive BoundedRepresentation (g : Graph) : Nat → Nat → Raw → Prop where
  | node {fuel id : Nat} {n : Node} {ts : List Raw} {t : Raw} (lookup : g[id]? = some n) (valid : n.valid id = true)
      (children : BoundedChildren g fuel n.children ts)
      (shape : n.assemble ts = some t) : BoundedRepresentation g (fuel + 1) id t

inductive BoundedChildren (g : Graph) : Nat → List Nat → List Raw → Prop where
  | nil : BoundedChildren g fuel [] []
  | cons {id : Nat} : BoundedRepresentation g fuel id t → BoundedChildren g fuel ids ts →
      BoundedChildren g fuel (id :: ids) (t :: ts)
end

theorem BoundedChildren.ofRelated
    (h : Related (BoundedRepresentation g fuel) ids ts) : BoundedChildren g fuel ids ts := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons hr ih

abbrev Represents (g : Graph) (id : Nat) (t : Raw) : Prop :=
  BoundedRepresentation g depthLimit id t

def traverse (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => do return (← f x) :: (← traverse f xs)

theorem traverse_sound {f : α → Option β} {xs : List α} {ys : List β} {R : α → β → Prop}
    (h : traverse f xs = some ys)
    (hf : ∀ x y, f x = some y → R x y) : Related R xs ys := by
  induction xs generalizing ys with
  | nil => simp only [traverse, Option.some.injEq] at h; subst ys; exact .nil
  | cons x xs ih =>
      cases hx : f x <;> cases hs : traverse f xs <;> simp [traverse, hx, hs] at h
      case some.some y ys' => subst ys; exact .cons (hf x y hx) (ih hs)

/-- Recursive unfolding has a hard depth bound; no default nodes or numeric
casts can repair malformed input. -/
def unfoldGraph : Nat → Graph → Nat → Option Raw
  | 0, _, _ => none
  | fuel + 1, g, id => do
      let n ← g[id]?
      if n.valid id then
        let ts ← traverse (unfoldGraph fuel g) n.children
        n.assemble ts
      else none

theorem unfoldGraph_sound {fuel id : Nat} {g : Graph} {t : Raw}
    (h : unfoldGraph fuel g id = some t) : BoundedRepresentation g fuel id t := by
  induction fuel generalizing id t with
  | zero => simp [unfoldGraph] at h
  | succ fuel ih =>
      cases hn : g[id]? with
      | none => simp [unfoldGraph, hn] at h
      | some n =>
          by_cases hv : n.valid id = true
          · cases ht : traverse (unfoldGraph fuel g) n.children with
            | none => simp [unfoldGraph, hn, hv, ht] at h
            | some ts =>
                simp [unfoldGraph, hn, hv, ht] at h
                exact .node hn hv (BoundedChildren.ofRelated (traverse_sound ht (fun _ _ hx => ih hx))) h
          · simp [unfoldGraph, hn, hv] at h

/-- Exact transport does not give a selected administrative sort a Raw meaning. -/
theorem unfoldGraph_prop_none {fuel id : Nat} {g : Graph}
    (lookup : g[id]? = some .prop) : unfoldGraph fuel g id = none := by
  cases fuel <;> simp [unfoldGraph, lookup, Node.valid, Node.payloadBounded,
    Node.children, traverse, Node.assemble]

theorem unfoldGraph_universe_none {fuel id level : Nat} {g : Graph}
    (lookup : g[id]? = some (.universe level)) : unfoldGraph fuel g id = none := by
  cases fuel <;> simp [unfoldGraph, lookup, Node.valid, Node.payloadBounded,
    Node.children, traverse, Node.assemble]

/-- Per-node DAG measurements are computed using only earlier entries, before
unfolding. They bound repeated references by counting each occurrence. -/
structure Measure where
  size : Nat
  depth : Nat
  deriving Repr

def measureNode (prior : Array Measure) (id : Nat) (n : Node) : Option Measure := do
  if !n.valid id then none else do
    let cs ← traverse (fun ref => prior[ref]?) n.children
    let m := Measure.mk (1 + (cs.map Measure.size).sum)
      (1 + (cs.map Measure.depth).foldl max 0)
    if m.size ≤ treeLimit ∧ m.depth ≤ depthLimit then some m else none

def measureGraph (g : Graph) : Option (Array Measure) :=
  g.foldlM (fun prior n => do
    let m ← measureNode prior prior.size n
    pure (prior.push m)) #[]

/-- Whole-graph validation includes unreachable nodes. Each graph is capped at
4096 nodes, each child vector at 4096, and every unfolded node at 200000 tree
occurrences and depth 128. Empty graphs cannot supply a root. -/
def graphValid (g : Graph) : Bool :=
  (decide (g.size ≤ nodeLimit) &&
    g.toList.zipIdx.all (fun (n, id) => n.valid id)) && (measureGraph g).isSome

theorem graphValid_bounds {g : Graph} (h : graphValid g = true) :
    g.size ≤ nodeLimit ∧
      ∀ n id, (n, id) ∈ g.toList.zipIdx → n.payloadBounded ∧
        n.children.length ≤ nodeLimit ∧ ∀ child ∈ n.children, child < id ∧ child < idBound := by
  have hs := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1)
  refine ⟨of_decide_eq_true hs.1, ?_⟩
  intro n id hn
  have hv := (List.all_eq_true.mp hs.2) (n, id) hn
  refine ⟨Node.valid_payload hv, ?_, fun child hc => Node.valid_backward hv hc⟩
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).2

def decode (g : Graph) (id : Nat) : Option Raw :=
  if graphValid g then unfoldGraph depthLimit g id else none

theorem decode_sound {g : Graph} {id : Nat} {t : Raw} (h : decode g id = some t) : Represents g id t := by
  unfold decode at h
  split at h
  · exact unfoldGraph_sound h
  · contradiction

/-- Acceptance proves the graph-count, all-node payload and backward-reference
bounds separately from the defensive size-measurement pass. -/
theorem decode_graph_bounds {g : Graph} {id : Nat} {t : Raw}
    (h : decode g id = some t) :
    g.size ≤ nodeLimit ∧
      ∀ n i, (n, i) ∈ g.toList.zipIdx → n.payloadBounded ∧
        n.children.length ≤ nodeLimit ∧ ∀ child ∈ n.children, child < i ∧ child < idBound := by
  unfold decode at h
  split at h
  next hv => exact graphValid_bounds hv
  next => contradiction

theorem decode_root_bound {g : Graph} {id : Nat} {t : Raw}
    (h : decode g id = some t) : id < g.size := by
  cases decode_sound h with
  | node lookup _ _ _ =>
      obtain ⟨bound, _⟩ := Array.getElem?_eq_some_iff.mp lookup
      exact bound

inductive Operation where
  | shift (amount : Nat)
  | substitute (replacement : Nat)
  deriving DecidableEq, Repr

structure Certificate where
  before : Graph
  after : Graph
  input : Nat
  output : Nat
  operation : Operation
  deriving Repr

/-- Equality of the entire old prefix, not a hash or a comparison of roots. -/
def appendOnly (c : Certificate) : Bool :=
  decide (c.before.toList <+: c.after.toList)

/-- Conservative work guard before substitution can duplicate an open value.
This preflight is defensive executable code, not a proved complexity theorem. -/
def substitutionSafe (c : Certificate) (replacement : Nat) : Bool :=
  match measureGraph c.before with
  | none => false
  | some sizes =>
      match sizes[c.input]?, sizes[replacement]? with
      | some a, some b => decide (a.size * b.size ≤ treeLimit ∧
          a.depth + b.depth ≤ depthLimit)
      | _, _ => false

def expected (c : Certificate) (input : Raw) : Option Raw :=
  match c.operation with
  | .shift amount =>
      if amount < signedBound.toNat then some (input.rename (fun k => k + amount)) else none
  | .substitute replacement =>
      if substitutionSafe c replacement then do
        let value ← decode c.before replacement
        pure (input.subst (Raw.single value))
      else none

/-- Acceptance compares decoded actual output to the existing formal transform;
it does not take the desired equality as a premise or proof field. -/
def validate (c : Certificate) : Bool :=
  if appendOnly c then
    match decode c.before c.input, decode c.after c.output with
    | some input, some output =>
        match expected c input with
        | some wanted => rawEqual output wanted
        | none => false
    | _, _ => false
  else false

/-- A successful check relates the original snapshot's input to the final
snapshot's output, and establishes actual append-only association. -/
theorem validate_sound (h : validate c = true) :
    c.before.toList <+: c.after.toList ∧
    ∃ input output, decode c.before c.input = some input ∧
      decode c.after c.output = some output ∧
      Represents c.before c.input input ∧ Represents c.after c.output output ∧
      expected c input = some output := by
  unfold validate at h
  split at h
  next hp =>
    have hp' : c.before.toList <+: c.after.toList := of_decide_eq_true hp
    cases hi : decode c.before c.input <;> cases ho : decode c.after c.output <;> simp [hi, ho] at h
    case some.some input output =>
      cases he : expected c input <;> simp [he, rawEqual_iff] at h
      case some wanted =>
        subst wanted
        exact ⟨hp', input, output, rfl, rfl, decode_sound hi, decode_sound ho, he⟩
  next => contradiction

theorem validate_shift (h : validate c = true) (hop : c.operation = .shift amount) :
    ∃ input output, Represents c.before c.input input ∧ Represents c.after c.output output ∧
      output = input.rename (fun k => k + amount) := by
  obtain ⟨_, input, output, _, _, hi, ho, he⟩ := validate_sound h
  simp only [expected, hop] at he
  split at he <;> cases he
  exact ⟨input, _, hi, ho, rfl⟩

theorem validate_substitute (h : validate c = true)
    (hop : c.operation = .substitute replacement) :
    ∃ input value output, Represents c.before c.input input ∧
      Represents c.before replacement value ∧ Represents c.after c.output output ∧
      output = input.subst (Raw.single value) := by
  obtain ⟨_, input, output, _, _, hi, ho, he⟩ := validate_sound h
  simp only [expected, hop] at he
  split at he
  next =>
    cases hv : decode c.before replacement <;> simp [hv] at he
    case some value =>
      subst output
      exact ⟨input, value, _, hi, decode_sound hv, ho, rfl⟩
  next => contradiction

end Jihoo.GraphCertificates
