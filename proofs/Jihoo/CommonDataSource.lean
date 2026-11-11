import Jihoo.CommonDataDeterminism

/-! Strict constructor-view adapter for one binary family. Export fidelity and
native layout are tested boundaries, not source checker refinement theorems. -/
namespace Jihoo.CommonDataSource
open CommonData

inductive Node where
  | core (node : ScopedLend.Graph.Node)
  | ind (family : Nat) (arguments : List Nat)
  | con (family constructor : Nat) (arguments : List Nat)
  | caseOf (family motive : Nat) (branches : List Nat) (value : Nat)
  | drop (family owner rest : Nat)
  deriving DecidableEq, Repr
abbrev Graph := Array Node

def nodeAt (g : Graph) (id : Nat) := g[id]?.getD (.core .opaque)

def Node.children : Node → List Nat
  | .core n => n.children
  | .ind _ args | .con _ _ args => args
  | .caseOf _ motive branches value => motive :: value :: branches
  | .drop _ owner rest => [owner,rest]

structure Family where
  data : Bool
  params : Nat
  arity : Nat
  globals : Nat
  constructors : List Nat
  deriving DecidableEq, Repr

structure Source where
  root : Nat
  typeRoot : Nat
  family : Family
  nodes : Graph
  deriving DecidableEq, Repr

def binaryType (g : Graph) (id : Nat) : Bool := nodeAt g id == .ind 0 []

def constructorType (g : Graph) (id : Nat) : Bool :=
  match nodeAt g id with
  | .core (.pi false left rest) =>
    match nodeAt g rest with
    | .core (.pi false right result) => binaryType g left && binaryType g right && binaryType g result
    | _ => false
  | _ => false

def familyValid (s : Source) : Bool :=
  s.family.data && s.family.params == 0 && s.family.arity == 0 && s.family.globals == 0 &&
    match s.family.constructors with
    | [nil,node] => binaryType s.nodes nil && constructorType s.nodes node
    | _ => false

def valid (s : Source) : Bool :=
  s.nodes.size ≤ 4096 && s.root < s.nodes.size && s.typeRoot < s.nodes.size &&
    (List.range s.nodes.size).all fun id =>
      (nodeAt s.nodes id).children.all (· < id) && match nodeAt s.nodes id with
      | .core (.integer n) => n < 2^63
      | .core (.natural n) => n < 2^64
      | .core (.var n) => n < 2^32
      | _ => true

def constantDataMotive (g : Graph) (id : Nat) : Bool :=
  match nodeAt g id with
  | .core (.lam false ty body) => binaryType g ty && binaryType g body
  | _ => false

def branchBody (g : Graph) (id : Nat) : Option Nat :=
  match nodeAt g id with
  | .core (.lam false left rest) =>
    match nodeAt g rest with
    | .core (.lam false right body) =>
      if binaryType g left && binaryType g right then some body else none
    | _ => none
  | _ => none

/-- Only Data-valued Case is adapted. Its empty branch must be the nullary
constructor, which also forces the target typing's common result to Data. -/
def adaptNode (g : Graph) : Node → CommonData.Node
  | .core n => .core n
  | .ind 0 [] => .ind 0 []
  | .con 0 0 [] => .empty
  | .con 0 1 [left,right] => .construct left right
  | .drop 0 owner rest => .drop 0 owner rest
  | .caseOf 0 motive [nil,node] value =>
    if constantDataMotive g motive && nodeAt g nil == .con 0 0 [] then
      match branchBody g node with
      | some body => .caseTree value nil body 0
      | none => .core .opaque
    else .core .opaque
  | _ => .core .opaque

def adapt (s : Source) : Option CommonData.Graph :=
  if valid s && familyValid s then some (s.nodes.map (adaptNode s.nodes)) else none

/-- A checked constructor view of a direct Tree -> I64 export. This selects
its original body ID, without normalization or inferred replacement IDs. -/
def entry (s : Source) : Option (CommonData.Graph × Nat) := do
  let g ← adapt s
  match nodeAt s.nodes s.typeRoot, nodeAt s.nodes s.root with
  | .core (.pi false domain result), .core (.lam false annotation body) =>
    if binaryType s.nodes domain && binaryType s.nodes annotation && nodeAt s.nodes result == .core .i64
    then some (g,body) else none
  | _, _ => none

theorem adapted_at {id : Nat} :
    CommonData.nodeAt (g.map (adaptNode g)) id = adaptNode g (nodeAt g id) := by
  cases found : g[id]? <;>
    simp [CommonData.nodeAt, nodeAt, Array.getElem?_map, found, adaptNode]

theorem opaque_not_typed (shape : CommonData.nodeAt g term = .core .opaque) :
    ¬ Typing g ctx count sizes term kind := by
  intro typed
  cases typed <;> simp_all

/-- The adapted empty constructor arm forces Data result typing; this is why
this adapter does not silently erase a scalar or dependent motive. -/
theorem case_empty_result (shape : CommonData.nodeAt g term = .caseTree scrutinee nilBranch nodeBranch ghosts)
    (nilShape : CommonData.nodeAt g nilBranch = .empty)
    (typed : Typing g ctx count sizes term kind) : kind = .data := by
  cases typed <;> simp_all
  rename_i emptyTyped nodeTyped
  cases emptyTyped <;> simp_all

end Jihoo.CommonDataSource
