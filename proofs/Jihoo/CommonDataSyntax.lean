import Jihoo.RecursiveCaseBody

/-! Restricted monomorphic binary-data syntax sharing original Core node IDs.
This is a graph extension, not an export of production Case families/motives. -/
namespace Jihoo.CommonData
open HeapLeases LinearHeapPrograms RecursiveFieldOwnership RecursiveFieldRuntime
open RecursiveLexicalFields

inductive Node where
  | core (node : ScopedLend.Graph.Node)
  | embedded (body : Nat)
  | ind (family : Nat) (arguments : List Nat)
  | empty
  | drop (family owner rest : Nat)
  | construct (left right : Nat)
  | caseTree (scrutinee emptyBranch nodeBranch ghosts : Nat)
  deriving DecidableEq, Repr
abbrev Graph := Array Node

def nodeAt (g : Graph) (id : Nat) : Node := g[id]?.getD (.core .opaque)
def projectNode : Node → ScopedLend.Graph.Node
  | .core n => n
  | _ => .opaque
def coreGraph (g : Graph) : ScopedLend.Graph.Graph := g.map projectNode

/-- Projection preserves node IDs and maps every extension/out-of-bounds node
 to opaque, never to an executable empty constructor. -/
theorem core_at {id : Nat} : ScopedLend.Graph.nodeAt (coreGraph g) id = projectNode (nodeAt g id) := by
  cases found : g[id]? <;>
    simp [ScopedLend.Graph.nodeAt, coreGraph, nodeAt, Array.getElem?_map, found, projectNode]

def Node.children : Node → List Nat
  | .core n => n.children
  | .embedded body => [body]
  | .empty => []
  | .ind _ arguments => arguments
  | .construct l r => [l,r]
  | .drop _ owner rest => [owner,rest]
  | .caseTree scrutinee emptyBranch nodeBranch _ => [scrutinee,emptyBranch,nodeBranch]

def validGraph (g : Graph) : Bool :=
  g.size ≤ 4096 && (List.range g.size).all fun id =>
    (nodeAt g id).children.all (· < id)

abbrev State := RecursiveCaseBody.State
abbrev finish := RecursiveCaseBody.finish

def allocate (s : State) (l r : Ref) : State :=
  ⟨⟨allocatedState s.buffers.heap 0, s.buffers.length⟩,
    put s.cells s.buffers.heap.nextObject (some ⟨l,r⟩)⟩

/-- Removing an empty head consumes all of its lexical aliases, preserving
slot positions and shifting the rest of the capability inventory by one. -/
def removeEntry : Entry → Entry
  | .data 0 | .buffer 0 => .dead
  | .data (k+1) => .data k
  | .buffer (k+1) => .buffer k
  | other => other

def removeHead (ctx : List Entry) := ctx.map removeEntry

/-- A computed argument consumes the entire old capability inventory. Only
non-owning lexical values survive; its returned tree gets one fresh slot. -/
def retireAll : Entry → Entry
  | .data _ | .buffer _ => .dead
  | other => other

def dataContinuation (ctx : List Entry) := .data 0 :: ctx.map retireAll

theorem rel_retireAll (h : Rel old e v) : Rel new (retireAll e) v := by
  cases e <;> first | trivial | exact h

theorem agrees_dataContinuation (h : Agrees old ctx env) :
    Agrees [.data tree] (dataContinuation ctx) (.data (root tree) :: env) := by
  constructor
  · exact ⟨tree,rfl,rfl⟩
  · induction h with
    | nil => exact .nil
    | cons head tail ih => exact .cons (rel_retireAll head) ih

def caps (trees : List Tree) (owners : List Nat) :=
  trees.map Capability.data ++ owners.map Capability.buffer

theorem rel_remove (h : Rel (.data tree :: rest) e v) : Rel rest (removeEntry e) v := by
  cases e with
  | data k | buffer k => cases k <;> first | trivial | exact h
  | nat _ | scalar | ghost | dead => exact h

theorem agrees_remove (h : Agrees (.data tree :: rest) ctx env) :
    Agrees rest (removeHead ctx) env := by
  induction h with
  | nil => exact .nil
  | cons first _ ih => exact .cons (rel_remove first) ih

theorem data_lookup {k slot : Nat} (h : Agrees capabilities ctx env)
    (selected : ctx[k]? = some (.data slot))
    (cap : capabilities[slot]? = some (.data tree)) : env[k]? = some (.data (root tree)) := by
  obtain ⟨v, found, actual, lookup, eq⟩ := h.lookup selected
  have same := Capability.data.inj (Option.some.inj (cap.symm.trans lookup))
  subst actual; subst v; exact found

theorem owns_permute (h : Owns heap xs) (perm : xs.Perm ys) : Owns heap ys :=
  ⟨perm.nodup_iff.mp h.distinct,
    fun x hx => h.live x (perm.mem_iff.mpr hx),
    fun x hx => h.leaseFree x (perm.mem_iff.mpr hx)⟩

theorem move_pending (h : Owns heap (x :: (active ++ frame))) :
    Owns heap (active ++ (x :: frame)) := by
  apply owns_permute h
  have perm : (([x] ++ active) ++ frame).Perm ((active ++ [x]) ++ frame) :=
    List.perm_append_comm.append_right frame
  simpa [List.append_assoc] using perm

theorem restore_pending (h : Owns heap (active ++ (x :: frame))) :
    Owns heap (x :: (active ++ frame)) := by
  apply owns_permute h
  have perm : (([x] ++ active) ++ frame).Perm ((active ++ [x]) ++ frame) :=
    List.perm_append_comm.append_right frame
  simp

theorem steps_append (a : HeapLeases.Steps s es t) (b : HeapLeases.Steps t fs u) :
    HeapLeases.Steps s (es ++ fs) u := by
  induction a with
  | nil => exact b
  | cons step _ ih => exact .cons step (ih b)

inductive Result where
  | scalar | data
  deriving DecidableEq, Repr

/-- Result ownership includes the caller's arbitrary pending frame. -/
def Post (kind : Result) (s : State) (v : Value) (frame : List Nat) : Prop :=
  match kind with
  | .scalar => (∃ n, v = .scalar n) ∧ Owns s.buffers.heap frame
  | .data => ∃ tree, v = .data (root tree) ∧ Represents s.cells tree ∧
      Owns s.buffers.heap (tree.owners ++ frame)

/-- A returned data tree cannot contain the pending parent being freed. -/
theorem Post.finish (post : Post kind s v (parent :: frame))
    (valid : Valid s.buffers.heap) :
    Step s.buffers.heap (.free parent) (finish s parent).buffers.heap ∧
      Valid (finish s parent).buffers.heap ∧ Post kind (finish s parent) v frame := by
  cases kind with
  | scalar =>
    obtain ⟨value, owned⟩ := post
    have step := Step.free (owned.live parent (by simp)) (owned.leaseFree parent (by simp))
    exact ⟨step, step_valid valid step, value,
      OwnedCoreContinuation.free_owns owned Select.here⟩
  | data =>
    obtain ⟨tree, value, fields, owned⟩ := post
    have pending := restore_pending owned
    have step := Step.free (pending.live parent (by simp)) (pending.leaseFree parent (by simp))
    have absent : parent ∉ tree.owners := by
      intro member
      exact (List.nodup_cons.mp pending.distinct).1 (List.mem_append_left frame member)
    exact ⟨step, step_valid valid step, tree, value, fields.clear_other absent,
      OwnedCoreContinuation.free_owns pending Select.here⟩

end Jihoo.CommonData
