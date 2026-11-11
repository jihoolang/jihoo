import Jihoo.RecursiveFieldRuntime

/-! A closing-instance lexical interface for abstract binary field stores.
Data roots are distinct from Buffer values. Entering a case binds the roots
read from the store, revokes every parent alias and retains its shell for a
later release. This does not add source Case typing or native node reuse. -/
namespace Jihoo.RecursiveLexicalFields
open HeapLeases LinearHeapPrograms OwnedCoreContinuation RecursiveFieldOwnership
open RecursiveFieldRuntime

inductive Capability where
  | buffer (object : Nat)
  | data (tree : Tree)
  deriving DecidableEq, Repr

def Capability.owners : Capability → List Nat
  | .buffer x => [x]
  | .data tree => tree.owners

def footprint : List Capability → List Nat
  | [] => []
  | c :: cs => c.owners ++ footprint cs

def Capability.Fields (cells : Cells) : Capability → Prop
  | .buffer _ => True
  | .data tree => Represents cells tree

def Fields (cells : Cells) (caps : List Capability) : Prop :=
  ∀ c ∈ caps, c.Fields cells

def Inventory (s : RecursiveFieldRuntime.State) (caps : List Capability) : Prop :=
  Owns s.heap (footprint caps) ∧ Fields s.cells caps

inductive Entry where
  | nat (value : Nat)
  | scalar
  | buffer (slot : Nat)
  | data (slot : Nat)
  | ghost
  | dead
  deriving DecidableEq, Repr

inductive Value where
  | nat (value : Nat)
  | scalar (value : Nat)
  | buffer (object : Nat)
  | borrow (object : Nat)
  | data (reference : Ref)
  | ghost
  deriving DecidableEq, Repr

def Rel (caps : List Capability) : Entry → Value → Prop
  | .nat n, v => v = .nat n
  | .scalar, v => ∃ n, v = .scalar n
  | .buffer k, v => ∃ x, caps[k]? = some (.buffer x) ∧ v = .buffer x
  | .data k, v => ∃ tree, caps[k]? = some (.data tree) ∧ v = .data (root tree)
  | .ghost, v => v = .ghost
  | .dead, _ => True

inductive Agrees (caps : List Capability) : List Entry → List Value → Prop where
  | nil : Agrees caps [] []
  | cons : Rel caps e v → Agrees caps ctx env → Agrees caps (e :: ctx) (v :: env)

theorem Agrees.lookup {k : Nat} (h : Agrees caps ctx env) (found : ctx[k]? = some e) :
    ∃ v, env[k]? = some v ∧ Rel caps e v := by
  induction h generalizing k with
  | nil => simp at found
  | cons first rest ih =>
    cases k with
    | zero => cases Option.some.inj found; exact ⟨_, rfl, first⟩
    | succ k => exact ih found

/-- The selected data capability is head of the semantic inventory. Runtime
aliases may occur at any lexical index. Other capability slots shift by one. -/
def retireEntry : Entry → Entry
  | .buffer 0 | .data 0 => .dead
  | .buffer (k+1) => .buffer (k+2)
  | .data (k+1) => .data (k+2)
  | other => other

def retire (ctx : List Entry) := ctx.map retireEntry

theorem Rel.retire (h : Rel (.data parent :: rest) e v) :
    Rel (.data left :: .data right :: rest) (retireEntry e) v := by
  cases e with
  | buffer k => cases k <;> first | trivial | exact h
  | data k => cases k <;> first | trivial | exact h
  | nat _ | scalar | ghost | dead => exact h

theorem Agrees.retire (h : Agrees (.data parent :: rest) ctx env) :
    Agrees (.data left :: .data right :: rest) (retire ctx) env := by
  induction h with
  | nil => exact .nil
  | cons first _ ih => exact .cons first.retire ih

/-- Declaration order is [erased slots..., left, right]. Newest binders are
first, so the lexical order is [right, left, ghosts...] followed by outer slots. -/
def bindContext (ghosts : Nat) (ctx : List Entry) : List Entry :=
  .data 1 :: .data 0 :: (List.replicate ghosts .ghost ++ retire ctx)

def bindValues (ghosts : Nat) (cell : Cell) (env : List Value) : List Value :=
  .data cell.right :: .data cell.left :: (List.replicate ghosts .ghost ++ env)

theorem Agrees.ghosts (h : Agrees caps ctx env) :
    Agrees caps (List.replicate n .ghost ++ ctx) (List.replicate n .ghost ++ env) := by
  induction n with
  | zero => exact h
  | succ n ih => exact .cons rfl ih

theorem Agrees.bind {ghosts : Nat} (h : Agrees (.data (.node x left right) :: rest) ctx env) :
    Agrees (.data left :: .data right :: rest) (bindContext ghosts ctx)
      (bindValues ghosts ⟨root left, root right⟩ env) := by
  exact .cons ⟨right, rfl, rfl⟩ (.cons ⟨left, rfl, rfl⟩ h.retire.ghosts)

/-- The operational entry receives only an environment index and stored
fields, never a tree witness or a pre-flattened ownership inventory. -/
def enter (s : RecursiveFieldRuntime.State) (env : List Value) (k ghosts : Nat) :
    Option (List Value × Nat) := do
  let .data (some x) ← env[k]? | none
  if s.heap.live x then
    let cell ← s.cells x
    pure (bindValues ghosts cell env, x)
  else none

theorem Fields.bind (h : Fields cells (.data (.node x left right) :: rest)) :
    Fields cells (.data left :: .data right :: rest) := by
  have node : Represents cells (.node x left right) := h (.data (.node x left right)) (by simp)
  intro c member
  rcases List.mem_cons.mp member with rfl | member
  · exact node.2.1
  rcases List.mem_cons.mp member with rfl | member
  · exact node.2.2
  · exact h c (List.mem_cons_of_mem _ member)

/-- Real lookup constructs the case environment. Parent liveness is retained
as separate pending authority, not available through any old lexical alias. -/
theorem enter_total (agreement : Agrees (.data (.node x left right) :: rest) ctx env)
    (selected : ctx[k]? = some (.data 0))
    (inventory : Inventory s (.data (.node x left right) :: rest)) :
    ∃ env', enter s env k ghosts = some (env', x) ∧
      Agrees (.data left :: .data right :: rest) (bindContext ghosts ctx) env' ∧
      Owns s.heap (x :: footprint (.data left :: .data right :: rest)) ∧
      Fields s.cells (.data left :: .data right :: rest) := by
  obtain ⟨v, lookup, tree, cap, value⟩ := agreement.lookup selected
  have treeEq : Tree.node x left right = tree := Capability.data.inj (Option.some.inj cap)
  subst tree; subst v
  have node : Represents s.cells (.node x left right) := inventory.2 (.data (.node x left right)) (by simp)
  have live := inventory.1.live x (by simp [footprint, Capability.owners, Tree.owners])
  refine ⟨bindValues ghosts ⟨root left, root right⟩ env, ?_, agreement.bind, ?_, inventory.2.bind⟩
  · simp [enter, lookup, root, live, node.1]
  · simpa [footprint, Capability.owners, Tree.owners, List.append_assoc] using inventory.1

theorem footprint_member (cap : c ∈ caps) (member : x ∈ c.owners) : x ∈ footprint caps := by
  induction caps with
  | nil => simp at cap
  | cons d ds ih =>
    rcases List.mem_cons.mp cap with rfl | cap
    · exact List.mem_append_left _ member
    · exact List.mem_append_right _ (ih cap)

theorem Fields.clear (h : Fields cells caps) (absent : x ∉ footprint caps) :
    Fields (put cells x none) caps := by
  intro c member
  cases c with
  | buffer _ => trivial
  | data tree =>
    exact (h (.data tree) member).clear_other (fun here => absent (footprint_member member here))

/-- Final release consumes only the pending parent. The body must preserve
this authority and the active inventory; arbitrary bodies are not certified. -/
theorem finish_safe (valid : Valid s.heap)
    (pending : Owns s.heap (x :: footprint caps)) (fields : Fields s.cells caps) :
    Step s.heap (.free x) (release s x).heap ∧ Valid (release s x).heap ∧
    Inventory (release s x) caps := by
  have step := Step.free (pending.live x (by simp)) (pending.leaseFree x (by simp))
  exact ⟨step, step_valid valid step, free_owns pending Select.here,
    fields.clear (List.nodup_cons.mp pending.distinct).1⟩

theorem data_not_buffer : ¬ Rel caps (.buffer slot) (.data reference) := by
  rintro ⟨x, _, impossible⟩; cases impossible

theorem buffer_not_data : ¬ Rel caps (.data slot) (.buffer object) := by
  rintro ⟨tree, _, impossible⟩; cases impossible

end Jihoo.RecursiveLexicalFields
