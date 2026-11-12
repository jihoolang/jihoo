import Jihoo.BoundedMir

/-! A layout-neutral candidate memory extension, not production Data lowering.
Cells are abstract slots: no claim about pointer width, tags, field offsets,
null bit patterns, alignment or native allocation layout is made here.
The existing BoundedMir and all SizedMir semantics remain unchanged. -/
namespace Jihoo.ReferenceHeap

inductive Ref where
  | null
  | object (id index : Nat)
  deriving DecidableEq, Repr
inductive Cell where
  | scalar (value : Nat)
  | reference (value : Ref)
  deriving DecidableEq, Repr
structure Object where
  alive : Bool
  cells : Array (Option Cell)
  deriving DecidableEq, Repr
abbrev Heap := Array Object

def isNull : Ref → Bool
  | .null => true
  | .object _ _ => false

/-- Address validity is distinct from initialized-cell validity. No dereference
of null, a dead object, an absent object, or a one-past pointer is permitted. -/
def address (H : Heap) : Ref → Option (Nat × Nat × Object)
  | .null => none
  | .object j i => do
    let obj ← H[j]?
    if obj.alive && i < obj.cells.size then some (j, i, obj) else none

def load (H : Heap) (p : Ref) : Option Cell := do
  let (_, i, obj) ← address H p
  (obj.cells[i]?).join

def loadRef (H : Heap) (p : Ref) : Option Ref := do
  let .reference r ← load H p | none
  pure r

def loadScalar (H : Heap) (p : Ref) : Option Nat := do
  let .scalar n ← load H p | none
  pure n

def validCell : Cell → Bool
  | .scalar n => n < BoundedMir.scalarBound
  | .reference _ => true

/-- Storing a reference does not dereference its target. In particular, dangling
references can be transported; ownership/liveness of children is a separate
source invariant, as with existing pointer-valued MIR locals. -/
def store (H : Heap) (p : Ref) (v : Cell) : Option Heap := do
  let (j, i, obj) ← address H p
  if validCell v then
    some (H.set! j {obj with cells := obj.cells.set! i (some v)})
  else none

/-- Same bounded accounting as BoundedMir, measured in abstract 8-byte slots
only for compatibility with its scalar fragment. This is not a Data ABI. -/
def allocate (H : Heap) (bytes : Nat) : Option Heap :=
  if 0 < bytes && bytes % 8 == 0 && bytes ≤ 32768 && H.size < 512 &&
      (H.toList.map (fun obj => obj.cells.size)).sum + bytes / 8 ≤ 4096 then
    some (H.push ⟨true, Array.replicate (bytes / 8) none⟩)
  else none

def release (H : Heap) : Ref → Option Heap
  | .null => none
  | .object j i => do
    let obj ← H[j]?
    if obj.alive && i == 0 then some (H.set! j {obj with alive := false}) else none

inductive Op where
  | read (p : Ref)
  | write (p value : Ref)
  | nullTest (p : Ref)
  | alloc (bytes : Nat)
  | free (p : Ref)
  deriving DecidableEq, Repr
inductive Result where
  | reference (p : Ref)
  | boolean (b : Bool)
  | unit
  deriving DecidableEq, Repr

/-- Memory-operation execution; integration with CFG locals is future work. -/
def execute (H : Heap) : Op → Option (Heap × Result)
  | .read p => do pure (H, .reference (← loadRef H p))
  | .write p r => do pure (← store H p (.reference r), .unit)
  | .nullTest p => some (H, .boolean (isNull p))
  | .alloc bytes => do pure (← allocate H bytes, .reference (.object H.size 0))
  | .free p => do pure (← release H p, .unit)

/-- Relational rules independent of execute. -/
inductive Step : Heap → Op → Heap → Result → Prop where
  | read : loadRef H p = some r → Step H (.read p) H (.reference r)
  | write : store H p (.reference r) = some H' → Step H (.write p r) H' .unit
  | nullTest : Step H (.nullTest p) H (.boolean (isNull p))
  | alloc : allocate H bytes = some H' →
      Step H (.alloc bytes) H' (.reference (.object H.size 0))
  | free : release H p = some H' → Step H (.free p) H' .unit

theorem execute_iff : execute H op = some (H', result) ↔ Step H op H' result := by
  constructor
  · intro h
    cases op with
    | read p =>
      cases hr : loadRef H p <;> simp [execute, hr] at h
      rcases h with ⟨rfl, rfl⟩
      exact .read hr
    | write p r =>
      cases hs : store H p (.reference r) <;> simp [execute, hs] at h
      rcases h with ⟨rfl, rfl⟩
      exact .write hs
    | nullTest p =>
      simp [execute] at h
      rcases h with ⟨rfl, rfl⟩
      exact .nullTest
    | alloc bytes =>
      cases ha : allocate H bytes <;> simp [execute, ha] at h
      rcases h with ⟨rfl, rfl⟩
      exact .alloc ha
    | free p =>
      cases hf : release H p <;> simp [execute, hf] at h
      rcases h with ⟨rfl, rfl⟩
      exact .free hf
  · intro h
    cases h <;> simp_all [execute]

theorem step_deterministic (a : Step H op H₁ r₁) (b : Step H op H₂ r₂) :
    H₁ = H₂ ∧ r₁ = r₂ := by
  have h := (execute_iff.mpr a).symm.trans (execute_iff.mpr b)
  simpa using h

@[simp] theorem load_null : load H .null = none := rfl
@[simp] theorem store_null : store H .null v = none := rfl
@[simp] theorem release_null : release H .null = none := rfl
@[simp] theorem null_ne_object : (Ref.null ≠ Ref.object j i) := by simp

theorem load_dead (h : H[j]? = some obj) (dead : obj.alive = false) :
    load H (.object j i) = none := by simp [load, address, h, dead]

theorem load_oob (h : H[j]? = some obj) (bound : obj.cells.size ≤ i) :
    load H (.object j i) = none := by simp [load, address, h, Nat.not_lt.mpr bound]

theorem load_uninitialized (h : H[j]? = some obj) (empty : obj.cells[i]? = some none) :
    load H (.object j i) = none := by
  simp [load, address, h, empty]

/-- Exact scalar embedding. none continues to mean uninitialized, never null. -/
def embedObject (o : BoundedMir.Object) : Object :=
  ⟨o.alive, o.cells.map (Option.map Cell.scalar)⟩
def embed (H : Array BoundedMir.Object) : Heap := H.map embedObject

theorem scalar_load_compatible (H : Array BoundedMir.Object) :
    loadScalar (embed H) (.object j i) = BoundedMir.load H j i := by
  simp only [loadScalar, load, address, embed, Array.getElem?_map]
  cases h : H[j]? with
  | none => simp [h, BoundedMir.load]
  | some obj =>
    simp only [Option.map_some]
    by_cases live : obj.alive = true
    · by_cases bound : i < obj.cells.size
      · simp [embedObject, live, bound, BoundedMir.load, h]
        cases obj.cells[i] <;> rfl

      · simp [embedObject, live, bound, BoundedMir.load, h]
    · have dead : obj.alive = false := Bool.eq_false_iff.mpr live
      simp [embedObject, dead, BoundedMir.load, h]

theorem release_compatible (H : Array BoundedMir.Object) :
    release (embed H) (.object j i) = (BoundedMir.freeHeap H j i).map embed := by
  simp only [release, embed, Array.getElem?_map]
  cases h : H[j]? with
  | none => simp [h, BoundedMir.freeHeap]
  | some obj =>
    simp [h, BoundedMir.freeHeap, embedObject]
    split <;> simp_all [embed, embedObject]

theorem allocate_compatible (H : Array BoundedMir.Object) :
    allocate (embed H) bytes = (BoundedMir.mallocHeap H bytes).map embed := by
  simp [allocate, BoundedMir.mallocHeap, embed, embedObject, List.map_map,
    Function.comp_def, Array.map_replicate]

/-- The exact dereferencing i64 write branch of existing BoundedMir commutes
with the embedding, including all failure cases. -/
theorem scalar_write_compatible (c : BoundedMir.Code) (f : BoundedMir.Frame)
    (hc : c.locals[slot]? = some .ptr)
    (hf : (f.locals[slot]?).join = some (.pointer j i)) :
    (BoundedMir.write c f ⟨slot, true⟩ (.i64 n)).map (fun out => embed out.heap) =
      store (embed f.heap) (.object j i) (.scalar n) := by
  simp only [BoundedMir.write, hc, hf]
  cases ho : f.heap[j]? with
  | none => simp [ho, store, address, embed]
  | some obj =>
    simp [ho, store, address, embed, embedObject, validCell]
    by_cases live : obj.alive = true
    · by_cases bound : i < obj.cells.size
      · by_cases value : n < BoundedMir.scalarBound
        · simp [live, bound, value]
        · simp [live, bound, value]
      · simp [live, bound]
    · simp [live]

/-- Abstract i64 storage words carry provenance; these constructors are not a
native bit encoding. In particular scalar object IDs cannot forge pointers.
This restricts the modeled fragment; it does not axiomatize arbitrary LLVM inttoptr. -/
abbrev Word := Cell
def pointerToWord (p : Ref) : Word := .reference p
def wordToPointer : Word → Option Ref
  | .reference p => some p
  | .scalar _ => none
@[simp] theorem pointer_roundtrip : wordToPointer (pointerToWord p) = some p := rfl
@[simp] theorem no_scalar_forgery : wordToPointer (.scalar n) = none := rfl

/-- A candidate boxed binary node has a scalar tag and two provenance words.
The two child references need not be live to transport them. -/
def node (left right : Ref) : Object :=
  ⟨true, #[some (.scalar 1), some (pointerToWord left), some (pointerToWord right)]⟩
def nilObject : Object := ⟨true, #[some (.scalar 0)]⟩
def rawNode : Object := ⟨true, #[none, none, none]⟩
def taggedNode : Object := ⟨true, #[some (.scalar 1), none, none]⟩
def leftNode (left : Ref) : Object :=
  ⟨true, #[some (.scalar 1), some (pointerToWord left), none]⟩

variable {H : Heap} {left right : Ref}

theorem object_not_null : isNull (.object H.size 0) = false := rfl

theorem node_allocate (capacity : H.size < 512)
    (budget : (H.toList.map (fun o => o.cells.size)).sum + 3 ≤ 4096) :
    allocate H 24 = some (H.push rawNode) := by
  simp [allocate, capacity, budget, rawNode, Array.replicate_succ]

theorem node_store_tag :
    store (H.push rawNode) (.object H.size 0) (.scalar 1) = some (H.push taggedNode) := by
  simp [store, address, rawNode, taggedNode, validCell, BoundedMir.scalarBound,
    Array.set!, Array.setIfInBounds, Array.set_push]

theorem node_store_left :
    store (H.push taggedNode) (.object H.size 1) (pointerToWord left) =
      some (H.push (leftNode left)) := by
  simp [store, address, taggedNode, leftNode, pointerToWord, validCell,
    Array.set!, Array.setIfInBounds, Array.set_push]

theorem node_store_right :
    store (H.push (leftNode left)) (.object H.size 2) (pointerToWord right) =
      some (H.push (node left right)) := by
  simp [store, address, leftNode, node, pointerToWord, validCell,
    Array.set!, Array.setIfInBounds, Array.set_push]

theorem node_load_children :
    loadRef (H.push (node left right)) (.object H.size 1) = some left ∧
    loadRef (H.push (node left right)) (.object H.size 2) = some right := by
  simp [loadRef, load, address, node, pointerToWord]

theorem node_release :
    release (H.push (node left right)) (.object H.size 0) =
      some (H.push {node left right with alive := false}) := by
  simp [release, node, Array.set!, Array.setIfInBounds, Array.set_push]

/-- Every old object, including its liveness and all cells, is retained at every
stage above; the fresh object's shape is arbitrary. -/
theorem external_frame (old : j < H.size) (fresh : Object) :
    (H.push fresh)[j]? = H[j]? := by simp [Array.getElem?_push, old, Nat.ne_of_lt old]

theorem released_node_unreadable :
    loadRef (H.push {node left right with alive := false}) (.object H.size i) = none := by
  simp [loadRef, load, address]

/-- An arbitrary external heap and arbitrary (possibly null/dangling) children.
This is a memory-operation sequence, not a compiled CFG or recursive Drop. -/
def nodeCycle (H : Heap) (left right : Ref) : Option (Heap × Ref × Ref) := do
  let H₁ ← allocate H 24
  let H₂ ← store H₁ (.object H.size 0) (.scalar 1)
  let H₃ ← store H₂ (.object H.size 1) (pointerToWord left)
  let H₄ ← store H₃ (.object H.size 2) (pointerToWord right)
  let l ← loadRef H₄ (.object H.size 1)
  let r ← loadRef H₄ (.object H.size 2)
  let H₅ ← release H₄ (.object H.size 0)
  pure (H₅, l, r)

theorem node_cycle (capacity : H.size < 512)
    (budget : (H.toList.map (fun o => o.cells.size)).sum + 3 ≤ 4096) :
    nodeCycle H left right = some (H.push {node left right with alive := false}, left, right) := by
  simp [nodeCycle, node_allocate capacity budget, node_store_tag, node_store_left,
    node_store_right, node_load_children.1, node_load_children.2, node_release]

theorem nil_tag : loadScalar (H.push nilObject) (.object H.size 0) = some 0 := by
  simp [loadScalar, load, address, nilObject]

theorem node_tag : loadScalar (H.push (node left right)) (.object H.size 0) = some 1 := by
  simp [loadScalar, load, address, node]

/-- Child liveness is deliberately not part of loadRef; source ownership must
supply this predicate plus bounds and initialization when a loaded child is
to be dereferenced. LiveBase alone permits a live zero-cell object. -/
def LiveBase (H : Heap) : Ref → Prop
  | .null => False
  | .object j i => i = 0 ∧ ∃ obj, H[j]? = some obj ∧ obj.alive = true

theorem store_dead (h : H[j]? = some obj) (dead : obj.alive = false) :
    store H (.object j i) v = none := by simp [store, address, h, dead]

theorem store_oob (h : H[j]? = some obj) (bound : obj.cells.size ≤ i) :
    store H (.object j i) v = none := by simp [store, address, h, Nat.not_lt.mpr bound]

end Jihoo.ReferenceHeap
