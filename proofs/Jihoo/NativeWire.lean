import Jihoo.NativeArena
import Jihoo.NativeSchema
import Jihoo.GraphCertificateCodec

/-! Canonical full-native snapshots, distinct from the historical Raw envelope.
The wire records every constructor and complete arena without typing or
transformation certificates. Byte exactness is independent of source provenance. -/
namespace Jihoo.NativeKernel.NativeWire

open GraphCertificates.Canonical
open NativeArena

private def nodeTag : Node → Nat
  | .var _ => 0
  | .node op _ => NativeSchema.tag op

private def nodePayload : Node → List Nat
  | .var k => [k]
  | .node op _ => NativeSchema.payload op

private def nodeRefs : Node → List Nat
  | .var _ => []
  | .node _ refs => refs

private def nodeOfCode (tag : Nat) (fields refs : List Nat) : Option Node :=
  if tag = 0 then
    match fields, refs with
    | [k], [] => some (.var k)
    | _, _ => none
  else (NativeSchema.ofCode tag fields).map (fun op => .node op refs)

private theorem nodeOfCode_encode (n : Node) :
    nodeOfCode (nodeTag n) (nodePayload n) (nodeRefs n) = some n := by
  cases n with
  | var k => rfl
  | node op refs => simp [nodeOfCode, nodeTag, nodePayload, nodeRefs]

def encodeNode (n : Node) : Bytes :=
  encodeNat (nodeTag n) ++ encodeList encodeNat (nodePayload n) ++
    encodeList encodeNat (nodeRefs n)

def parseNode : Parser Node := fun bytes => do
  let (tag, bytes) ← parseNat bytes
  let (fields, bytes) ← parseList parseNat bytes
  let (refs, bytes) ← parseList parseNat bytes
  let n ← nodeOfCode tag fields refs
  pure (n, bytes)

theorem parseNode_encode (n : Node) (rest : Bytes) :
    parseNode (encodeNode n ++ rest) = some (n, rest) := by
  simp [parseNode, encodeNode, List.append_assoc, parseNat_encode,
    parseList_encode encodeNat parseNat parseNat_encode, nodeOfCode_encode]

structure Snapshot where
  ghost : Bool
  termRoot : Nat
  typeRoot : Nat
  arena : Arena
  deriving Repr

def encodeSnapshotList (s : Snapshot) : Bytes :=
  encodeNat 4 ++ encodeBool s.ghost ++ encodeNat s.termRoot ++
    encodeNat s.typeRoot ++ encodeList encodeNode s.arena.toList

def parseSnapshot : Parser Snapshot := fun bytes => do
  let (version, bytes) ← parseNat bytes
  if version ≠ 4 then none else do
    let (ghost, bytes) ← parseBool bytes
    let (termRoot, bytes) ← parseNat bytes
    let (typeRoot, bytes) ← parseNat bytes
    let (nodes, bytes) ← parseList parseNode bytes
    pure ({ ghost, termRoot, typeRoot, arena := nodes.toArray }, bytes)

theorem parseSnapshot_encode (s : Snapshot) (rest : Bytes) :
    parseSnapshot (encodeSnapshotList s ++ rest) = some (s, rest) := by
  simp [parseSnapshot, encodeSnapshotList, List.append_assoc, parseNat_encode,
    parseBool_encode, parseList_encode encodeNode parseNode parseNode_encode]

def encodeSnapshot (s : Snapshot) : ByteArray := (encodeSnapshotList s).toByteArray

def decodeSnapshot (bytes : ByteArray) : Option Snapshot := do
  let (s, []) ← parseSnapshot bytes.data.toList | none
  if encodeSnapshotList s = bytes.data.toList then some s else none

theorem decodeSnapshot_encode (s : Snapshot) :
    decodeSnapshot (encodeSnapshot s) = some s := by
  simp [decodeSnapshot, encodeSnapshot, show parseSnapshot (encodeSnapshotList s) =
    some (s, []) from by simpa using parseSnapshot_encode s []]

theorem encodeSnapshot_injective : Function.Injective encodeSnapshot := by
  intro a b h
  have same := congrArg decodeSnapshot h
  simpa only [decodeSnapshot_encode, Option.some.injEq] using same

theorem decodeSnapshot_exact {bytes : ByteArray} {s : Snapshot}
    (h : decodeSnapshot bytes = some s) : encodeSnapshot s = bytes := by
  unfold decodeSnapshot at h
  cases hp : parseSnapshot bytes.data.toList with
  | none => simp [hp] at h
  | some result =>
      rcases result with ⟨s', rest⟩
      cases rest with
      | cons b rest => simp [hp] at h
      | nil =>
          simp only [hp, bind, Option.bind] at h
          split at h
          next he =>
            cases h
            apply ByteArray.ext
            apply Array.ext'
            simpa [encodeSnapshot, List.toList_data_toByteArray] using he
          next => contradiction

/-- Measure every node before expanding either selected root. All references
must point into the preceding prefix, even in unreachable nodes. Counts and
expanded tree occurrences have separate bounds. -/
def measure (arena : Arena) : Option (Array (Nat × Nat)) :=
  arena.foldlM (fun prior n => do
    match n with
    | .var k =>
        if k < 2^32 then pure (prior.push (1, 1)) else none
    | .node op refs =>
        if !NativeSchema.payloadBounded op || refs.length != op.arity || refs.length > 4096
        then none else do
          let children ← refs.mapM (fun root => prior[root]?)
          let size := 1 + (children.map Prod.fst).sum
          let depth := 1 + (children.map Prod.snd).foldl max 0
          if size ≤ 200000 ∧ depth ≤ 128
          then pure (prior.push (size, depth)) else none) #[]

def nodeValid (id : Nat) : Node → Bool
  | .var k => decide (k < 2^32)
  | .node op refs => NativeSchema.payloadBounded op &&
      decide (refs.length = op.arity ∧ refs.length ≤ 4096) &&
      refs.all (fun ref => decide (ref < id))

def graphValid (arena : Arena) : Bool :=
  (decide (arena.size ≤ 4096) &&
    arena.toList.zipIdx.all (fun (n, id) => nodeValid id n)) && (measure arena).isSome

theorem nodeValid_backward {id : Nat} {n : Node} (h : nodeValid id n = true) :
    ∀ ref ∈ n.references, ref < id := by
  cases n with
  | var k => simp [Node.references]
  | node op refs =>
      intro ref member
      exact of_decide_eq_true ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2) ref member)

theorem graphValid_node {arena : Arena} {id : Nat} {n : Node}
    (h : graphValid arena = true) (lookup : arena[id]? = some n) : nodeValid id n = true := by
  have nodes := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  apply (List.all_eq_true.mp nodes) (n, id)
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  simpa using lookup

theorem graphValid_backward {arena : Arena} (h : graphValid arena = true) : Backward arena := by
  intro id n lookup ref member
  exact nodeValid_backward (graphValid_node h lookup) ref member

theorem graphValid_size {arena : Arena} (h : graphValid arena = true) : arena.size ≤ 4096 :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

theorem graphValid_operator {arena : Arena} {id : Nat} {op : Op} {refs : List Nat}
    (h : graphValid arena = true) (lookup : arena[id]? = some (.node op refs)) :
    NativeSchema.payloadBounded op = true ∧ refs.length = op.arity ∧ refs.length ≤ 4096 := by
  have hn := (Bool.and_eq_true_iff.mp (graphValid_node h lookup)).1
  exact ⟨(Bool.and_eq_true_iff.mp hn).1,
    (of_decide_eq_true (Bool.and_eq_true_iff.mp hn).2).1,
    (of_decide_eq_true (Bool.and_eq_true_iff.mp hn).2).2⟩

end Jihoo.NativeKernel.NativeWire
