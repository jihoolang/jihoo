import Jihoo.NativeDefinitions

/-! Canonical whole-program envelopes for ordered native declarations. Modes
are computed from declaration types, never supplied by the input. This codec
does not establish execution fidelity of the native exporter. -/
namespace Jihoo.NativeKernel.NativeProgramWire

open GraphCertificates.Canonical NativeArena NativeWire

structure Roots where
  typeRoot : Nat
  valueRoot : Nat
  deriving Repr, DecidableEq

def encodeRoots (r : Roots) : Bytes := encodeNat r.typeRoot ++ encodeNat r.valueRoot

def parseRoots : Parser Roots := fun bytes => do
  let (typeRoot, bytes) ← parseNat bytes
  let (valueRoot, bytes) ← parseNat bytes
  pure (⟨typeRoot, valueRoot⟩, bytes)

theorem parseRoots_encode (r : Roots) (rest : Bytes) :
    parseRoots (encodeRoots r ++ rest) = some (r, rest) := by
  simp [parseRoots, encodeRoots, List.append_assoc, parseNat_encode]

structure Snapshot where
  declarations : List Roots
  arena : Arena
  deriving Repr

def encodeSnapshotList (s : Snapshot) : Bytes :=
  encodeNat 5 ++ encodeList encodeRoots s.declarations ++ encodeList NativeWire.encodeNode s.arena.toList

def parseSnapshot : Parser Snapshot := fun bytes => do
  let (version, bytes) ← parseNat bytes
  if version ≠ 5 then none else do
    let (declarations, bytes) ← parseList parseRoots bytes
    let (nodes, bytes) ← parseList NativeWire.parseNode bytes
    pure ({ declarations, arena := nodes.toArray }, bytes)

theorem parseSnapshot_encode (s : Snapshot) (rest : Bytes) :
    parseSnapshot (encodeSnapshotList s ++ rest) = some (s, rest) := by
  simp [parseSnapshot, encodeSnapshotList, List.append_assoc, parseNat_encode,
    parseList_encode encodeRoots parseRoots parseRoots_encode,
    parseList_encode NativeWire.encodeNode NativeWire.parseNode NativeWire.parseNode_encode]

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

/-- Aggregate root expansion is capped before decoding any declaration. Shared
roots count once per occurrence, including repeated declaration references. -/
def expansionWork (s : Snapshot) : Option Nat := do
  let sizes ← measure s.arena
  let pairs ← s.declarations.mapM (fun r => do
    let ty ← sizes[r.typeRoot]?
    let value ← sizes[r.valueRoot]?
    pure (ty.1 + value.1))
  pure pairs.sum

def structureValid (s : Snapshot) : Bool :=
  graphValid s.arena && decide (s.declarations.length ≤ 1024) &&
    match expansionWork s with
    | some work => decide (work ≤ 200000)
    | none => false

theorem structureValid_graph {s : Snapshot} (h : structureValid s = true) :
    graphValid s.arena = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

theorem structureValid_declarations {s : Snapshot} (h : structureValid s = true) :
    s.declarations.length ≤ 1024 :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2

theorem structureValid_expansion {s : Snapshot} (h : structureValid s = true) :
    ∃ work, expansionWork s = some work ∧ work ≤ 200000 := by
  have hw := (Bool.and_eq_true_iff.mp h).2
  cases he : expansionWork s with
  | none => simp [he] at hw
  | some work => exact ⟨work, rfl, of_decide_eq_true (by simpa only [he] using hw)⟩

def decodeRoot (arena : Arena) (r : Roots) : Option Definitions.Definition := do
  let type ← decode 128 arena r.typeRoot
  let value ← decode 128 arena r.valueRoot
  pure ⟨type, value⟩

def RepresentsDefinition (arena : Arena) (r : Roots) (d : Definitions.Definition) : Prop :=
  Represents arena r.typeRoot d.type ∧ Represents arena r.valueRoot d.value

theorem decodeRoot_sound {arena : Arena} {r : Roots} {d : Definitions.Definition}
    (h : decodeRoot arena r = some d) : RepresentsDefinition arena r d := by
  cases ht : decode 128 arena r.typeRoot <;>
    cases hv : decode 128 arena r.valueRoot <;> simp [decodeRoot, ht, hv] at h
  case some.some type value =>
    cases h
    exact ⟨decode_sound ht, decode_sound hv⟩

inductive RepresentsDefinitions (arena : Arena) : List Roots → List Definitions.Definition → Prop where
  | nil : RepresentsDefinitions arena [] []
  | cons : RepresentsDefinition arena r d → RepresentsDefinitions arena rs ds →
      RepresentsDefinitions arena (r :: rs) (d :: ds)

theorem RepresentsDefinitions.length_eq (h : RepresentsDefinitions arena rs ds) :
    rs.length = ds.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa using congrArg Nat.succ ih

theorem decodeRoots_sound {arena : Arena} {rs : List Roots} {ds : List Definitions.Definition}
    (h : rs.mapM (decodeRoot arena) = some ds) :
    RepresentsDefinitions arena rs ds := by
  induction rs generalizing ds with
  | nil => simp at h; subst ds; exact .nil
  | cons r rs ih =>
      cases hd : decodeRoot arena r <;> cases hs : rs.mapM (decodeRoot arena) <;>
        simp [List.mapM_cons, hd, hs] at h
      case some.some d tail =>
        subst ds
        exact .cons (decodeRoot_sound hd) (ih hs)

def decodeDefinitions (s : Snapshot) : Option (List Definitions.Definition) :=
  if structureValid s then s.declarations.mapM (decodeRoot s.arena) else none

theorem decodeDefinitions_structure {s : Snapshot} {ds : List Definitions.Definition}
    (h : decodeDefinitions s = some ds) : structureValid s = true := by
  unfold decodeDefinitions at h
  split at h
  next valid => exact valid
  next => contradiction

theorem decodeDefinitions_sound {s : Snapshot} {ds : List Definitions.Definition}
    (h : decodeDefinitions s = some ds) :
    graphValid s.arena = true ∧ Backward s.arena ∧
      RepresentsDefinitions s.arena s.declarations ds := by
  unfold decodeDefinitions at h
  split at h
  next valid =>
    have graph := structureValid_graph valid
    exact ⟨graph, graphValid_backward graph, decodeRoots_sound h⟩
  next => contradiction

theorem decodeDefinitions_length {s : Snapshot} {ds : List Definitions.Definition}
    (h : decodeDefinitions s = some ds) : ds.length = s.declarations.length :=
  (decodeDefinitions_sound h).2.2.length_eq.symm

theorem decodeDefinitions_bounds {s : Snapshot} {ds : List Definitions.Definition}
    (h : decodeDefinitions s = some ds) :
    ds.length ≤ 1024 ∧ s.arena.size ≤ 4096 ∧
      ∃ work, expansionWork s = some work ∧ work ≤ 200000 := by
  have valid := decodeDefinitions_structure h
  exact ⟨by rw [decodeDefinitions_length h]; exact structureValid_declarations valid,
    graphValid_size (structureValid_graph valid), structureValid_expansion valid⟩

end Jihoo.NativeKernel.NativeProgramWire
