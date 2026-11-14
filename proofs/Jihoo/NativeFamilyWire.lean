import Jihoo.NativeProgramWire

/-! Canonical version-6 shared graphs with ordered definitions and raw family
declarations. This module proves bytes and graph meanings, independently of
family positivity, signature checking, native parsing and execution. -/
namespace Jihoo.NativeKernel.NativeFamilyWire

open GraphCertificates.Canonical NativeArena

structure FamilyRoots where
  data : Bool
  params : Nat
  arity : Nat
  globals : Nat
  constructors : List Nat
  deriving Repr

structure FamilyTerms where
  data : Bool
  params : Nat
  arity : Nat
  globals : Nat
  constructors : List Term
  deriving Repr

def encodeFamily (f : FamilyRoots) : Bytes :=
  encodeBool f.data ++ encodeNat f.params ++ encodeNat f.arity ++ encodeNat f.globals ++
    encodeList encodeNat f.constructors

def parseFamily : Parser FamilyRoots := fun bytes => do
  let (data, bytes) ← parseBool bytes
  let (params, bytes) ← parseNat bytes
  let (arity, bytes) ← parseNat bytes
  let (globals, bytes) ← parseNat bytes
  let (constructors, bytes) ← parseList parseNat bytes
  pure (⟨data, params, arity, globals, constructors⟩, bytes)

theorem parseFamily_encode (f : FamilyRoots) (rest : Bytes) :
    parseFamily (encodeFamily f ++ rest) = some (f, rest) := by
  simp [parseFamily, encodeFamily, List.append_assoc, parseBool_encode, parseNat_encode,
    parseList_encode encodeNat parseNat parseNat_encode]

structure Snapshot where
  definitions : List NativeProgramWire.Roots
  families : List FamilyRoots
  arena : Arena
  deriving Repr

def encodeSnapshotList (s : Snapshot) : Bytes :=
  encodeNat 6 ++ encodeList NativeProgramWire.encodeRoots s.definitions ++
    encodeList encodeFamily s.families ++ encodeList NativeWire.encodeNode s.arena.toList

def parseSnapshot : Parser Snapshot := fun bytes => do
  let (version, bytes) ← parseNat bytes
  if version ≠ 6 then none else do
    let (definitions, bytes) ← parseList NativeProgramWire.parseRoots bytes
    let (families, bytes) ← parseList parseFamily bytes
    let (nodes, bytes) ← parseList NativeWire.parseNode bytes
    pure (⟨definitions, families, nodes.toArray⟩, bytes)

theorem parseSnapshot_encode (s : Snapshot) (rest : Bytes) :
    parseSnapshot (encodeSnapshotList s ++ rest) = some (s, rest) := by
  simp [parseSnapshot, encodeSnapshotList, List.append_assoc, parseNat_encode,
    parseList_encode NativeProgramWire.encodeRoots NativeProgramWire.parseRoots
      NativeProgramWire.parseRoots_encode,
    parseList_encode encodeFamily parseFamily parseFamily_encode,
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

def allRoots (s : Snapshot) : List Nat :=
  s.definitions.flatMap (fun r => [r.typeRoot, r.valueRoot]) ++
    s.families.flatMap (·.constructors)

/-- Include every constructor and repeated declaration occurrence before any
root expansion, rather than measuring only the final requested result. -/
def expansionWork (s : Snapshot) : Option Nat := do
  let sizes ← NativeWire.measure s.arena
  let occurrences ← (allRoots s).mapM (fun root => (sizes[root]?).map Prod.fst)
  pure occurrences.sum

def structureValid (s : Snapshot) : Bool :=
  NativeWire.graphValid s.arena && decide (s.definitions.length ≤ 1024) &&
    decide (s.families.length ≤ 1024) &&
    decide ((s.families.map (fun f => f.constructors.length)).sum ≤ 4096) &&
    match expansionWork s with
    | some work => decide (work ≤ 200000)
    | none => false

theorem structureValid_graph {s : Snapshot} (h : structureValid s = true) :
    NativeWire.graphValid s.arena = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).1).1

theorem structureValid_bounds {s : Snapshot} (h : structureValid s = true) :
    s.definitions.length ≤ 1024 ∧ s.families.length ≤ 1024 ∧
      (s.families.map (fun f => f.constructors.length)).sum ≤ 4096 ∧
      ∃ work, expansionWork s = some work ∧ work ≤ 200000 := by
  have hwork := (Bool.and_eq_true_iff.mp h).2
  have rest := (Bool.and_eq_true_iff.mp h).1
  have ctors := (Bool.and_eq_true_iff.mp rest).2
  have families := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp rest).1).2
  have defs := (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp rest).1).1).2
  refine ⟨of_decide_eq_true defs, of_decide_eq_true families, of_decide_eq_true ctors, ?_⟩
  cases hw : expansionWork s with
  | none => simp [hw] at hwork
  | some work => exact ⟨work, rfl, of_decide_eq_true (by simpa only [hw] using hwork)⟩

def decodeFamily (arena : Arena) (f : FamilyRoots) : Option FamilyTerms := do
  let constructors ← f.constructors.mapM (decode 128 arena)
  pure ⟨f.data, f.params, f.arity, f.globals, constructors⟩

def RepresentsFamily (arena : Arena) (f : FamilyRoots) (t : FamilyTerms) : Prop :=
  t.data = f.data ∧ t.params = f.params ∧ t.arity = f.arity ∧ t.globals = f.globals ∧
    RepresentsList arena f.constructors t.constructors

theorem decodeConstructors_sound {arena : Arena} {roots : List Nat} {terms : List Term}
    (h : roots.mapM (decode 128 arena) = some terms) : RepresentsList arena roots terms := by
  induction roots generalizing terms with
  | nil => simp at h; subst terms; exact .nil
  | cons r rs ih =>
      cases hr : decode 128 arena r <;> cases hs : rs.mapM (decode 128 arena) <;>
        simp [List.mapM_cons, hr, hs] at h
      case some.some t ts => subst terms; exact .cons (decode_sound hr) (ih hs)

theorem decodeFamily_sound {arena : Arena} {f : FamilyRoots} {t : FamilyTerms}
    (h : decodeFamily arena f = some t) : RepresentsFamily arena f t := by
  cases hc : f.constructors.mapM (decode 128 arena) with
  | none => simp [decodeFamily, hc] at h
  | some terms =>
      simp only [decodeFamily, hc, bind, Option.bind] at h
      cases h
      exact ⟨rfl, rfl, rfl, rfl, decodeConstructors_sound hc⟩

inductive RepresentsFamilies (arena : Arena) : List FamilyRoots → List FamilyTerms → Prop where
  | nil : RepresentsFamilies arena [] []
  | cons : RepresentsFamily arena f t → RepresentsFamilies arena fs ts →
      RepresentsFamilies arena (f :: fs) (t :: ts)

theorem RepresentsFamilies.length_eq (h : RepresentsFamilies arena fs ts) : fs.length = ts.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa using congrArg Nat.succ ih

theorem decodeFamilies_sound {arena : Arena} {fs : List FamilyRoots} {ts : List FamilyTerms}
    (h : fs.mapM (decodeFamily arena) = some ts) : RepresentsFamilies arena fs ts := by
  induction fs generalizing ts with
  | nil => simp at h; subst ts; exact .nil
  | cons f fs ih =>
      cases hf : decodeFamily arena f <;> cases hs : fs.mapM (decodeFamily arena) <;>
        simp [List.mapM_cons, hf, hs] at h
      case some.some t rest => subst ts; exact .cons (decodeFamily_sound hf) (ih hs)

def decodeProgram (s : Snapshot) : Option (List Definitions.Definition × List FamilyTerms) := do
  if !structureValid s then none else do
    let definitions ← s.definitions.mapM (NativeProgramWire.decodeRoot s.arena)
    let families ← s.families.mapM (decodeFamily s.arena)
    pure (definitions, families)

theorem decodeProgram_sound {s : Snapshot} {ds : List Definitions.Definition} {fs : List FamilyTerms}
    (h : decodeProgram s = some (ds, fs)) :
    structureValid s = true ∧ NativeArena.Backward s.arena ∧
      NativeProgramWire.RepresentsDefinitions s.arena s.definitions ds ∧
      RepresentsFamilies s.arena s.families fs := by
  unfold decodeProgram at h
  split at h
  next => contradiction
  next valid =>
    have valid : structureValid s = true := by simpa using valid
    cases hd : s.definitions.mapM (NativeProgramWire.decodeRoot s.arena) <;>
      cases hf : s.families.mapM (decodeFamily s.arena) <;>
      simp [hd, hf] at h
    case some.some defs fams =>
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨valid, NativeWire.graphValid_backward (structureValid_graph valid),
        NativeProgramWire.decodeRoots_sound hd, decodeFamilies_sound hf⟩

theorem decodeProgram_bounds {s : Snapshot} {ds : List Definitions.Definition} {fs : List FamilyTerms}
    (h : decodeProgram s = some (ds, fs)) :
    ds.length ≤ 1024 ∧ fs.length ≤ 1024 ∧ s.arena.size ≤ 4096 ∧
      ∃ work, expansionWork s = some work ∧ work ≤ 200000 := by
  obtain ⟨valid, _, definitions, families⟩ := decodeProgram_sound h
  obtain ⟨hd, hf, _, work⟩ := structureValid_bounds valid
  rw [definitions.length_eq] at hd
  rw [families.length_eq] at hf
  exact ⟨hd, hf, NativeWire.graphValid_size (structureValid_graph valid), work⟩

end Jihoo.NativeKernel.NativeFamilyWire
