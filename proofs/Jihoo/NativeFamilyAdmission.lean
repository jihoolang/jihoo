import Jihoo.NativeFamilyWire
import Jihoo.NativeFamilyEnvironment

/-! Exact-byte admission of mixed checked global/family declarations. Family
signatures are recomputed from constructor types, never supplied as evidence. -/
namespace Jihoo.NativeKernel.NativeFamilyAdmission

open NativeFamilyWire

def declaration (f : FamilyTerms) : FamilyEnvironment.Declaration :=
  ⟨f.data, f.params, f.arity, f.constructors, f.globals⟩

def Sound (s : Snapshot) : Prop :=
  ∃ ds fs env, decodeProgram s = some (ds, fs) ∧
    FamilyEnvironment.ProgramChecked ds (fs.map declaration) env

def checkSnapshot (fuel : Nat) (s : Snapshot) : Bool :=
  match decodeProgram s with
  | none => false
  | some (ds, fs) => (FamilyEnvironment.checkProgram fuel ds (fs.map declaration)).isSome

theorem checkSnapshot_sound {fuel : Nat} {s : Snapshot}
    (h : checkSnapshot fuel s = true) : Sound s := by
  cases hp : decodeProgram s with
  | none => simp [checkSnapshot, hp] at h
  | some pair =>
      rcases pair with ⟨ds, fs⟩
      cases he : FamilyEnvironment.checkProgram fuel ds (fs.map declaration) with
      | none => simp [checkSnapshot, hp, he] at h
      | some env => exact ⟨ds, fs, env, hp, FamilyEnvironment.checkProgram_sound he⟩

def checkBytes (fuel : Nat) (bytes : ByteArray) : Bool :=
  match decodeSnapshot bytes with
  | none => false
  | some s => checkSnapshot fuel s

theorem checkBytes_sound {fuel : Nat} {bytes : ByteArray}
    (h : checkBytes fuel bytes = true) :
    ∃ s ds fs env, encodeSnapshot s = bytes ∧
      NativeWire.graphValid s.arena = true ∧ NativeArena.Backward s.arena ∧
      NativeProgramWire.RepresentsDefinitions s.arena s.definitions ds ∧
      RepresentsFamilies s.arena s.families fs ∧
      FamilyEnvironment.ProgramChecked ds (fs.map declaration) env := by
  cases hs : decodeSnapshot bytes with
  | none => simp [checkBytes, hs] at h
  | some s =>
      have accepted : checkSnapshot fuel s = true := by simpa only [checkBytes, hs] using h
      obtain ⟨ds, fs, env, decoded, checked⟩ := checkSnapshot_sound accepted
      obtain ⟨valid, backwards, definitions, families⟩ := decodeProgram_sound decoded
      exact ⟨s, ds, fs, env, decodeSnapshot_exact hs, structureValid_graph valid,
        backwards, definitions, families, checked⟩

theorem checkBytes_encode (fuel : Nat) (s : Snapshot) :
    checkBytes fuel (encodeSnapshot s) = checkSnapshot fuel s := by
  simp only [checkBytes, decodeSnapshot_encode]

theorem checkBytes_family_safety {fuel : Nat} {bytes : ByteArray}
    (h : checkBytes fuel bytes = true) :
    ∃ s ds fs env, encodeSnapshot s = bytes ∧
      RepresentsFamilies s.arena s.families fs ∧
      FamilyEnvironment.ProgramChecked ds (fs.map declaration) env ∧
      ∀ i entry, env.families[i]? = some entry →
        ∀ t ∈ entry.declaration.constructors,
          FamilyEnvironment.Positive i t ∧ t.Scoped 0 ∧ t.WellFormed := by
  obtain ⟨s, ds, fs, env, exactBytes, _, _, _, families, checked⟩ := checkBytes_sound h
  exact ⟨s, ds, fs, env, exactBytes, families, checked, fun _ _ found => checked.family_safety found⟩

theorem checkBytes_bounds {fuel : Nat} {bytes : ByteArray}
    (h : checkBytes fuel bytes = true) :
    ∃ (s : Snapshot) (ds : List Definitions.Definition) (fs : List FamilyTerms),
      encodeSnapshot s = bytes ∧ ds.length ≤ 1024 ∧ fs.length ≤ 1024 ∧ s.arena.size ≤ 4096 ∧
      ∃ work, expansionWork s = some work ∧ work ≤ 200000 := by
  cases hs : decodeSnapshot bytes with
  | none => simp [checkBytes, hs] at h
  | some s =>
      have accepted : checkSnapshot fuel s = true := by simpa only [checkBytes, hs] using h
      obtain ⟨ds, fs, env, decoded, checked⟩ := checkSnapshot_sound accepted
      obtain ⟨definitions, families, nodes, work⟩ := decodeProgram_bounds decoded
      exact ⟨s, ds, fs, decodeSnapshot_exact hs, definitions, families, nodes, work⟩

end Jihoo.NativeKernel.NativeFamilyAdmission
