import Jihoo.NativeProgramWire
import Jihoo.NativeGlobalEnvironment

/-! Whole-program admission binds an ordered checked global environment to
the exact canonical input bytes and shared graph. Native execution refinement
and checked inductive signatures remain separate obligations. -/
namespace Jihoo.NativeKernel.NativeProgramAdmission

open NativeProgramWire

def Sound (s : Snapshot) : Prop :=
  ∃ ds env, decodeDefinitions s = some ds ∧
    GlobalEnvironment.SequentiallyChecked ds env

def checkSnapshot (fuel : Nat) (s : Snapshot) : Bool :=
  match decodeDefinitions s with
  | none => false
  | some ds => (GlobalEnvironment.checkProgram fuel ds).isSome

theorem checkSnapshot_sound {fuel : Nat} {s : Snapshot}
    (h : checkSnapshot fuel s = true) : Sound s := by
  cases hd : decodeDefinitions s with
  | none => simp [checkSnapshot, hd] at h
  | some ds =>
      cases he : GlobalEnvironment.checkProgram fuel ds with
      | none => simp [checkSnapshot, hd, he] at h
      | some env => exact ⟨ds, env, hd, GlobalEnvironment.checkProgram_sound he⟩

def checkBytes (fuel : Nat) (bytes : ByteArray) : Bool :=
  match decodeSnapshot bytes with
  | none => false
  | some s => checkSnapshot fuel s

theorem checkBytes_sound {fuel : Nat} {bytes : ByteArray}
    (h : checkBytes fuel bytes = true) :
    ∃ s ds env, encodeSnapshot s = bytes ∧
      NativeWire.graphValid s.arena = true ∧ NativeArena.Backward s.arena ∧
      RepresentsDefinitions s.arena s.declarations ds ∧
      GlobalEnvironment.SequentiallyChecked ds env := by
  cases hs : decodeSnapshot bytes with
  | none => simp [checkBytes, hs] at h
  | some s =>
      have accepted : checkSnapshot fuel s = true := by simpa only [checkBytes, hs] using h
      obtain ⟨ds, env, decoded, checked⟩ := checkSnapshot_sound accepted
      obtain ⟨valid, backwards, meaning⟩ := decodeDefinitions_sound decoded
      exact ⟨s, ds, env, decodeSnapshot_exact hs, valid, backwards, meaning, checked⟩

theorem checkBytes_encode (fuel : Nat) (s : Snapshot) :
    checkBytes fuel (encodeSnapshot s) = checkSnapshot fuel s := by
  simp only [checkBytes, decodeSnapshot_encode]

/-- Every interpreted declaration has independent formation, the body mode
derived from its sort, and genuine local closure, without global axioms. -/
theorem checkBytes_declarations {fuel : Nat} {bytes : ByteArray}
    (h : checkBytes fuel bytes = true) :
    ∃ s ds env, encodeSnapshot s = bytes ∧
      RepresentsDefinitions s.arena s.declarations ds ∧
      GlobalEnvironment.SequentiallyChecked ds env ∧
      ∀ d ∈ env.toList, Definitions.Valid d ∧
        GlobalEnvironment.GlobalFree d.type ∧ GlobalEnvironment.GlobalFree d.value ∧
        d.type.Scoped 0 ∧ d.value.Scoped 0 ∧ d.type.WellFormed ∧ d.value.WellFormed := by
  obtain ⟨s, ds, env, exactBytes, _, _, meaning, checked⟩ := checkBytes_sound h
  refine ⟨s, ds, env, exactBytes, meaning, checked, ?_⟩
  intro d member
  have free := checked.globalFree d member
  exact ⟨checked.valid d member, free.1, free.2, checked.closed d member⟩

theorem checkBytes_no_forward {fuel : Nat} {bytes : ByteArray}
    (h : checkBytes fuel bytes = true) :
    ∃ s ds, encodeSnapshot s = bytes ∧
      RepresentsDefinitions s.arena s.declarations ds ∧
      ∀ i d, ds[i]? = some d →
        GlobalEnvironment.Before i d.type ∧ GlobalEnvironment.Before i d.value := by
  obtain ⟨s, ds, env, exactBytes, _, _, meaning, checked⟩ := checkBytes_sound h
  exact ⟨s, ds, exactBytes, meaning, fun _ _ found => checked.ordered found⟩

theorem checkBytes_bounds {fuel : Nat} {bytes : ByteArray}
    (h : checkBytes fuel bytes = true) :
    ∃ (s : Snapshot) (ds : List Definitions.Definition),
      encodeSnapshot s = bytes ∧ ds.length ≤ 1024 ∧ s.arena.size ≤ 4096 ∧
      ∃ work, expansionWork s = some work ∧ work ≤ 200000 := by
  cases hs : decodeSnapshot bytes with
  | none => simp [checkBytes, hs] at h
  | some s =>
      have accepted : checkSnapshot fuel s = true := by simpa only [checkBytes, hs] using h
      obtain ⟨ds, env, decoded, checked⟩ := checkSnapshot_sound accepted
      obtain ⟨declarations, nodes, work⟩ := decodeDefinitions_bounds decoded
      exact ⟨s, ds, decodeSnapshot_exact hs, declarations, nodes, work⟩

end Jihoo.NativeKernel.NativeProgramAdmission
