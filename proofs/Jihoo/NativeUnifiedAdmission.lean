import Jihoo.NativeUnifiedProgram
import Jihoo.NativeFamilyWire

/-! Exact-byte entry point for the unified mixed checker. Decoding supplies
raw declarations only: positivity, dependent signatures, storage metadata,
sort-derived body modes and runtime quantities are recomputed in sequence. -/
namespace Jihoo.NativeKernel.NativeUnifiedAdmission
open NativeFamilyWire

def declaration (source : FamilyTerms) : Environment.FamilyDeclaration :=
  ⟨source.data, source.params, source.arity, source.constructors, source.globals⟩

def checkSnapshot (fuel quantityFuel : Nat) (snapshot : Snapshot) : Bool :=
  match decodeProgram snapshot with
  | none => false
  | some (definitions, families) =>
      (UnifiedProgram.checkProgram fuel quantityFuel definitions (families.map declaration)).isSome

theorem checkSnapshot_sound (accepted : checkSnapshot fuel quantityFuel snapshot = true) :
    ∃ definitions families env, decodeProgram snapshot = some (definitions, families) ∧
      UnifiedProgram.UnifiedProgramChecked definitions (families.map declaration) env ∧
      UnifiedProgram.EnvWellFormed env := by
  cases decoded : decodeProgram snapshot with
  | none => simp [checkSnapshot, decoded] at accepted
  | some pair =>
      rcases pair with ⟨definitions, families⟩
      cases checked : UnifiedProgram.checkProgram fuel quantityFuel definitions (families.map declaration) with
      | none => simp [checkSnapshot, decoded, checked] at accepted
      | some env =>
          have history := UnifiedProgram.checkProgram_sound checked
          exact ⟨definitions, families, env, rfl, history, history.wellFormed⟩

def checkBytes (fuel quantityFuel : Nat) (bytes : ByteArray) : Bool :=
  match decodeSnapshot bytes with
  | none => false
  | some snapshot => checkSnapshot fuel quantityFuel snapshot

theorem checkBytes_sound (accepted : checkBytes fuel quantityFuel bytes = true) :
    ∃ snapshot definitions families env, encodeSnapshot snapshot = bytes ∧
      NativeWire.graphValid snapshot.arena = true ∧ NativeArena.Backward snapshot.arena ∧
      NativeProgramWire.RepresentsDefinitions snapshot.arena snapshot.definitions definitions ∧
      RepresentsFamilies snapshot.arena snapshot.families families ∧
      UnifiedProgram.UnifiedProgramChecked definitions (families.map declaration) env ∧
      UnifiedProgram.EnvWellFormed env := by
  cases decoded : decodeSnapshot bytes with
  | none => simp [checkBytes, decoded] at accepted
  | some snapshot =>
      have checked : checkSnapshot fuel quantityFuel snapshot = true := by
        simpa only [checkBytes, decoded] using accepted
      obtain ⟨definitions, families, env, source, history, wellFormed⟩ := checkSnapshot_sound checked
      obtain ⟨valid, backwards, definitionsRepresented, familiesRepresented⟩ := decodeProgram_sound source
      exact ⟨snapshot, definitions, families, env, decodeSnapshot_exact decoded,
        structureValid_graph valid, backwards, definitionsRepresented, familiesRepresented, history, wellFormed⟩

theorem checkBytes_encode (fuel quantityFuel : Nat) (snapshot : Snapshot) :
    checkBytes fuel quantityFuel (encodeSnapshot snapshot) = checkSnapshot fuel quantityFuel snapshot := by
  simp only [checkBytes, decodeSnapshot_encode]

end Jihoo.NativeKernel.NativeUnifiedAdmission
