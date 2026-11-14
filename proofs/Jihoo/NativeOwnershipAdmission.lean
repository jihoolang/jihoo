import Jihoo.NativeEnvironmentCheckerSoundness
import Jihoo.NativeOwnership
import Jihoo.NativeWire

/-! A resource-gated entry point for closed native declarations. The executable
checker derives the body mode from the declared sort and always checks code
with depth zero and empty outer resource lists. Raw environment records alone
are not a checked global/family history. This module certifies typing relative
to the supplied environment and the separate projected-control resource gate. -/
namespace Jihoo.NativeKernel.NativeOwnershipAdmission

abbrev Declaration := Environment.GlobalDeclaration

/-- Core.extend runs evidence only in ghost mode. -/
def bodyMode : SortTag → Bool
  | .prop => true
  | .type _ => false

/-- Formation, mode-correct typing, and closed resource safety for code. -/
def Valid (env : Environment) (d : Declaration) : Prop :=
  ∃ sort : SortTag, Environment.HasType env [] true d.type sort.term ∧
    Environment.HasType env [] (bodyMode sort) d.value d.type ∧
    (bodyMode sort = false → NativeOwnership.ClosedSafe d.value)

/-- This is the declaration admission entry point. `infer` remains a typing
operation; a code declaration must also pass the independent quantity check. -/
def check (fuel quantityFuel : Nat) (env : Environment) (d : Declaration) : Bool :=
  match Environment.Checker.sort fuel env [] d.type with
  | none => false
  | some sort => Environment.Checker.check fuel env [] (bodyMode sort) d.value d.type &&
      NativeOwnership.declarationGate quantityFuel (bodyMode sort) d.value

theorem check_sound (h : check fuel quantityFuel env d = true) : Valid env d := by
  cases hs : Environment.Checker.sort fuel env [] d.type with
  | none => simp [check, hs] at h
  | some sort =>
      have accepted : Environment.Checker.check fuel env [] (bodyMode sort) d.value d.type = true ∧
          NativeOwnership.declarationGate quantityFuel (bodyMode sort) d.value = true := by
        simpa only [check, hs, Bool.and_eq_true] using h
      refine ⟨sort, Environment.Checker.sort_sound hs, Environment.Checker.check_sound accepted.1, ?_⟩
      intro code
      rw [code] at accepted
      exact NativeOwnership.declarationGate_code accepted.2

/-- No caller can select ghost mode to avoid the code declaration gate. -/
theorem checked_code_gate (h : check fuel quantityFuel env d = true)
    (sort : Environment.Checker.sort fuel env [] d.type = some (.type level)) :
    NativeOwnership.checkClosed quantityFuel d.value = true := by
  have both := h
  simp only [check, sort, bodyMode, NativeOwnership.declarationGate, Bool.false_or,
    Bool.and_eq_true] at both
  exact both.2

open NativeWire NativeArena

def checkSnapshot (fuel quantityFuel : Nat) (env : Environment) (s : Snapshot) : Bool :=
  graphValid s.arena &&
    match decode 128 s.arena s.termRoot, decode 128 s.arena s.typeRoot with
    | some value, some type => check fuel quantityFuel env ⟨type, value⟩
    | _, _ => false

/-- The recorded observation mode is not authority for declaration admission. -/
theorem checkSnapshot_mode (fuel quantityFuel : Nat) (env : Environment) (s : Snapshot) (ghost : Bool) :
    checkSnapshot fuel quantityFuel env { s with ghost } = checkSnapshot fuel quantityFuel env s := rfl

theorem checkSnapshot_sound (h : checkSnapshot fuel quantityFuel env s = true) :
    ∃ d : Declaration, decode 128 s.arena s.termRoot = some d.value ∧
      decode 128 s.arena s.typeRoot = some d.type ∧ Valid env d := by
  have accepted := (Bool.and_eq_true_iff.mp h).2
  cases hv : decode 128 s.arena s.termRoot <;>
    cases ht : decode 128 s.arena s.typeRoot <;>
    simp only [hv, ht, Bool.false_eq_true] at accepted
  case some.some value type => exact ⟨⟨type, value⟩, rfl, rfl, check_sound accepted⟩

def checkBytes (fuel quantityFuel : Nat) (env : Environment) (bytes : ByteArray) : Bool :=
  match decodeSnapshot bytes with
  | none => false
  | some s => checkSnapshot fuel quantityFuel env s

theorem checkBytes_sound (h : checkBytes fuel quantityFuel env bytes = true) :
    ∃ s : Snapshot, ∃ d : Declaration, encodeSnapshot s = bytes ∧
      graphValid s.arena = true ∧ Backward s.arena ∧
      Represents s.arena s.termRoot d.value ∧ Represents s.arena s.typeRoot d.type ∧ Valid env d := by
  cases hs : decodeSnapshot bytes with
  | none => simp [checkBytes, hs] at h
  | some s =>
      have accepted : checkSnapshot fuel quantityFuel env s = true := by
        simpa only [checkBytes, hs] using h
      have graph := (Bool.and_eq_true_iff.mp accepted).1
      obtain ⟨d, value, type, checked⟩ := checkSnapshot_sound accepted
      exact ⟨s, d, decodeSnapshot_exact hs, graph, graphValid_backward graph,
        decode_sound value, decode_sound type, checked⟩

theorem checkBytes_encode (fuel quantityFuel : Nat) (env : Environment) (s : Snapshot) :
    checkBytes fuel quantityFuel env (encodeSnapshot s) = checkSnapshot fuel quantityFuel env s := by
  simp only [checkBytes, decodeSnapshot_encode]

end Jihoo.NativeKernel.NativeOwnershipAdmission
