import Jihoo.NativeAdmission

/-! Checked closed declarations derive their body mode from the declared type's
sort, as Core.extend does. An externally recorded observation mode is not an
authority for accepting runtime use of erased values. Globals and families need
an additional checked program environment; this file does not assume one. -/
namespace Jihoo.NativeKernel.Definitions

open NativeWire NativeArena

/-- Evidence declarations are checked in ghost mode; data declarations in code. -/
def bodyMode : SortTag → Bool
  | .prop => true
  | .type _ => false

structure Definition where
  type : Term
  value : Term
  deriving Repr

/-- Independent formation and body typing, with a mode computed from the sort. -/
def Valid (d : Definition) : Prop :=
  ∃ sort : SortTag, HasType [] true d.type sort.term ∧
    HasType [] (bodyMode sort) d.value d.type

def check (fuel : Nat) (d : Definition) : Bool :=
  match Checker.sort fuel [] d.type with
  | some sort => Checker.check fuel [] (bodyMode sort) d.value d.type
  | none => false

theorem check_sound {fuel : Nat} {d : Definition} (h : check fuel d = true) : Valid d := by
  cases hs : Checker.sort fuel [] d.type with
  | none => simp [check, hs] at h
  | some sort =>
      exact ⟨sort, Checker.sort_sound hs,
        Checker.check_sound (by simpa only [check, hs] using h)⟩

theorem check_closed {fuel : Nat} {d : Definition} (h : check fuel d = true) :
    d.type.Scoped 0 ∧ d.value.Scoped 0 ∧ d.type.WellFormed ∧ d.value.WellFormed := by
  obtain ⟨_, formed, typed⟩ := check_sound h
  exact ⟨formed.term_scoped, typed.term_scoped, formed.term_wellFormed, typed.term_wellFormed⟩

/-- The snapshot's recorded operation mode is deliberately not used to choose
whether a declaration's value may run. That choice follows from type formation. -/
def checkSnapshot (fuel : Nat) (s : Snapshot) : Bool :=
  graphValid s.arena &&
    match decode 128 s.arena s.termRoot, decode 128 s.arena s.typeRoot with
    | some value, some type => check fuel ⟨type, value⟩
    | _, _ => false

theorem checkSnapshot_mode (fuel : Nat) (s : Snapshot) (ghost : Bool) :
    checkSnapshot fuel { s with ghost } = checkSnapshot fuel s := rfl

theorem checkSnapshot_sound {fuel : Nat} {s : Snapshot}
    (h : checkSnapshot fuel s = true) :
    ∃ d : Definition, decode 128 s.arena s.termRoot = some d.value ∧
      decode 128 s.arena s.typeRoot = some d.type ∧ Valid d := by
  have hc := (Bool.and_eq_true_iff.mp h).2
  cases hv : decode 128 s.arena s.termRoot <;>
    cases ht : decode 128 s.arena s.typeRoot <;>
    simp only [hv, ht, Bool.false_eq_true] at hc
  case some.some value type => exact ⟨⟨type, value⟩, rfl, rfl, check_sound hc⟩

def checkBytes (fuel : Nat) (bytes : ByteArray) : Bool :=
  match decodeSnapshot bytes with
  | some s => checkSnapshot fuel s
  | none => false

theorem checkBytes_sound {fuel : Nat} {bytes : ByteArray}
    (h : checkBytes fuel bytes = true) :
    ∃ s : Snapshot, ∃ d : Definition, encodeSnapshot s = bytes ∧
      graphValid s.arena = true ∧ Backward s.arena ∧
      Represents s.arena s.termRoot d.value ∧ Represents s.arena s.typeRoot d.type ∧ Valid d := by
  cases hs : decodeSnapshot bytes with
  | none => simp [checkBytes, hs] at h
  | some s =>
      have accepted : checkSnapshot fuel s = true := by simpa only [checkBytes, hs] using h
      have validGraph := (Bool.and_eq_true_iff.mp accepted).1
      obtain ⟨d, hv, ht, valid⟩ := checkSnapshot_sound accepted
      exact ⟨s, d, decodeSnapshot_exact hs, validGraph, graphValid_backward validGraph,
        decode_sound hv, decode_sound ht, valid⟩

theorem checkBytes_encode (fuel : Nat) (s : Snapshot) :
    checkBytes fuel (encodeSnapshot s) = checkSnapshot fuel s := by
  simp only [checkBytes, decodeSnapshot_encode]

end Jihoo.NativeKernel.Definitions
