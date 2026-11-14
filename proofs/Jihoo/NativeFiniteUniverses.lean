import Jihoo.NativeTyping

-- Host universe syntax needs room above the native administrative top.
set_option maxUniverseOffset 40
/-! Concrete finite host universes for the native contextual model. Native
universe inputs remain below32; Universe32 is administrative. Host level33
only classifies that administrative object and is not an extra native input. -/
namespace Jihoo.NativeKernel.Environment.Semantics.Finite

inductive LevelSort where
  | proposition
  | type (level : Fin 34)
  deriving DecidableEq

def LevelSort.native : LevelSort → SortTag
  | .proposition => .prop
  | .type level => .type level.val

def LevelSort.pi : LevelSort → LevelSort → LevelSort
  | _, .proposition => .proposition
  | .proposition, .type level => .type level
  | .type first, .type second => .type ⟨max first.val second.val,by omega⟩

theorem LevelSort.pi_native (domain codomain : LevelSort) :
    (domain.pi codomain).native = domain.native.pi codomain.native := by
  cases domain <;> cases codomain <;> rfl

inductive Universe : LevelSort → Type 35 where
  | proposition (truth : Prop) : Universe .proposition
  | type0 (carrier : Type 0) : Universe (.type ⟨0,by decide⟩)
  | type1 (carrier : Type 1) : Universe (.type ⟨1,by decide⟩)
  | type2 (carrier : Type 2) : Universe (.type ⟨2,by decide⟩)
  | type3 (carrier : Type 3) : Universe (.type ⟨3,by decide⟩)
  | type4 (carrier : Type 4) : Universe (.type ⟨4,by decide⟩)
  | type5 (carrier : Type 5) : Universe (.type ⟨5,by decide⟩)
  | type6 (carrier : Type 6) : Universe (.type ⟨6,by decide⟩)
  | type7 (carrier : Type 7) : Universe (.type ⟨7,by decide⟩)
  | type8 (carrier : Type 8) : Universe (.type ⟨8,by decide⟩)
  | type9 (carrier : Type 9) : Universe (.type ⟨9,by decide⟩)
  | type10 (carrier : Type 10) : Universe (.type ⟨10,by decide⟩)
  | type11 (carrier : Type 11) : Universe (.type ⟨11,by decide⟩)
  | type12 (carrier : Type 12) : Universe (.type ⟨12,by decide⟩)
  | type13 (carrier : Type 13) : Universe (.type ⟨13,by decide⟩)
  | type14 (carrier : Type 14) : Universe (.type ⟨14,by decide⟩)
  | type15 (carrier : Type 15) : Universe (.type ⟨15,by decide⟩)
  | type16 (carrier : Type 16) : Universe (.type ⟨16,by decide⟩)
  | type17 (carrier : Type 17) : Universe (.type ⟨17,by decide⟩)
  | type18 (carrier : Type 18) : Universe (.type ⟨18,by decide⟩)
  | type19 (carrier : Type 19) : Universe (.type ⟨19,by decide⟩)
  | type20 (carrier : Type 20) : Universe (.type ⟨20,by decide⟩)
  | type21 (carrier : Type 21) : Universe (.type ⟨21,by decide⟩)
  | type22 (carrier : Type 22) : Universe (.type ⟨22,by decide⟩)
  | type23 (carrier : Type 23) : Universe (.type ⟨23,by decide⟩)
  | type24 (carrier : Type 24) : Universe (.type ⟨24,by decide⟩)
  | type25 (carrier : Type 25) : Universe (.type ⟨25,by decide⟩)
  | type26 (carrier : Type 26) : Universe (.type ⟨26,by decide⟩)
  | type27 (carrier : Type 27) : Universe (.type ⟨27,by decide⟩)
  | type28 (carrier : Type 28) : Universe (.type ⟨28,by decide⟩)
  | type29 (carrier : Type 29) : Universe (.type ⟨29,by decide⟩)
  | type30 (carrier : Type 30) : Universe (.type ⟨30,by decide⟩)
  | type31 (carrier : Type 31) : Universe (.type ⟨31,by decide⟩)
  | type32 (carrier : Type 32) : Universe (.type ⟨32,by decide⟩)
  | type33 (carrier : Type 33) : Universe (.type ⟨33,by decide⟩)

def Carrier : {sort : LevelSort} → Universe sort → Type 34
  | _, .proposition truth => ULift.{34} (PLift truth)
  | _, .type0 carrier => ULift.{34} carrier
  | _, .type1 carrier => ULift.{34} carrier
  | _, .type2 carrier => ULift.{34} carrier
  | _, .type3 carrier => ULift.{34} carrier
  | _, .type4 carrier => ULift.{34} carrier
  | _, .type5 carrier => ULift.{34} carrier
  | _, .type6 carrier => ULift.{34} carrier
  | _, .type7 carrier => ULift.{34} carrier
  | _, .type8 carrier => ULift.{34} carrier
  | _, .type9 carrier => ULift.{34} carrier
  | _, .type10 carrier => ULift.{34} carrier
  | _, .type11 carrier => ULift.{34} carrier
  | _, .type12 carrier => ULift.{34} carrier
  | _, .type13 carrier => ULift.{34} carrier
  | _, .type14 carrier => ULift.{34} carrier
  | _, .type15 carrier => ULift.{34} carrier
  | _, .type16 carrier => ULift.{34} carrier
  | _, .type17 carrier => ULift.{34} carrier
  | _, .type18 carrier => ULift.{34} carrier
  | _, .type19 carrier => ULift.{34} carrier
  | _, .type20 carrier => ULift.{34} carrier
  | _, .type21 carrier => ULift.{34} carrier
  | _, .type22 carrier => ULift.{34} carrier
  | _, .type23 carrier => ULift.{34} carrier
  | _, .type24 carrier => ULift.{34} carrier
  | _, .type25 carrier => ULift.{34} carrier
  | _, .type26 carrier => ULift.{34} carrier
  | _, .type27 carrier => ULift.{34} carrier
  | _, .type28 carrier => ULift.{34} carrier
  | _, .type29 carrier => ULift.{34} carrier
  | _, .type30 carrier => ULift.{34} carrier
  | _, .type31 carrier => ULift.{34} carrier
  | _, .type32 carrier => ULift.{34} carrier
  | _, .type33 carrier => ULift.{34} carrier

def decode0 : Universe (.type ⟨0,by decide⟩) → Type 0
  | .type0 carrier => carrier

theorem encode_decode0 (code : Universe (.type ⟨0,by decide⟩)) : Universe.type0 (decode0 code) = code := by
  cases code
  rfl

def decode1 : Universe (.type ⟨1,by decide⟩) → Type 1
  | .type1 carrier => carrier

theorem encode_decode1 (code : Universe (.type ⟨1,by decide⟩)) : Universe.type1 (decode1 code) = code := by
  cases code
  rfl

def decode2 : Universe (.type ⟨2,by decide⟩) → Type 2
  | .type2 carrier => carrier

theorem encode_decode2 (code : Universe (.type ⟨2,by decide⟩)) : Universe.type2 (decode2 code) = code := by
  cases code
  rfl

def decode3 : Universe (.type ⟨3,by decide⟩) → Type 3
  | .type3 carrier => carrier

theorem encode_decode3 (code : Universe (.type ⟨3,by decide⟩)) : Universe.type3 (decode3 code) = code := by
  cases code
  rfl

def decode4 : Universe (.type ⟨4,by decide⟩) → Type 4
  | .type4 carrier => carrier

theorem encode_decode4 (code : Universe (.type ⟨4,by decide⟩)) : Universe.type4 (decode4 code) = code := by
  cases code
  rfl

def decode5 : Universe (.type ⟨5,by decide⟩) → Type 5
  | .type5 carrier => carrier

theorem encode_decode5 (code : Universe (.type ⟨5,by decide⟩)) : Universe.type5 (decode5 code) = code := by
  cases code
  rfl

def decode6 : Universe (.type ⟨6,by decide⟩) → Type 6
  | .type6 carrier => carrier

theorem encode_decode6 (code : Universe (.type ⟨6,by decide⟩)) : Universe.type6 (decode6 code) = code := by
  cases code
  rfl

def decode7 : Universe (.type ⟨7,by decide⟩) → Type 7
  | .type7 carrier => carrier

theorem encode_decode7 (code : Universe (.type ⟨7,by decide⟩)) : Universe.type7 (decode7 code) = code := by
  cases code
  rfl

def decode8 : Universe (.type ⟨8,by decide⟩) → Type 8
  | .type8 carrier => carrier

theorem encode_decode8 (code : Universe (.type ⟨8,by decide⟩)) : Universe.type8 (decode8 code) = code := by
  cases code
  rfl

def decode9 : Universe (.type ⟨9,by decide⟩) → Type 9
  | .type9 carrier => carrier

theorem encode_decode9 (code : Universe (.type ⟨9,by decide⟩)) : Universe.type9 (decode9 code) = code := by
  cases code
  rfl

def decode10 : Universe (.type ⟨10,by decide⟩) → Type 10
  | .type10 carrier => carrier

theorem encode_decode10 (code : Universe (.type ⟨10,by decide⟩)) : Universe.type10 (decode10 code) = code := by
  cases code
  rfl

def decode11 : Universe (.type ⟨11,by decide⟩) → Type 11
  | .type11 carrier => carrier

theorem encode_decode11 (code : Universe (.type ⟨11,by decide⟩)) : Universe.type11 (decode11 code) = code := by
  cases code
  rfl

def decode12 : Universe (.type ⟨12,by decide⟩) → Type 12
  | .type12 carrier => carrier

theorem encode_decode12 (code : Universe (.type ⟨12,by decide⟩)) : Universe.type12 (decode12 code) = code := by
  cases code
  rfl

def decode13 : Universe (.type ⟨13,by decide⟩) → Type 13
  | .type13 carrier => carrier

theorem encode_decode13 (code : Universe (.type ⟨13,by decide⟩)) : Universe.type13 (decode13 code) = code := by
  cases code
  rfl

def decode14 : Universe (.type ⟨14,by decide⟩) → Type 14
  | .type14 carrier => carrier

theorem encode_decode14 (code : Universe (.type ⟨14,by decide⟩)) : Universe.type14 (decode14 code) = code := by
  cases code
  rfl

def decode15 : Universe (.type ⟨15,by decide⟩) → Type 15
  | .type15 carrier => carrier

theorem encode_decode15 (code : Universe (.type ⟨15,by decide⟩)) : Universe.type15 (decode15 code) = code := by
  cases code
  rfl

def decode16 : Universe (.type ⟨16,by decide⟩) → Type 16
  | .type16 carrier => carrier

theorem encode_decode16 (code : Universe (.type ⟨16,by decide⟩)) : Universe.type16 (decode16 code) = code := by
  cases code
  rfl

def decode17 : Universe (.type ⟨17,by decide⟩) → Type 17
  | .type17 carrier => carrier

theorem encode_decode17 (code : Universe (.type ⟨17,by decide⟩)) : Universe.type17 (decode17 code) = code := by
  cases code
  rfl

def decode18 : Universe (.type ⟨18,by decide⟩) → Type 18
  | .type18 carrier => carrier

theorem encode_decode18 (code : Universe (.type ⟨18,by decide⟩)) : Universe.type18 (decode18 code) = code := by
  cases code
  rfl

def decode19 : Universe (.type ⟨19,by decide⟩) → Type 19
  | .type19 carrier => carrier

theorem encode_decode19 (code : Universe (.type ⟨19,by decide⟩)) : Universe.type19 (decode19 code) = code := by
  cases code
  rfl

def decode20 : Universe (.type ⟨20,by decide⟩) → Type 20
  | .type20 carrier => carrier

theorem encode_decode20 (code : Universe (.type ⟨20,by decide⟩)) : Universe.type20 (decode20 code) = code := by
  cases code
  rfl

def decode21 : Universe (.type ⟨21,by decide⟩) → Type 21
  | .type21 carrier => carrier

theorem encode_decode21 (code : Universe (.type ⟨21,by decide⟩)) : Universe.type21 (decode21 code) = code := by
  cases code
  rfl

def decode22 : Universe (.type ⟨22,by decide⟩) → Type 22
  | .type22 carrier => carrier

theorem encode_decode22 (code : Universe (.type ⟨22,by decide⟩)) : Universe.type22 (decode22 code) = code := by
  cases code
  rfl

def decode23 : Universe (.type ⟨23,by decide⟩) → Type 23
  | .type23 carrier => carrier

theorem encode_decode23 (code : Universe (.type ⟨23,by decide⟩)) : Universe.type23 (decode23 code) = code := by
  cases code
  rfl

def decode24 : Universe (.type ⟨24,by decide⟩) → Type 24
  | .type24 carrier => carrier

theorem encode_decode24 (code : Universe (.type ⟨24,by decide⟩)) : Universe.type24 (decode24 code) = code := by
  cases code
  rfl

def decode25 : Universe (.type ⟨25,by decide⟩) → Type 25
  | .type25 carrier => carrier

theorem encode_decode25 (code : Universe (.type ⟨25,by decide⟩)) : Universe.type25 (decode25 code) = code := by
  cases code
  rfl

def decode26 : Universe (.type ⟨26,by decide⟩) → Type 26
  | .type26 carrier => carrier

theorem encode_decode26 (code : Universe (.type ⟨26,by decide⟩)) : Universe.type26 (decode26 code) = code := by
  cases code
  rfl

def decode27 : Universe (.type ⟨27,by decide⟩) → Type 27
  | .type27 carrier => carrier

theorem encode_decode27 (code : Universe (.type ⟨27,by decide⟩)) : Universe.type27 (decode27 code) = code := by
  cases code
  rfl

def decode28 : Universe (.type ⟨28,by decide⟩) → Type 28
  | .type28 carrier => carrier

theorem encode_decode28 (code : Universe (.type ⟨28,by decide⟩)) : Universe.type28 (decode28 code) = code := by
  cases code
  rfl

def decode29 : Universe (.type ⟨29,by decide⟩) → Type 29
  | .type29 carrier => carrier

theorem encode_decode29 (code : Universe (.type ⟨29,by decide⟩)) : Universe.type29 (decode29 code) = code := by
  cases code
  rfl

def decode30 : Universe (.type ⟨30,by decide⟩) → Type 30
  | .type30 carrier => carrier

theorem encode_decode30 (code : Universe (.type ⟨30,by decide⟩)) : Universe.type30 (decode30 code) = code := by
  cases code
  rfl

def decode31 : Universe (.type ⟨31,by decide⟩) → Type 31
  | .type31 carrier => carrier

theorem encode_decode31 (code : Universe (.type ⟨31,by decide⟩)) : Universe.type31 (decode31 code) = code := by
  cases code
  rfl

def decode32 : Universe (.type ⟨32,by decide⟩) → Type 32
  | .type32 carrier => carrier

theorem encode_decode32 (code : Universe (.type ⟨32,by decide⟩)) : Universe.type32 (decode32 code) = code := by
  cases code
  rfl

def decode33 : Universe (.type ⟨33,by decide⟩) → Type 33
  | .type33 carrier => carrier

theorem encode_decode33 (code : Universe (.type ⟨33,by decide⟩)) : Universe.type33 (decode33 code) = code := by
  cases code
  rfl

def natural : Universe (.type ⟨0,by decide⟩) := .type0 Nat
def integer : Universe (.type ⟨0,by decide⟩) := .type0 Int
def propositionUniverse : Universe (.type ⟨0,by decide⟩) := .type0 Prop

def array (length : Nat) : Universe (.type ⟨0,by decide⟩) := .type0 (Fin length → Int)
def equal (left right : Nat) : Universe .proposition := .proposition (left = right)
def less (left right : Nat) : Universe .proposition := .proposition (left < right)

theorem equal_realized (value : Carrier (equal left right)) : left = right := value.down.down
theorem less_realized (value : Carrier (less left right)) : left < right := value.down.down

theorem false_equal_empty (different : left ≠ right) : ¬ Nonempty (Carrier (equal left right)) := by
  intro realized
  obtain ⟨value⟩ := realized
  exact different (equal_realized value)

theorem false_less_empty (unordered : ¬ left < right) : ¬ Nonempty (Carrier (less left right)) := by
  intro realized
  obtain ⟨value⟩ := realized
  exact unordered (less_realized value)

def universe0 : Universe (.type ⟨1,by decide⟩) := .type1 (Type 0)

def universe1 : Universe (.type ⟨2,by decide⟩) := .type2 (Type 1)

def universe2 : Universe (.type ⟨3,by decide⟩) := .type3 (Type 2)

def universe3 : Universe (.type ⟨4,by decide⟩) := .type4 (Type 3)

def universe4 : Universe (.type ⟨5,by decide⟩) := .type5 (Type 4)

def universe5 : Universe (.type ⟨6,by decide⟩) := .type6 (Type 5)

def universe6 : Universe (.type ⟨7,by decide⟩) := .type7 (Type 6)

def universe7 : Universe (.type ⟨8,by decide⟩) := .type8 (Type 7)

def universe8 : Universe (.type ⟨9,by decide⟩) := .type9 (Type 8)

def universe9 : Universe (.type ⟨10,by decide⟩) := .type10 (Type 9)

def universe10 : Universe (.type ⟨11,by decide⟩) := .type11 (Type 10)

def universe11 : Universe (.type ⟨12,by decide⟩) := .type12 (Type 11)

def universe12 : Universe (.type ⟨13,by decide⟩) := .type13 (Type 12)

def universe13 : Universe (.type ⟨14,by decide⟩) := .type14 (Type 13)

def universe14 : Universe (.type ⟨15,by decide⟩) := .type15 (Type 14)

def universe15 : Universe (.type ⟨16,by decide⟩) := .type16 (Type 15)

def universe16 : Universe (.type ⟨17,by decide⟩) := .type17 (Type 16)

def universe17 : Universe (.type ⟨18,by decide⟩) := .type18 (Type 17)

def universe18 : Universe (.type ⟨19,by decide⟩) := .type19 (Type 18)

def universe19 : Universe (.type ⟨20,by decide⟩) := .type20 (Type 19)

def universe20 : Universe (.type ⟨21,by decide⟩) := .type21 (Type 20)

def universe21 : Universe (.type ⟨22,by decide⟩) := .type22 (Type 21)

def universe22 : Universe (.type ⟨23,by decide⟩) := .type23 (Type 22)

def universe23 : Universe (.type ⟨24,by decide⟩) := .type24 (Type 23)

def universe24 : Universe (.type ⟨25,by decide⟩) := .type25 (Type 24)

def universe25 : Universe (.type ⟨26,by decide⟩) := .type26 (Type 25)

def universe26 : Universe (.type ⟨27,by decide⟩) := .type27 (Type 26)

def universe27 : Universe (.type ⟨28,by decide⟩) := .type28 (Type 27)

def universe28 : Universe (.type ⟨29,by decide⟩) := .type29 (Type 28)

def universe29 : Universe (.type ⟨30,by decide⟩) := .type30 (Type 29)

def universe30 : Universe (.type ⟨31,by decide⟩) := .type31 (Type 30)

def universe31 : Universe (.type ⟨32,by decide⟩) := .type32 (Type 31)

def universe32 : Universe (.type ⟨33,by decide⟩) := .type33 (Type 32)

end Jihoo.NativeKernel.Environment.Semantics.Finite
