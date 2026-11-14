import Jihoo.NativeContextualUniverseModel
set_option maxUniverseOffset 40
set_option autoImplicit false

/-! Concrete Tarski coding and decoding, stable under contextual substitution.
Host level33 classifies administrative Universe32 only; no additional native
universe input or semantic-membership assumption is introduced. -/
namespace Jihoo.NativeKernel.Environment.Semantics.Contextual
open Finite

def propositionType {Γ : Context} : Ty Γ (.type ⟨0,by decide⟩) := fun _ => Finite.propositionUniverse

def encodeProposition {Γ : Context} (A : Ty Γ .proposition) : Tm (propositionType (Γ := Γ)) :=
  fun γ => ⟨decodeProp (A γ)⟩

def decodeProposition {Γ : Context} (code : Tm (propositionType (Γ := Γ))) : Ty Γ .proposition :=
  fun γ => .proposition (code γ).down

theorem decode_encode_proposition {Γ : Context} (A : Ty Γ .proposition) :
    decodeProposition (encodeProposition A) = A := by
  funext γ
  exact encode_decodeProp _

theorem encode_decode_proposition {Γ : Context} (code : Tm (propositionType (Γ := Γ))) :
    encodeProposition (decodeProposition code) = code := rfl

def universeType0 {Γ : Context} : Ty Γ (.type ⟨1,by decide⟩) := fun _ => Finite.universe0

def encodeType0 {Γ : Context} (A : Ty Γ (.type ⟨0,by decide⟩)) : Tm (universeType0 (Γ := Γ)) :=
  fun γ => ⟨decode0 (A γ)⟩

def decodeType0 {Γ : Context} (code : Tm (universeType0 (Γ := Γ))) : Ty Γ (.type ⟨0,by decide⟩) :=
  fun γ => .type0 (code γ).down

theorem decode_encode_type0 {Γ : Context} (A : Ty Γ (.type ⟨0,by decide⟩)) :
    decodeType0 (encodeType0 A) = A := by
  funext γ
  exact encode_decode0 _

theorem encode_decode_type0 {Γ : Context} (code : Tm (universeType0 (Γ := Γ))) :
    encodeType0 (decodeType0 code) = code := rfl

theorem encode_type0_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨0,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType0 A) σ = encodeType0 (typeSubst A σ) := rfl

theorem decode_type0_substitution {Γ Δ : Context} (code : Tm (universeType0 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType0 code) σ = decodeType0 (termSubst code σ) := rfl

def universeType1 {Γ : Context} : Ty Γ (.type ⟨2,by decide⟩) := fun _ => Finite.universe1

def encodeType1 {Γ : Context} (A : Ty Γ (.type ⟨1,by decide⟩)) : Tm (universeType1 (Γ := Γ)) :=
  fun γ => ⟨decode1 (A γ)⟩

def decodeType1 {Γ : Context} (code : Tm (universeType1 (Γ := Γ))) : Ty Γ (.type ⟨1,by decide⟩) :=
  fun γ => .type1 (code γ).down

theorem decode_encode_type1 {Γ : Context} (A : Ty Γ (.type ⟨1,by decide⟩)) :
    decodeType1 (encodeType1 A) = A := by
  funext γ
  exact encode_decode1 _

theorem encode_decode_type1 {Γ : Context} (code : Tm (universeType1 (Γ := Γ))) :
    encodeType1 (decodeType1 code) = code := rfl

theorem encode_type1_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨1,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType1 A) σ = encodeType1 (typeSubst A σ) := rfl

theorem decode_type1_substitution {Γ Δ : Context} (code : Tm (universeType1 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType1 code) σ = decodeType1 (termSubst code σ) := rfl

def universeType2 {Γ : Context} : Ty Γ (.type ⟨3,by decide⟩) := fun _ => Finite.universe2

def encodeType2 {Γ : Context} (A : Ty Γ (.type ⟨2,by decide⟩)) : Tm (universeType2 (Γ := Γ)) :=
  fun γ => ⟨decode2 (A γ)⟩

def decodeType2 {Γ : Context} (code : Tm (universeType2 (Γ := Γ))) : Ty Γ (.type ⟨2,by decide⟩) :=
  fun γ => .type2 (code γ).down

theorem decode_encode_type2 {Γ : Context} (A : Ty Γ (.type ⟨2,by decide⟩)) :
    decodeType2 (encodeType2 A) = A := by
  funext γ
  exact encode_decode2 _

theorem encode_decode_type2 {Γ : Context} (code : Tm (universeType2 (Γ := Γ))) :
    encodeType2 (decodeType2 code) = code := rfl

theorem encode_type2_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨2,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType2 A) σ = encodeType2 (typeSubst A σ) := rfl

theorem decode_type2_substitution {Γ Δ : Context} (code : Tm (universeType2 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType2 code) σ = decodeType2 (termSubst code σ) := rfl

def universeType3 {Γ : Context} : Ty Γ (.type ⟨4,by decide⟩) := fun _ => Finite.universe3

def encodeType3 {Γ : Context} (A : Ty Γ (.type ⟨3,by decide⟩)) : Tm (universeType3 (Γ := Γ)) :=
  fun γ => ⟨decode3 (A γ)⟩

def decodeType3 {Γ : Context} (code : Tm (universeType3 (Γ := Γ))) : Ty Γ (.type ⟨3,by decide⟩) :=
  fun γ => .type3 (code γ).down

theorem decode_encode_type3 {Γ : Context} (A : Ty Γ (.type ⟨3,by decide⟩)) :
    decodeType3 (encodeType3 A) = A := by
  funext γ
  exact encode_decode3 _

theorem encode_decode_type3 {Γ : Context} (code : Tm (universeType3 (Γ := Γ))) :
    encodeType3 (decodeType3 code) = code := rfl

theorem encode_type3_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨3,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType3 A) σ = encodeType3 (typeSubst A σ) := rfl

theorem decode_type3_substitution {Γ Δ : Context} (code : Tm (universeType3 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType3 code) σ = decodeType3 (termSubst code σ) := rfl

def universeType4 {Γ : Context} : Ty Γ (.type ⟨5,by decide⟩) := fun _ => Finite.universe4

def encodeType4 {Γ : Context} (A : Ty Γ (.type ⟨4,by decide⟩)) : Tm (universeType4 (Γ := Γ)) :=
  fun γ => ⟨decode4 (A γ)⟩

def decodeType4 {Γ : Context} (code : Tm (universeType4 (Γ := Γ))) : Ty Γ (.type ⟨4,by decide⟩) :=
  fun γ => .type4 (code γ).down

theorem decode_encode_type4 {Γ : Context} (A : Ty Γ (.type ⟨4,by decide⟩)) :
    decodeType4 (encodeType4 A) = A := by
  funext γ
  exact encode_decode4 _

theorem encode_decode_type4 {Γ : Context} (code : Tm (universeType4 (Γ := Γ))) :
    encodeType4 (decodeType4 code) = code := rfl

theorem encode_type4_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨4,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType4 A) σ = encodeType4 (typeSubst A σ) := rfl

theorem decode_type4_substitution {Γ Δ : Context} (code : Tm (universeType4 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType4 code) σ = decodeType4 (termSubst code σ) := rfl

def universeType5 {Γ : Context} : Ty Γ (.type ⟨6,by decide⟩) := fun _ => Finite.universe5

def encodeType5 {Γ : Context} (A : Ty Γ (.type ⟨5,by decide⟩)) : Tm (universeType5 (Γ := Γ)) :=
  fun γ => ⟨decode5 (A γ)⟩

def decodeType5 {Γ : Context} (code : Tm (universeType5 (Γ := Γ))) : Ty Γ (.type ⟨5,by decide⟩) :=
  fun γ => .type5 (code γ).down

theorem decode_encode_type5 {Γ : Context} (A : Ty Γ (.type ⟨5,by decide⟩)) :
    decodeType5 (encodeType5 A) = A := by
  funext γ
  exact encode_decode5 _

theorem encode_decode_type5 {Γ : Context} (code : Tm (universeType5 (Γ := Γ))) :
    encodeType5 (decodeType5 code) = code := rfl

theorem encode_type5_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨5,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType5 A) σ = encodeType5 (typeSubst A σ) := rfl

theorem decode_type5_substitution {Γ Δ : Context} (code : Tm (universeType5 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType5 code) σ = decodeType5 (termSubst code σ) := rfl

def universeType6 {Γ : Context} : Ty Γ (.type ⟨7,by decide⟩) := fun _ => Finite.universe6

def encodeType6 {Γ : Context} (A : Ty Γ (.type ⟨6,by decide⟩)) : Tm (universeType6 (Γ := Γ)) :=
  fun γ => ⟨decode6 (A γ)⟩

def decodeType6 {Γ : Context} (code : Tm (universeType6 (Γ := Γ))) : Ty Γ (.type ⟨6,by decide⟩) :=
  fun γ => .type6 (code γ).down

theorem decode_encode_type6 {Γ : Context} (A : Ty Γ (.type ⟨6,by decide⟩)) :
    decodeType6 (encodeType6 A) = A := by
  funext γ
  exact encode_decode6 _

theorem encode_decode_type6 {Γ : Context} (code : Tm (universeType6 (Γ := Γ))) :
    encodeType6 (decodeType6 code) = code := rfl

theorem encode_type6_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨6,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType6 A) σ = encodeType6 (typeSubst A σ) := rfl

theorem decode_type6_substitution {Γ Δ : Context} (code : Tm (universeType6 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType6 code) σ = decodeType6 (termSubst code σ) := rfl

def universeType7 {Γ : Context} : Ty Γ (.type ⟨8,by decide⟩) := fun _ => Finite.universe7

def encodeType7 {Γ : Context} (A : Ty Γ (.type ⟨7,by decide⟩)) : Tm (universeType7 (Γ := Γ)) :=
  fun γ => ⟨decode7 (A γ)⟩

def decodeType7 {Γ : Context} (code : Tm (universeType7 (Γ := Γ))) : Ty Γ (.type ⟨7,by decide⟩) :=
  fun γ => .type7 (code γ).down

theorem decode_encode_type7 {Γ : Context} (A : Ty Γ (.type ⟨7,by decide⟩)) :
    decodeType7 (encodeType7 A) = A := by
  funext γ
  exact encode_decode7 _

theorem encode_decode_type7 {Γ : Context} (code : Tm (universeType7 (Γ := Γ))) :
    encodeType7 (decodeType7 code) = code := rfl

theorem encode_type7_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨7,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType7 A) σ = encodeType7 (typeSubst A σ) := rfl

theorem decode_type7_substitution {Γ Δ : Context} (code : Tm (universeType7 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType7 code) σ = decodeType7 (termSubst code σ) := rfl

def universeType8 {Γ : Context} : Ty Γ (.type ⟨9,by decide⟩) := fun _ => Finite.universe8

def encodeType8 {Γ : Context} (A : Ty Γ (.type ⟨8,by decide⟩)) : Tm (universeType8 (Γ := Γ)) :=
  fun γ => ⟨decode8 (A γ)⟩

def decodeType8 {Γ : Context} (code : Tm (universeType8 (Γ := Γ))) : Ty Γ (.type ⟨8,by decide⟩) :=
  fun γ => .type8 (code γ).down

theorem decode_encode_type8 {Γ : Context} (A : Ty Γ (.type ⟨8,by decide⟩)) :
    decodeType8 (encodeType8 A) = A := by
  funext γ
  exact encode_decode8 _

theorem encode_decode_type8 {Γ : Context} (code : Tm (universeType8 (Γ := Γ))) :
    encodeType8 (decodeType8 code) = code := rfl

theorem encode_type8_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨8,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType8 A) σ = encodeType8 (typeSubst A σ) := rfl

theorem decode_type8_substitution {Γ Δ : Context} (code : Tm (universeType8 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType8 code) σ = decodeType8 (termSubst code σ) := rfl

def universeType9 {Γ : Context} : Ty Γ (.type ⟨10,by decide⟩) := fun _ => Finite.universe9

def encodeType9 {Γ : Context} (A : Ty Γ (.type ⟨9,by decide⟩)) : Tm (universeType9 (Γ := Γ)) :=
  fun γ => ⟨decode9 (A γ)⟩

def decodeType9 {Γ : Context} (code : Tm (universeType9 (Γ := Γ))) : Ty Γ (.type ⟨9,by decide⟩) :=
  fun γ => .type9 (code γ).down

theorem decode_encode_type9 {Γ : Context} (A : Ty Γ (.type ⟨9,by decide⟩)) :
    decodeType9 (encodeType9 A) = A := by
  funext γ
  exact encode_decode9 _

theorem encode_decode_type9 {Γ : Context} (code : Tm (universeType9 (Γ := Γ))) :
    encodeType9 (decodeType9 code) = code := rfl

theorem encode_type9_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨9,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType9 A) σ = encodeType9 (typeSubst A σ) := rfl

theorem decode_type9_substitution {Γ Δ : Context} (code : Tm (universeType9 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType9 code) σ = decodeType9 (termSubst code σ) := rfl

def universeType10 {Γ : Context} : Ty Γ (.type ⟨11,by decide⟩) := fun _ => Finite.universe10

def encodeType10 {Γ : Context} (A : Ty Γ (.type ⟨10,by decide⟩)) : Tm (universeType10 (Γ := Γ)) :=
  fun γ => ⟨decode10 (A γ)⟩

def decodeType10 {Γ : Context} (code : Tm (universeType10 (Γ := Γ))) : Ty Γ (.type ⟨10,by decide⟩) :=
  fun γ => .type10 (code γ).down

theorem decode_encode_type10 {Γ : Context} (A : Ty Γ (.type ⟨10,by decide⟩)) :
    decodeType10 (encodeType10 A) = A := by
  funext γ
  exact encode_decode10 _

theorem encode_decode_type10 {Γ : Context} (code : Tm (universeType10 (Γ := Γ))) :
    encodeType10 (decodeType10 code) = code := rfl

theorem encode_type10_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨10,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType10 A) σ = encodeType10 (typeSubst A σ) := rfl

theorem decode_type10_substitution {Γ Δ : Context} (code : Tm (universeType10 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType10 code) σ = decodeType10 (termSubst code σ) := rfl

def universeType11 {Γ : Context} : Ty Γ (.type ⟨12,by decide⟩) := fun _ => Finite.universe11

def encodeType11 {Γ : Context} (A : Ty Γ (.type ⟨11,by decide⟩)) : Tm (universeType11 (Γ := Γ)) :=
  fun γ => ⟨decode11 (A γ)⟩

def decodeType11 {Γ : Context} (code : Tm (universeType11 (Γ := Γ))) : Ty Γ (.type ⟨11,by decide⟩) :=
  fun γ => .type11 (code γ).down

theorem decode_encode_type11 {Γ : Context} (A : Ty Γ (.type ⟨11,by decide⟩)) :
    decodeType11 (encodeType11 A) = A := by
  funext γ
  exact encode_decode11 _

theorem encode_decode_type11 {Γ : Context} (code : Tm (universeType11 (Γ := Γ))) :
    encodeType11 (decodeType11 code) = code := rfl

theorem encode_type11_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨11,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType11 A) σ = encodeType11 (typeSubst A σ) := rfl

theorem decode_type11_substitution {Γ Δ : Context} (code : Tm (universeType11 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType11 code) σ = decodeType11 (termSubst code σ) := rfl

def universeType12 {Γ : Context} : Ty Γ (.type ⟨13,by decide⟩) := fun _ => Finite.universe12

def encodeType12 {Γ : Context} (A : Ty Γ (.type ⟨12,by decide⟩)) : Tm (universeType12 (Γ := Γ)) :=
  fun γ => ⟨decode12 (A γ)⟩

def decodeType12 {Γ : Context} (code : Tm (universeType12 (Γ := Γ))) : Ty Γ (.type ⟨12,by decide⟩) :=
  fun γ => .type12 (code γ).down

theorem decode_encode_type12 {Γ : Context} (A : Ty Γ (.type ⟨12,by decide⟩)) :
    decodeType12 (encodeType12 A) = A := by
  funext γ
  exact encode_decode12 _

theorem encode_decode_type12 {Γ : Context} (code : Tm (universeType12 (Γ := Γ))) :
    encodeType12 (decodeType12 code) = code := rfl

theorem encode_type12_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨12,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType12 A) σ = encodeType12 (typeSubst A σ) := rfl

theorem decode_type12_substitution {Γ Δ : Context} (code : Tm (universeType12 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType12 code) σ = decodeType12 (termSubst code σ) := rfl

def universeType13 {Γ : Context} : Ty Γ (.type ⟨14,by decide⟩) := fun _ => Finite.universe13

def encodeType13 {Γ : Context} (A : Ty Γ (.type ⟨13,by decide⟩)) : Tm (universeType13 (Γ := Γ)) :=
  fun γ => ⟨decode13 (A γ)⟩

def decodeType13 {Γ : Context} (code : Tm (universeType13 (Γ := Γ))) : Ty Γ (.type ⟨13,by decide⟩) :=
  fun γ => .type13 (code γ).down

theorem decode_encode_type13 {Γ : Context} (A : Ty Γ (.type ⟨13,by decide⟩)) :
    decodeType13 (encodeType13 A) = A := by
  funext γ
  exact encode_decode13 _

theorem encode_decode_type13 {Γ : Context} (code : Tm (universeType13 (Γ := Γ))) :
    encodeType13 (decodeType13 code) = code := rfl

theorem encode_type13_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨13,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType13 A) σ = encodeType13 (typeSubst A σ) := rfl

theorem decode_type13_substitution {Γ Δ : Context} (code : Tm (universeType13 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType13 code) σ = decodeType13 (termSubst code σ) := rfl

def universeType14 {Γ : Context} : Ty Γ (.type ⟨15,by decide⟩) := fun _ => Finite.universe14

def encodeType14 {Γ : Context} (A : Ty Γ (.type ⟨14,by decide⟩)) : Tm (universeType14 (Γ := Γ)) :=
  fun γ => ⟨decode14 (A γ)⟩

def decodeType14 {Γ : Context} (code : Tm (universeType14 (Γ := Γ))) : Ty Γ (.type ⟨14,by decide⟩) :=
  fun γ => .type14 (code γ).down

theorem decode_encode_type14 {Γ : Context} (A : Ty Γ (.type ⟨14,by decide⟩)) :
    decodeType14 (encodeType14 A) = A := by
  funext γ
  exact encode_decode14 _

theorem encode_decode_type14 {Γ : Context} (code : Tm (universeType14 (Γ := Γ))) :
    encodeType14 (decodeType14 code) = code := rfl

theorem encode_type14_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨14,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType14 A) σ = encodeType14 (typeSubst A σ) := rfl

theorem decode_type14_substitution {Γ Δ : Context} (code : Tm (universeType14 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType14 code) σ = decodeType14 (termSubst code σ) := rfl

def universeType15 {Γ : Context} : Ty Γ (.type ⟨16,by decide⟩) := fun _ => Finite.universe15

def encodeType15 {Γ : Context} (A : Ty Γ (.type ⟨15,by decide⟩)) : Tm (universeType15 (Γ := Γ)) :=
  fun γ => ⟨decode15 (A γ)⟩

def decodeType15 {Γ : Context} (code : Tm (universeType15 (Γ := Γ))) : Ty Γ (.type ⟨15,by decide⟩) :=
  fun γ => .type15 (code γ).down

theorem decode_encode_type15 {Γ : Context} (A : Ty Γ (.type ⟨15,by decide⟩)) :
    decodeType15 (encodeType15 A) = A := by
  funext γ
  exact encode_decode15 _

theorem encode_decode_type15 {Γ : Context} (code : Tm (universeType15 (Γ := Γ))) :
    encodeType15 (decodeType15 code) = code := rfl

theorem encode_type15_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨15,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType15 A) σ = encodeType15 (typeSubst A σ) := rfl

theorem decode_type15_substitution {Γ Δ : Context} (code : Tm (universeType15 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType15 code) σ = decodeType15 (termSubst code σ) := rfl

def universeType16 {Γ : Context} : Ty Γ (.type ⟨17,by decide⟩) := fun _ => Finite.universe16

def encodeType16 {Γ : Context} (A : Ty Γ (.type ⟨16,by decide⟩)) : Tm (universeType16 (Γ := Γ)) :=
  fun γ => ⟨decode16 (A γ)⟩

def decodeType16 {Γ : Context} (code : Tm (universeType16 (Γ := Γ))) : Ty Γ (.type ⟨16,by decide⟩) :=
  fun γ => .type16 (code γ).down

theorem decode_encode_type16 {Γ : Context} (A : Ty Γ (.type ⟨16,by decide⟩)) :
    decodeType16 (encodeType16 A) = A := by
  funext γ
  exact encode_decode16 _

theorem encode_decode_type16 {Γ : Context} (code : Tm (universeType16 (Γ := Γ))) :
    encodeType16 (decodeType16 code) = code := rfl

theorem encode_type16_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨16,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType16 A) σ = encodeType16 (typeSubst A σ) := rfl

theorem decode_type16_substitution {Γ Δ : Context} (code : Tm (universeType16 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType16 code) σ = decodeType16 (termSubst code σ) := rfl

def universeType17 {Γ : Context} : Ty Γ (.type ⟨18,by decide⟩) := fun _ => Finite.universe17

def encodeType17 {Γ : Context} (A : Ty Γ (.type ⟨17,by decide⟩)) : Tm (universeType17 (Γ := Γ)) :=
  fun γ => ⟨decode17 (A γ)⟩

def decodeType17 {Γ : Context} (code : Tm (universeType17 (Γ := Γ))) : Ty Γ (.type ⟨17,by decide⟩) :=
  fun γ => .type17 (code γ).down

theorem decode_encode_type17 {Γ : Context} (A : Ty Γ (.type ⟨17,by decide⟩)) :
    decodeType17 (encodeType17 A) = A := by
  funext γ
  exact encode_decode17 _

theorem encode_decode_type17 {Γ : Context} (code : Tm (universeType17 (Γ := Γ))) :
    encodeType17 (decodeType17 code) = code := rfl

theorem encode_type17_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨17,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType17 A) σ = encodeType17 (typeSubst A σ) := rfl

theorem decode_type17_substitution {Γ Δ : Context} (code : Tm (universeType17 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType17 code) σ = decodeType17 (termSubst code σ) := rfl

def universeType18 {Γ : Context} : Ty Γ (.type ⟨19,by decide⟩) := fun _ => Finite.universe18

def encodeType18 {Γ : Context} (A : Ty Γ (.type ⟨18,by decide⟩)) : Tm (universeType18 (Γ := Γ)) :=
  fun γ => ⟨decode18 (A γ)⟩

def decodeType18 {Γ : Context} (code : Tm (universeType18 (Γ := Γ))) : Ty Γ (.type ⟨18,by decide⟩) :=
  fun γ => .type18 (code γ).down

theorem decode_encode_type18 {Γ : Context} (A : Ty Γ (.type ⟨18,by decide⟩)) :
    decodeType18 (encodeType18 A) = A := by
  funext γ
  exact encode_decode18 _

theorem encode_decode_type18 {Γ : Context} (code : Tm (universeType18 (Γ := Γ))) :
    encodeType18 (decodeType18 code) = code := rfl

theorem encode_type18_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨18,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType18 A) σ = encodeType18 (typeSubst A σ) := rfl

theorem decode_type18_substitution {Γ Δ : Context} (code : Tm (universeType18 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType18 code) σ = decodeType18 (termSubst code σ) := rfl

def universeType19 {Γ : Context} : Ty Γ (.type ⟨20,by decide⟩) := fun _ => Finite.universe19

def encodeType19 {Γ : Context} (A : Ty Γ (.type ⟨19,by decide⟩)) : Tm (universeType19 (Γ := Γ)) :=
  fun γ => ⟨decode19 (A γ)⟩

def decodeType19 {Γ : Context} (code : Tm (universeType19 (Γ := Γ))) : Ty Γ (.type ⟨19,by decide⟩) :=
  fun γ => .type19 (code γ).down

theorem decode_encode_type19 {Γ : Context} (A : Ty Γ (.type ⟨19,by decide⟩)) :
    decodeType19 (encodeType19 A) = A := by
  funext γ
  exact encode_decode19 _

theorem encode_decode_type19 {Γ : Context} (code : Tm (universeType19 (Γ := Γ))) :
    encodeType19 (decodeType19 code) = code := rfl

theorem encode_type19_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨19,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType19 A) σ = encodeType19 (typeSubst A σ) := rfl

theorem decode_type19_substitution {Γ Δ : Context} (code : Tm (universeType19 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType19 code) σ = decodeType19 (termSubst code σ) := rfl

def universeType20 {Γ : Context} : Ty Γ (.type ⟨21,by decide⟩) := fun _ => Finite.universe20

def encodeType20 {Γ : Context} (A : Ty Γ (.type ⟨20,by decide⟩)) : Tm (universeType20 (Γ := Γ)) :=
  fun γ => ⟨decode20 (A γ)⟩

def decodeType20 {Γ : Context} (code : Tm (universeType20 (Γ := Γ))) : Ty Γ (.type ⟨20,by decide⟩) :=
  fun γ => .type20 (code γ).down

theorem decode_encode_type20 {Γ : Context} (A : Ty Γ (.type ⟨20,by decide⟩)) :
    decodeType20 (encodeType20 A) = A := by
  funext γ
  exact encode_decode20 _

theorem encode_decode_type20 {Γ : Context} (code : Tm (universeType20 (Γ := Γ))) :
    encodeType20 (decodeType20 code) = code := rfl

theorem encode_type20_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨20,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType20 A) σ = encodeType20 (typeSubst A σ) := rfl

theorem decode_type20_substitution {Γ Δ : Context} (code : Tm (universeType20 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType20 code) σ = decodeType20 (termSubst code σ) := rfl

def universeType21 {Γ : Context} : Ty Γ (.type ⟨22,by decide⟩) := fun _ => Finite.universe21

def encodeType21 {Γ : Context} (A : Ty Γ (.type ⟨21,by decide⟩)) : Tm (universeType21 (Γ := Γ)) :=
  fun γ => ⟨decode21 (A γ)⟩

def decodeType21 {Γ : Context} (code : Tm (universeType21 (Γ := Γ))) : Ty Γ (.type ⟨21,by decide⟩) :=
  fun γ => .type21 (code γ).down

theorem decode_encode_type21 {Γ : Context} (A : Ty Γ (.type ⟨21,by decide⟩)) :
    decodeType21 (encodeType21 A) = A := by
  funext γ
  exact encode_decode21 _

theorem encode_decode_type21 {Γ : Context} (code : Tm (universeType21 (Γ := Γ))) :
    encodeType21 (decodeType21 code) = code := rfl

theorem encode_type21_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨21,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType21 A) σ = encodeType21 (typeSubst A σ) := rfl

theorem decode_type21_substitution {Γ Δ : Context} (code : Tm (universeType21 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType21 code) σ = decodeType21 (termSubst code σ) := rfl

def universeType22 {Γ : Context} : Ty Γ (.type ⟨23,by decide⟩) := fun _ => Finite.universe22

def encodeType22 {Γ : Context} (A : Ty Γ (.type ⟨22,by decide⟩)) : Tm (universeType22 (Γ := Γ)) :=
  fun γ => ⟨decode22 (A γ)⟩

def decodeType22 {Γ : Context} (code : Tm (universeType22 (Γ := Γ))) : Ty Γ (.type ⟨22,by decide⟩) :=
  fun γ => .type22 (code γ).down

theorem decode_encode_type22 {Γ : Context} (A : Ty Γ (.type ⟨22,by decide⟩)) :
    decodeType22 (encodeType22 A) = A := by
  funext γ
  exact encode_decode22 _

theorem encode_decode_type22 {Γ : Context} (code : Tm (universeType22 (Γ := Γ))) :
    encodeType22 (decodeType22 code) = code := rfl

theorem encode_type22_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨22,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType22 A) σ = encodeType22 (typeSubst A σ) := rfl

theorem decode_type22_substitution {Γ Δ : Context} (code : Tm (universeType22 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType22 code) σ = decodeType22 (termSubst code σ) := rfl

def universeType23 {Γ : Context} : Ty Γ (.type ⟨24,by decide⟩) := fun _ => Finite.universe23

def encodeType23 {Γ : Context} (A : Ty Γ (.type ⟨23,by decide⟩)) : Tm (universeType23 (Γ := Γ)) :=
  fun γ => ⟨decode23 (A γ)⟩

def decodeType23 {Γ : Context} (code : Tm (universeType23 (Γ := Γ))) : Ty Γ (.type ⟨23,by decide⟩) :=
  fun γ => .type23 (code γ).down

theorem decode_encode_type23 {Γ : Context} (A : Ty Γ (.type ⟨23,by decide⟩)) :
    decodeType23 (encodeType23 A) = A := by
  funext γ
  exact encode_decode23 _

theorem encode_decode_type23 {Γ : Context} (code : Tm (universeType23 (Γ := Γ))) :
    encodeType23 (decodeType23 code) = code := rfl

theorem encode_type23_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨23,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType23 A) σ = encodeType23 (typeSubst A σ) := rfl

theorem decode_type23_substitution {Γ Δ : Context} (code : Tm (universeType23 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType23 code) σ = decodeType23 (termSubst code σ) := rfl

def universeType24 {Γ : Context} : Ty Γ (.type ⟨25,by decide⟩) := fun _ => Finite.universe24

def encodeType24 {Γ : Context} (A : Ty Γ (.type ⟨24,by decide⟩)) : Tm (universeType24 (Γ := Γ)) :=
  fun γ => ⟨decode24 (A γ)⟩

def decodeType24 {Γ : Context} (code : Tm (universeType24 (Γ := Γ))) : Ty Γ (.type ⟨24,by decide⟩) :=
  fun γ => .type24 (code γ).down

theorem decode_encode_type24 {Γ : Context} (A : Ty Γ (.type ⟨24,by decide⟩)) :
    decodeType24 (encodeType24 A) = A := by
  funext γ
  exact encode_decode24 _

theorem encode_decode_type24 {Γ : Context} (code : Tm (universeType24 (Γ := Γ))) :
    encodeType24 (decodeType24 code) = code := rfl

theorem encode_type24_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨24,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType24 A) σ = encodeType24 (typeSubst A σ) := rfl

theorem decode_type24_substitution {Γ Δ : Context} (code : Tm (universeType24 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType24 code) σ = decodeType24 (termSubst code σ) := rfl

def universeType25 {Γ : Context} : Ty Γ (.type ⟨26,by decide⟩) := fun _ => Finite.universe25

def encodeType25 {Γ : Context} (A : Ty Γ (.type ⟨25,by decide⟩)) : Tm (universeType25 (Γ := Γ)) :=
  fun γ => ⟨decode25 (A γ)⟩

def decodeType25 {Γ : Context} (code : Tm (universeType25 (Γ := Γ))) : Ty Γ (.type ⟨25,by decide⟩) :=
  fun γ => .type25 (code γ).down

theorem decode_encode_type25 {Γ : Context} (A : Ty Γ (.type ⟨25,by decide⟩)) :
    decodeType25 (encodeType25 A) = A := by
  funext γ
  exact encode_decode25 _

theorem encode_decode_type25 {Γ : Context} (code : Tm (universeType25 (Γ := Γ))) :
    encodeType25 (decodeType25 code) = code := rfl

theorem encode_type25_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨25,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType25 A) σ = encodeType25 (typeSubst A σ) := rfl

theorem decode_type25_substitution {Γ Δ : Context} (code : Tm (universeType25 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType25 code) σ = decodeType25 (termSubst code σ) := rfl

def universeType26 {Γ : Context} : Ty Γ (.type ⟨27,by decide⟩) := fun _ => Finite.universe26

def encodeType26 {Γ : Context} (A : Ty Γ (.type ⟨26,by decide⟩)) : Tm (universeType26 (Γ := Γ)) :=
  fun γ => ⟨decode26 (A γ)⟩

def decodeType26 {Γ : Context} (code : Tm (universeType26 (Γ := Γ))) : Ty Γ (.type ⟨26,by decide⟩) :=
  fun γ => .type26 (code γ).down

theorem decode_encode_type26 {Γ : Context} (A : Ty Γ (.type ⟨26,by decide⟩)) :
    decodeType26 (encodeType26 A) = A := by
  funext γ
  exact encode_decode26 _

theorem encode_decode_type26 {Γ : Context} (code : Tm (universeType26 (Γ := Γ))) :
    encodeType26 (decodeType26 code) = code := rfl

theorem encode_type26_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨26,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType26 A) σ = encodeType26 (typeSubst A σ) := rfl

theorem decode_type26_substitution {Γ Δ : Context} (code : Tm (universeType26 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType26 code) σ = decodeType26 (termSubst code σ) := rfl

def universeType27 {Γ : Context} : Ty Γ (.type ⟨28,by decide⟩) := fun _ => Finite.universe27

def encodeType27 {Γ : Context} (A : Ty Γ (.type ⟨27,by decide⟩)) : Tm (universeType27 (Γ := Γ)) :=
  fun γ => ⟨decode27 (A γ)⟩

def decodeType27 {Γ : Context} (code : Tm (universeType27 (Γ := Γ))) : Ty Γ (.type ⟨27,by decide⟩) :=
  fun γ => .type27 (code γ).down

theorem decode_encode_type27 {Γ : Context} (A : Ty Γ (.type ⟨27,by decide⟩)) :
    decodeType27 (encodeType27 A) = A := by
  funext γ
  exact encode_decode27 _

theorem encode_decode_type27 {Γ : Context} (code : Tm (universeType27 (Γ := Γ))) :
    encodeType27 (decodeType27 code) = code := rfl

theorem encode_type27_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨27,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType27 A) σ = encodeType27 (typeSubst A σ) := rfl

theorem decode_type27_substitution {Γ Δ : Context} (code : Tm (universeType27 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType27 code) σ = decodeType27 (termSubst code σ) := rfl

def universeType28 {Γ : Context} : Ty Γ (.type ⟨29,by decide⟩) := fun _ => Finite.universe28

def encodeType28 {Γ : Context} (A : Ty Γ (.type ⟨28,by decide⟩)) : Tm (universeType28 (Γ := Γ)) :=
  fun γ => ⟨decode28 (A γ)⟩

def decodeType28 {Γ : Context} (code : Tm (universeType28 (Γ := Γ))) : Ty Γ (.type ⟨28,by decide⟩) :=
  fun γ => .type28 (code γ).down

theorem decode_encode_type28 {Γ : Context} (A : Ty Γ (.type ⟨28,by decide⟩)) :
    decodeType28 (encodeType28 A) = A := by
  funext γ
  exact encode_decode28 _

theorem encode_decode_type28 {Γ : Context} (code : Tm (universeType28 (Γ := Γ))) :
    encodeType28 (decodeType28 code) = code := rfl

theorem encode_type28_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨28,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType28 A) σ = encodeType28 (typeSubst A σ) := rfl

theorem decode_type28_substitution {Γ Δ : Context} (code : Tm (universeType28 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType28 code) σ = decodeType28 (termSubst code σ) := rfl

def universeType29 {Γ : Context} : Ty Γ (.type ⟨30,by decide⟩) := fun _ => Finite.universe29

def encodeType29 {Γ : Context} (A : Ty Γ (.type ⟨29,by decide⟩)) : Tm (universeType29 (Γ := Γ)) :=
  fun γ => ⟨decode29 (A γ)⟩

def decodeType29 {Γ : Context} (code : Tm (universeType29 (Γ := Γ))) : Ty Γ (.type ⟨29,by decide⟩) :=
  fun γ => .type29 (code γ).down

theorem decode_encode_type29 {Γ : Context} (A : Ty Γ (.type ⟨29,by decide⟩)) :
    decodeType29 (encodeType29 A) = A := by
  funext γ
  exact encode_decode29 _

theorem encode_decode_type29 {Γ : Context} (code : Tm (universeType29 (Γ := Γ))) :
    encodeType29 (decodeType29 code) = code := rfl

theorem encode_type29_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨29,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType29 A) σ = encodeType29 (typeSubst A σ) := rfl

theorem decode_type29_substitution {Γ Δ : Context} (code : Tm (universeType29 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType29 code) σ = decodeType29 (termSubst code σ) := rfl

def universeType30 {Γ : Context} : Ty Γ (.type ⟨31,by decide⟩) := fun _ => Finite.universe30

def encodeType30 {Γ : Context} (A : Ty Γ (.type ⟨30,by decide⟩)) : Tm (universeType30 (Γ := Γ)) :=
  fun γ => ⟨decode30 (A γ)⟩

def decodeType30 {Γ : Context} (code : Tm (universeType30 (Γ := Γ))) : Ty Γ (.type ⟨30,by decide⟩) :=
  fun γ => .type30 (code γ).down

theorem decode_encode_type30 {Γ : Context} (A : Ty Γ (.type ⟨30,by decide⟩)) :
    decodeType30 (encodeType30 A) = A := by
  funext γ
  exact encode_decode30 _

theorem encode_decode_type30 {Γ : Context} (code : Tm (universeType30 (Γ := Γ))) :
    encodeType30 (decodeType30 code) = code := rfl

theorem encode_type30_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨30,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType30 A) σ = encodeType30 (typeSubst A σ) := rfl

theorem decode_type30_substitution {Γ Δ : Context} (code : Tm (universeType30 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType30 code) σ = decodeType30 (termSubst code σ) := rfl

def universeType31 {Γ : Context} : Ty Γ (.type ⟨32,by decide⟩) := fun _ => Finite.universe31

def encodeType31 {Γ : Context} (A : Ty Γ (.type ⟨31,by decide⟩)) : Tm (universeType31 (Γ := Γ)) :=
  fun γ => ⟨decode31 (A γ)⟩

def decodeType31 {Γ : Context} (code : Tm (universeType31 (Γ := Γ))) : Ty Γ (.type ⟨31,by decide⟩) :=
  fun γ => .type31 (code γ).down

theorem decode_encode_type31 {Γ : Context} (A : Ty Γ (.type ⟨31,by decide⟩)) :
    decodeType31 (encodeType31 A) = A := by
  funext γ
  exact encode_decode31 _

theorem encode_decode_type31 {Γ : Context} (code : Tm (universeType31 (Γ := Γ))) :
    encodeType31 (decodeType31 code) = code := rfl

theorem encode_type31_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨31,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType31 A) σ = encodeType31 (typeSubst A σ) := rfl

theorem decode_type31_substitution {Γ Δ : Context} (code : Tm (universeType31 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType31 code) σ = decodeType31 (termSubst code σ) := rfl

def universeType32 {Γ : Context} : Ty Γ (.type ⟨33,by decide⟩) := fun _ => Finite.universe32

def encodeType32 {Γ : Context} (A : Ty Γ (.type ⟨32,by decide⟩)) : Tm (universeType32 (Γ := Γ)) :=
  fun γ => ⟨decode32 (A γ)⟩

def decodeType32 {Γ : Context} (code : Tm (universeType32 (Γ := Γ))) : Ty Γ (.type ⟨32,by decide⟩) :=
  fun γ => .type32 (code γ).down

theorem decode_encode_type32 {Γ : Context} (A : Ty Γ (.type ⟨32,by decide⟩)) :
    decodeType32 (encodeType32 A) = A := by
  funext γ
  exact encode_decode32 _

theorem encode_decode_type32 {Γ : Context} (code : Tm (universeType32 (Γ := Γ))) :
    encodeType32 (decodeType32 code) = code := rfl

theorem encode_type32_substitution {Γ Δ : Context} (A : Ty Δ (.type ⟨32,by decide⟩)) (σ : Sub Γ Δ) :
    termSubst (encodeType32 A) σ = encodeType32 (typeSubst A σ) := rfl

theorem decode_type32_substitution {Γ Δ : Context} (code : Tm (universeType32 (Γ := Δ))) (σ : Sub Γ Δ) :
    typeSubst (decodeType32 code) σ = decodeType32 (termSubst code σ) := rfl

def universeLiteral0 {Γ : Context} : Tm (universeType1 (Γ := Γ)) := encodeType1 universeType0

def universeLiteral1 {Γ : Context} : Tm (universeType2 (Γ := Γ)) := encodeType2 universeType1

def universeLiteral2 {Γ : Context} : Tm (universeType3 (Γ := Γ)) := encodeType3 universeType2

def universeLiteral3 {Γ : Context} : Tm (universeType4 (Γ := Γ)) := encodeType4 universeType3

def universeLiteral4 {Γ : Context} : Tm (universeType5 (Γ := Γ)) := encodeType5 universeType4

def universeLiteral5 {Γ : Context} : Tm (universeType6 (Γ := Γ)) := encodeType6 universeType5

def universeLiteral6 {Γ : Context} : Tm (universeType7 (Γ := Γ)) := encodeType7 universeType6

def universeLiteral7 {Γ : Context} : Tm (universeType8 (Γ := Γ)) := encodeType8 universeType7

def universeLiteral8 {Γ : Context} : Tm (universeType9 (Γ := Γ)) := encodeType9 universeType8

def universeLiteral9 {Γ : Context} : Tm (universeType10 (Γ := Γ)) := encodeType10 universeType9

def universeLiteral10 {Γ : Context} : Tm (universeType11 (Γ := Γ)) := encodeType11 universeType10

def universeLiteral11 {Γ : Context} : Tm (universeType12 (Γ := Γ)) := encodeType12 universeType11

def universeLiteral12 {Γ : Context} : Tm (universeType13 (Γ := Γ)) := encodeType13 universeType12

def universeLiteral13 {Γ : Context} : Tm (universeType14 (Γ := Γ)) := encodeType14 universeType13

def universeLiteral14 {Γ : Context} : Tm (universeType15 (Γ := Γ)) := encodeType15 universeType14

def universeLiteral15 {Γ : Context} : Tm (universeType16 (Γ := Γ)) := encodeType16 universeType15

def universeLiteral16 {Γ : Context} : Tm (universeType17 (Γ := Γ)) := encodeType17 universeType16

def universeLiteral17 {Γ : Context} : Tm (universeType18 (Γ := Γ)) := encodeType18 universeType17

def universeLiteral18 {Γ : Context} : Tm (universeType19 (Γ := Γ)) := encodeType19 universeType18

def universeLiteral19 {Γ : Context} : Tm (universeType20 (Γ := Γ)) := encodeType20 universeType19

def universeLiteral20 {Γ : Context} : Tm (universeType21 (Γ := Γ)) := encodeType21 universeType20

def universeLiteral21 {Γ : Context} : Tm (universeType22 (Γ := Γ)) := encodeType22 universeType21

def universeLiteral22 {Γ : Context} : Tm (universeType23 (Γ := Γ)) := encodeType23 universeType22

def universeLiteral23 {Γ : Context} : Tm (universeType24 (Γ := Γ)) := encodeType24 universeType23

def universeLiteral24 {Γ : Context} : Tm (universeType25 (Γ := Γ)) := encodeType25 universeType24

def universeLiteral25 {Γ : Context} : Tm (universeType26 (Γ := Γ)) := encodeType26 universeType25

def universeLiteral26 {Γ : Context} : Tm (universeType27 (Γ := Γ)) := encodeType27 universeType26

def universeLiteral27 {Γ : Context} : Tm (universeType28 (Γ := Γ)) := encodeType28 universeType27

def universeLiteral28 {Γ : Context} : Tm (universeType29 (Γ := Γ)) := encodeType29 universeType28

def universeLiteral29 {Γ : Context} : Tm (universeType30 (Γ := Γ)) := encodeType30 universeType29

def universeLiteral30 {Γ : Context} : Tm (universeType31 (Γ := Γ)) := encodeType31 universeType30

def universeLiteral31 {Γ : Context} : Tm (universeType32 (Γ := Γ)) := encodeType32 universeType31

end Jihoo.NativeKernel.Environment.Semantics.Contextual
