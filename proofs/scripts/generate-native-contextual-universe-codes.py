"""Generate checked contextual universe coding/decoding through admin32."""
from pathlib import Path
out=['''import Jihoo.NativeContextualUniverseModel
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
''']
for n in range(33):
 out.append(f'\ndef universeType{n} {{Γ : Context}} : Ty Γ (.type ⟨{n+1},by decide⟩) := fun _ => Finite.universe{n}\n')
 out.append(f'\ndef encodeType{n} {{Γ : Context}} (A : Ty Γ (.type ⟨{n},by decide⟩)) : Tm (universeType{n} (Γ := Γ)) :=\n  fun γ => ⟨decode{n} (A γ)⟩\n')
 out.append(f'\ndef decodeType{n} {{Γ : Context}} (code : Tm (universeType{n} (Γ := Γ))) : Ty Γ (.type ⟨{n},by decide⟩) :=\n  fun γ => .type{n} (code γ).down\n')
 out.append(f'\ntheorem decode_encode_type{n} {{Γ : Context}} (A : Ty Γ (.type ⟨{n},by decide⟩)) :\n    decodeType{n} (encodeType{n} A) = A := by\n  funext γ\n  exact encode_decode{n} _\n')
 out.append(f'\ntheorem encode_decode_type{n} {{Γ : Context}} (code : Tm (universeType{n} (Γ := Γ))) :\n    encodeType{n} (decodeType{n} code) = code := rfl\n')
 out.append(f'\ntheorem encode_type{n}_substitution {{Γ Δ : Context}} (A : Ty Δ (.type ⟨{n},by decide⟩)) (σ : Sub Γ Δ) :\n    termSubst (encodeType{n} A) σ = encodeType{n} (typeSubst A σ) := rfl\n')
 out.append(f'\ntheorem decode_type{n}_substitution {{Γ Δ : Context}} (code : Tm (universeType{n} (Γ := Δ))) (σ : Sub Γ Δ) :\n    typeSubst (decodeType{n} code) σ = decodeType{n} (termSubst code σ) := rfl\n')
for n in range(32):
 out.append(f'\ndef universeLiteral{n} {{Γ : Context}} : Tm (universeType{n+1} (Γ := Γ)) := encodeType{n+1} universeType{n}\n')
out.append('\nend Jihoo.NativeKernel.Environment.Semantics.Contextual\n')
Path('Jihoo/NativeContextualUniverseCodes.lean').write_text(''.join(out))
