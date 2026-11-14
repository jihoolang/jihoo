"""Generate the checked dependent Pi closure of the finite semantic hierarchy."""
from pathlib import Path
out=['''import Jihoo.NativeFiniteUniverses
set_option maxUniverseOffset 40

/-! Concrete dependent Pi closure at every finite semantic universe, with
impredicative proposition codomains and actual lambda/application beta and eta.
Every generated case is checked by Lean; no candidate membership is assumed. -/
namespace Jihoo.NativeKernel.Environment.Semantics.Finite

universe u v w

structure PiStructure (domain : Sort u) (codomain : domain → Sort v) (function : Sort w) where
  lam : ((value : domain) → codomain value) → function
  app : function → (value : domain) → codomain value
  beta : ∀ body value, app (lam body) value = body value
  eta : ∀ value, lam (app value) = value

def liftedPiType (domain : Type u) (codomain : ULift.{34} domain → Type v) :
    PiStructure (ULift.{34} domain) (fun value => ULift.{34} (codomain value))
      (ULift.{34} ((value : domain) → codomain (ULift.up value))) where
  lam body := ⟨fun value => (body ⟨value⟩).down⟩
  app function value := ⟨function.down value.down⟩
  beta := by intro body value; cases value; rfl
  eta := by intro value; cases value; rfl

def liftedPiPropDomain (domain : Prop) (codomain : ULift.{34} (PLift domain) → Type v) :
    PiStructure (ULift.{34} (PLift domain)) (fun value => ULift.{34} (codomain value))
      (ULift.{34} ((value : domain) → codomain (ULift.up (PLift.up value)))) where
  lam body := ⟨fun value => (body ⟨⟨value⟩⟩).down⟩
  app function value := ⟨function.down value.down.down⟩
  beta := by intro body value; cases value with | up value => cases value; rfl
  eta := by intro value; cases value; rfl

def decodeProp : Universe .proposition → Prop
  | .proposition truth => truth

theorem encode_decodeProp (code : Universe .proposition) : Universe.proposition (decodeProp code) = code := by
  cases code
  rfl

def piProp (domain : Universe sort) (codomain : Carrier domain → Universe .proposition) :
    Universe .proposition := .proposition (∀ value,decodeProp (codomain value))

def piMeaningProp (domain : Universe sort) (codomain : Carrier domain → Universe .proposition) :
    PiStructure (Carrier domain) (fun value => Carrier (codomain value)) (Carrier (piProp domain codomain)) := by
  have canonical : codomain = fun value => Universe.proposition (decodeProp (codomain value)) := by
    funext value
    exact (encode_decodeProp _).symm
  rw [canonical]
  exact {
    lam := fun body => ⟨⟨fun value => (body value).down.down⟩⟩
    app := fun function value => ⟨⟨function.down.down value⟩⟩
    beta := by intros; rfl
    eta := by intros; rfl }
''']
for n in range(34):
 out.append(f'\ndef piType{n} (domain : Universe sort) (codomain : Carrier domain → Universe (.type ⟨{n},by decide⟩)) :\n    Universe (sort.pi (.type ⟨{n},by decide⟩)) :=\n  match domain with\n')
 out.append(f'  | .proposition truth => .type{n} ((value : truth) → decode{n} (codomain ⟨⟨value⟩⟩))\n')
 for m in range(34):out.append(f'  | .type{m} carrier => .type{max(m,n)} ((value : carrier) → decode{n} (codomain ⟨value⟩))\n')
 out.append(f'\ndef piMeaning{n} (domain : Universe sort) (codomain : Carrier domain → Universe (.type ⟨{n},by decide⟩)) :\n    PiStructure (Carrier domain) (fun value => Carrier (codomain value)) (Carrier (piType{n} domain codomain)) := by\n')
 out.append(f'  have canonical : codomain = fun value => Universe.type{n} (decode{n} (codomain value)) := by\n    funext value\n    exact (encode_decode{n} _).symm\n  rw [canonical]\n  cases domain with\n')
 out.append(f'  | proposition truth => exact liftedPiPropDomain truth (fun value => decode{n} (codomain value))\n')
 for m in range(34):out.append(f'  | type{m} carrier => exact liftedPiType carrier (fun value => decode{n} (codomain value))\n')
out.append('\ndef pi (domain : Universe sort) (resultSort : LevelSort)\n    (codomain : Carrier domain → Universe resultSort) : Universe (sort.pi resultSort) :=\n  match resultSort with\n  | .proposition => piProp domain codomain\n')
for n in range(34):out.append(f'  | .type ⟨{n},_⟩ => piType{n} domain codomain\n')
out.append('  | .type ⟨n + 34,bound⟩ => False.elim (by omega)\n')
out.append('\ndef piMeaning (domain : Universe sort) (resultSort : LevelSort) (codomain : Carrier domain → Universe resultSort) :\n    PiStructure (Carrier domain) (fun value => Carrier (codomain value)) (Carrier (pi domain resultSort codomain)) :=\n  match resultSort with\n  | .proposition => piMeaningProp domain codomain\n')
for n in range(34):out.append(f'  | .type ⟨{n},_⟩ => piMeaning{n} domain codomain\n')
out.append('  | .type ⟨n + 34,bound⟩ => False.elim (by omega)\n')
out.append('\nend Jihoo.NativeKernel.Environment.Semantics.Finite\n')
Path('Jihoo/NativeFinitePi.lean').write_text(''.join(out))
