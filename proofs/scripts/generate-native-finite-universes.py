"""Generate a finite Tarski hierarchy with one administrative top level.
All generated declarations are checked by Lean; this script is not an oracle.
"""
from pathlib import Path
LEVELS=34
UP=34
out=['import Jihoo.NativeTyping\n\n-- Host universe syntax needs room above the native administrative top.\nset_option maxUniverseOffset 40\n', '''/-! Concrete finite host universes for the native contextual model. Native
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
''']
for n in range(LEVELS): out.append(f'  | type{n} (carrier : Type {n}) : Universe (.type ⟨{n},by decide⟩)\n')
out.append('\ndef Carrier : {sort : LevelSort} → Universe sort → Type 34\n  | _, .proposition truth => ULift.{34} (PLift truth)\n')
for n in range(LEVELS):out.append(f'  | _, .type{n} carrier => ULift.{{34}} carrier\n')
for n in range(LEVELS):
 out.append(f'\ndef decode{n} : Universe (.type ⟨{n},by decide⟩) → Type {n}\n  | .type{n} carrier => carrier\n')
 out.append(f'\ntheorem encode_decode{n} (code : Universe (.type ⟨{n},by decide⟩)) : Universe.type{n} (decode{n} code) = code := by\n  cases code\n  rfl\n')
out.append('''
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
''')
for n in range(33):out.append(f'\ndef universe{n} : Universe (.type ⟨{n+1},by decide⟩) := .type{n+1} (Type {n})\n')
out.append('\nend Jihoo.NativeKernel.Environment.Semantics.Finite\n')
Path('Jihoo/NativeFiniteUniverses.lean').write_text(''.join(out))
