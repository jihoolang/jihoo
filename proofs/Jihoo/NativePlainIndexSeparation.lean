import Jihoo.NativePlainIndexRoots

namespace Jihoo.NativeKernel.Environment.Representation
open Environment.Conversion

theorem PlainIndices.not_buffer (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx mode term type) (plain : PlainIndices env ctx term) :
    ¬ Conv env term (.buffer n) := by
  intro converted
  obtain ⟨common, first, second⟩ := converted.church_rosser history.wellFormed.admissible
  have safe := (forward_plain_transform history first).preserves typed plain
  obtain ⟨children, rfl, kids⟩ := forward_rigid_shape second rfl rfl
  cases kids with | cons first rest => cases rest; exact safe.no_buffer history

theorem PlainIndices.not_ref (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx mode term type) (plain : PlainIndices env ctx term) :
    ¬ Conv env term (.ref owner) := by
  intro converted
  obtain ⟨common, first, second⟩ := converted.church_rosser history.wellFormed.admissible
  have safe := (forward_plain_transform history first).preserves typed plain
  obtain ⟨children, rfl, kids⟩ := forward_rigid_shape second rfl rfl
  cases kids with | cons first rest => cases rest; exact safe.no_ref history

theorem PlainIndices.not_back (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx mode term type) (plain : PlainIndices env ctx term) :
    ¬ Conv env term (.back erased owner motive) := by
  intro converted
  obtain ⟨common, first, second⟩ := converted.church_rosser history.wellFormed.admissible
  have safe := (forward_plain_transform history first).preserves typed plain
  obtain ⟨children, rfl, kids⟩ := forward_rigid_shape second rfl rfl
  cases kids with | cons first rest => cases rest with | cons second rest => cases rest; exact safe.no_back history

theorem PlainIndices.nonFunction (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx mode term type) (plain : PlainIndices env ctx term) : CodeKinds.PiSeparated env term := by
  intro erased domain result converted
  obtain ⟨common, first, second⟩ := converted.church_rosser history.wellFormed.admissible
  have safe := (forward_plain_transform history first).preserves typed plain
  obtain ⟨children, rfl, kids⟩ := forward_rigid_shape second rfl rfl
  cases kids with | cons first rest => cases rest with | cons second rest => cases rest; exact safe.no_pi history

theorem PlainIndices.not_boxed_family (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx mode term type) (plain : PlainIndices env ctx term)
    (found : env.families[family]? = some entry) (boxed : entry.boxed = true) :
    ¬ Conv env term (.node (.ind family count) indices) := by
  intro converted
  obtain ⟨common, first, second⟩ := converted.church_rosser history.wellFormed.admissible
  have safe := (forward_plain_transform history first).preserves typed plain
  obtain ⟨children, rfl, _⟩ := forward_rigid_shape second rfl rfl
  exact safe.no_boxed_family history found boxed

theorem PlainIndices.not_owned (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx mode term type) (plain : PlainIndices env ctx term) : ¬ Owned env term := by
  intro owned
  cases owned with
  | buffer converted => exact plain.not_buffer history typed converted
  | family found boxed converted => exact plain.not_boxed_family history typed found boxed converted

end Jihoo.NativeKernel.Environment.Representation
