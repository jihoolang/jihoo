import Jihoo.NativeEnvironmentGhostMetatheory

/-! Ghost context conversion is derived from simultaneous typed substitution.
Lookup annotations are related by actual ACU conversion, never by a supplied
output typing derivation. The checked environment remains fixed. -/
namespace Jihoo.NativeKernel.Environment.Ghost

def ContextConversion (source target : Context) : Prop :=
  ∀ index binding, lookup source index = some binding →
    ∃ replacement, lookup target index = some replacement ∧ replacement.erased = binding.erased ∧
      Conversion.Conv binding.ty replacement.ty

theorem ContextConversion.refl (ctx : Context) : ContextConversion ctx ctx :=
  fun _ binding found => ⟨binding, found, rfl, .refl _⟩

theorem ContextConversion.trans (first : ContextConversion source middle) (second : ContextConversion middle target) :
    ContextConversion source target := by
  intro index binding found
  obtain ⟨next, selected, erased, converted⟩ := first index binding found
  obtain ⟨last, lastSelected, lastErased, lastConverted⟩ := second index next selected
  exact ⟨last, lastSelected, lastErased.trans erased, .trans converted lastConverted⟩

theorem ContextConversion.extend (related : ContextConversion source target)
    (domain : Conversion.Conv original replacement) (erased : Bool) :
    ContextConversion (⟨original, erased⟩ :: source) (⟨replacement, erased⟩ :: target) := by
  intro index binding found
  cases index with
  | zero =>
      simp only [lookup, Option.some.injEq] at found
      cases found
      exact ⟨⟨replacement.rename Nat.succ, erased⟩, rfl, rfl, domain.renaming Nat.succ⟩
  | succ index =>
      simp only [lookup] at found
      obtain ⟨prior, selected, same⟩ := Option.map_eq_some_iff.mp found
      subst binding
      obtain ⟨next, nextSelected, nextErased, nextConverted⟩ := related index prior selected
      exact ⟨⟨next.ty.rename Nat.succ, next.erased⟩,
        by simp only [lookup, nextSelected, Option.map_some], nextErased, nextConverted.renaming Nat.succ⟩

theorem ContextConversion.substitution (related : ContextConversion source target) :
    Substitution env source target Term.var := by
  intro index binding found
  obtain ⟨next, selected, erased, converted⟩ := related index binding found
  simpa only [Term.subst_id] using HasType.convert (HasType.var selected (Or.inl rfl)) converted.symm

end Jihoo.NativeKernel.Environment.Ghost
namespace Jihoo.NativeKernel.Environment

theorem HasType.ghostContext (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env source mode term type) (related : Ghost.ContextConversion source target) :
    HasType env target true term type := by
  simpa only [Term.subst_id] using typed.ghostSubstitution wellFormed related.substitution

theorem Binder.ghostContext (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : Binder env source erased domain sort) (related : Ghost.ContextConversion source target) :
    Binder env target erased domain sort := by
  simpa only [Term.subst_id] using typed.ghostSubstitution wellFormed related.substitution

end Jihoo.NativeKernel.Environment
