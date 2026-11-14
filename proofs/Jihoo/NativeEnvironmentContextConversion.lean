import Jihoo.NativeEnvironmentGhostMetatheory

/-! Ghost context conversion is derived from simultaneous typed substitution.
Lookup annotations are related by actual ACU conversion, never by a supplied
output typing derivation. The checked environment remains fixed. -/
namespace Jihoo.NativeKernel.Environment.Ghost

def ContextConversion (env : Environment) (source target : Context) : Prop :=
  ∀ index binding, lookup source index = some binding →
    ∃ replacement, lookup target index = some replacement ∧ replacement.erased = binding.erased ∧
      Conversion.Conv env binding.ty replacement.ty

theorem ContextConversion.refl (env : Environment) (ctx : Context) : ContextConversion env ctx ctx :=
  fun _ binding found => ⟨binding, found, rfl, .refl _⟩

theorem ContextConversion.trans (first : ContextConversion env source middle) (second : ContextConversion env middle target) :
    ContextConversion env source target := by
  intro index binding found
  obtain ⟨next, selected, erased, converted⟩ := first index binding found
  obtain ⟨last, lastSelected, lastErased, lastConverted⟩ := second index next selected
  exact ⟨last, lastSelected, lastErased.trans erased, .trans converted lastConverted⟩

theorem ContextConversion.extend (related : ContextConversion env source target)
    (domain : Conversion.Conv env original replacement) (erased : Bool) (closed : Conversion.Closed env) :
    ContextConversion env (⟨original, erased⟩ :: source) (⟨replacement, erased⟩ :: target) := by
  intro index binding found
  cases index with
  | zero =>
      simp only [lookup, Option.some.injEq] at found
      cases found
      exact ⟨⟨replacement.rename Nat.succ, erased⟩, rfl, rfl, domain.renaming Nat.succ closed⟩
  | succ index =>
      simp only [lookup] at found
      obtain ⟨prior, selected, same⟩ := Option.map_eq_some_iff.mp found
      subst binding
      obtain ⟨next, nextSelected, nextErased, nextConverted⟩ := related index prior selected
      exact ⟨⟨next.ty.rename Nat.succ, next.erased⟩,
        by simp only [lookup, nextSelected, Option.map_some], nextErased, nextConverted.renaming Nat.succ closed⟩

theorem ContextConversion.substitution (related : ContextConversion env source target) :
    Substitution env source target Term.var := by
  intro index binding found
  obtain ⟨next, selected, erased, converted⟩ := related index binding found
  simpa only [Term.subst_id] using HasType.convert (HasType.var selected (Or.inl rfl)) converted.symm

end Jihoo.NativeKernel.Environment.Ghost
namespace Jihoo.NativeKernel.Environment

theorem HasType.ghostContext (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env source mode term type) (related : Ghost.ContextConversion env source target) :
    HasType env target true term type := by
  simpa only [Term.subst_id] using typed.ghostSubstitution wellFormed related.substitution

theorem Binder.ghostContext (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : Binder env source erased domain sort) (related : Ghost.ContextConversion env source target) :
    Binder env target erased domain sort := by
  simpa only [Term.subst_id] using typed.ghostSubstitution wellFormed related.substitution

end Jihoo.NativeKernel.Environment
