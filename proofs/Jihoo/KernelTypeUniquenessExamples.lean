import Jihoo.KernelTypeUniqueness

/-! Dependent application and concrete rejection consequences of type
uniqueness. These examples use the declarative judgment independently of any
algorithmic inference result. -/
namespace Jihoo.CoreBridge.Raw.Beta.UniquenessExamples

private def sevenProof : Raw :=
  .app (.lam false .u64 (.refl (.var 0))) (.natural 7)

private theorem sevenProof_typed {Γ : Context} :
    HasType Γ sevenProof (.eq (.natural 7) (.natural 7)) := by
  have hf : HasType Γ (.lam false .u64 (.refl (.var 0)))
      (.pi false .u64 (.eq (.var 0) (.var 0))) :=
    .lam .u64 rfl (.refl (.var (by simp [Context.extend, rename])))
  simpa [sevenProof, subst, single] using
    HasType.app hf (show HasType Γ (.natural 7) .u64 from .natural (by decide))

theorem dependent_equality_endpoints_unique
    (h : HasType Γ sevenProof (.eq (.natural m) (.natural n))) : m = 7 ∧ n = 7 := by
  have hc := (h.unique sevenProof_typed).eq_injective
  exact ⟨hc.1.natural_injective, hc.2.natural_injective⟩

theorem dependent_false_equality_rejected :
    ¬ HasType Γ sevenProof (.eq (.natural 7) (.natural 8)) := by
  intro h
  have bad := (dependent_equality_endpoints_unique h).2
  contradiction

private theorem singleton_typed {Γ : Context} :
    HasType Γ (.elements [.integer 7]) (.array (.natural 1)) := by
  apply HasType.elements
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact .integer (by decide) (by decide)
  · decide

theorem singleton_length_unique
    (h : HasType Γ (.elements [.integer 7]) (.array (.natural n))) : n = 1 :=
  h.array_length_unique singleton_typed

theorem singleton_wrong_length_rejected :
    ¬ HasType Γ (.elements [.integer 7]) (.array (.natural 2)) := by
  intro h
  have bad := singleton_length_unique h
  contradiction

theorem scalar_confusion_rejected : ¬ HasType Γ (.natural 7) .i64 := by
  intro h
  exact (show HasType Γ (.natural 7) .u64 from .natural (by decide)).no_scalar_confusion h

theorem converted_reflexivity_rejected :
    ¬ HasType Γ (.refl (.uadd (.natural 1) (.natural 2)))
      (.eq (.natural 3) (.natural 4)) :=
  HasType.refl_false_equality_rejected (by decide)

end Jihoo.CoreBridge.Raw.Beta.UniquenessExamples
