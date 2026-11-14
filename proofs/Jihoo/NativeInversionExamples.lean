import Jihoo.NativeRootPreservation

/-! Converted contexts, conversion-chain inversion and concrete typed root
contractions. These examples use independent typing and conversion premises. -/
namespace Jihoo.NativeKernel.InversionExamples

private theorem variable0 : HasType [⟨.u64,false⟩] true (.var 0) .u64 :=
  .var (b := ⟨.u64,false⟩) (by simp [lookup,Term.rename,renameArgs]) (Or.inl rfl)

private def alias : Term := .app (.lam false .u64 .u64) (.natural 7)

private theorem alias_conversion : Conversion.Conv .u64 alias := by
  have beta := Conversion.Conv.beta false .u64 .u64 (.natural 7)
  exact .symm (by simpa [alias,Term.subst,substArgs] using beta)

theorem converted_context : HasType [⟨alias,false⟩] true (.refl (.var 0)) (.eq (.var 0) (.var 0)) := by
  exact (HasType.refl (ghost := true) variable0).ghostContextConversion
    ((Ghost.ContextConversion.refl []).extend alias_conversion false)

theorem flag_change_rejected :
    ¬ Ghost.ContextConversion [⟨.u64,false⟩] [⟨.u64,true⟩] := by
  intro h
  obtain ⟨b,hb,he,hconv⟩ := h 0 ⟨.u64,false⟩ (by simp [lookup,Term.rename,renameArgs])
  simp [lookup,Term.rename,renameArgs] at hb
  cases hb
  contradiction

private def expandedPi : Term := .app (.lam false .u64 (.pi false .u64 .u64)) (.natural 7)

private theorem expanded_pi_conversion : Conversion.Conv (.pi false .u64 .u64) expandedPi := by
  have beta := Conversion.Conv.beta false .u64 (.pi false .u64 .u64) (.natural 7)
  exact .symm (by simpa [expandedPi,Term.subst,substArgs,Op.binders,liftSub] using beta)

theorem lambda_inversion_through_conversion :
    ∃ s B, Binder [] false .u64 s ∧ HasType [⟨.u64,false⟩] true (.var 0) B ∧
      Conversion.Conv (.pi false .u64 B) expandedPi := by
  have domain : Binder [] false .u64 (.type 0) := .intro .u64 (by simp [binderAllowed])
  exact (HasType.convert (.lam domain variable0)
    (.trans (.refl _) expanded_pi_conversion)).lamView

theorem read_preserves_type : HasType [] true (.integer (-7)) .i64 := by
  have element : HasType [] true (.integer (-7)) .i64 := .integer (by decide) (by decide)
  have array : HasType [] true (.elements 1 [.integer (-7)]) (.array (.natural 1)) :=
    .elements rfl (by decide) (by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact element)
  have index : HasType [] true (.index (.elements 1 [.integer (-7)]) (.natural 0)
      (.decide (.natural 0) (.natural 1))) .i64 :=
    .index array (.natural (by decide)) (.decide (by decide) (by decide) (by decide))
  exact index.ghostRead rfl

theorem add_preserves_converted_type : HasType [] true (.natural 3) alias := by
  have addition : HasType [] false (.uadd (.natural 1) (.natural 2)) .u64 :=
    .uadd (.natural (by decide)) (.natural (by decide))
  exact (addition.convert alias_conversion).ghostAdd (by decide)

end Jihoo.NativeKernel.InversionExamples
