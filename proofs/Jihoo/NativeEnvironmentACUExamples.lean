import Jihoo.NativeEnvironmentCheckerSoundness

/-! Same-judgment regressions for the actual full-Term ACU converter. These
checks supply syntax and raw environments, never conversion certificates. -/
namespace Jihoo.NativeKernel.Environment.ACUIntegrationExamples

private def ctx : Context := [⟨.pi false .u64 .u64,false⟩]
private def atomA : Term := .app (.var 0) (.natural 1)
private def atomB : Term := .app (.var 0) (.natural 2)
private def left : Term := .uadd atomA atomB
private def right : Term := .uadd atomB atomA

/-- Arbitrary neutral application atoms pass through the same Env checker. -/
theorem nonaffine_type_indices_compare :
    Checker.check 12 empty ctx true (.refl left) (.eq right left) = true := by cbv

theorem nonaffine_type_indices_typed : HasType empty ctx true (.refl left) (.eq right left) :=
  Checker.check_sound nonaffine_type_indices_compare

/-- The previous bounded beta/arithmetic comparator did not sort these atoms. -/
theorem legacy_comparator_missed_nonaffine_acu :
    Jihoo.NativeKernel.Conversion.equal 12 left right = false := by cbv

theorem actual_acu_comparator_accepts_nonaffine_atoms : Conversion.equal 12 left right = true := by cbv

private def wrappedFunctionContext : Context :=
  [⟨.uadd (.pi false .u64 .u64) (.natural 0),false⟩]

theorem head_exposure_uses_full_acu :
    Checker.infer 12 empty wrappedFunctionContext true (.app (.var 0) (.natural 3)) = some .u64 := by cbv

theorem exposed_function_typed_in_same_judgment :
    HasType empty wrappedFunctionContext true (.app (.var 0) (.natural 3)) .u64 :=
  Checker.infer_sound head_exposure_uses_full_acu

private def aliasEnv : Environment :=
  ⟨#[⟨.univ 0,.buffer (.natural 2)⟩],#[]⟩
private def typeApplication : Term :=
  .app (.lam false (.univ 0) (.natural 0)) (.node (.global 0) [])

theorem unresolved_global_is_not_plain : plain aliasEnv (.node (.global 0) []) = false := by cbv

theorem global_buffer_alias_runtime_type_argument_rejected :
    Checker.infer 12 aliasEnv [] false typeApplication = none := by cbv

theorem global_buffer_alias_ghost_type_argument_accepted :
    Checker.infer 12 aliasEnv [] true typeApplication = some .u64 := by cbv

theorem ghost_global_application_typed : HasType aliasEnv [] true typeApplication .u64 :=
  Checker.infer_sound global_buffer_alias_ghost_type_argument_accepted

/-- The nonfunction property quantifies full ACU conversion, including zero. -/
theorem additive_hidden_function_is_not_nonFunction :
    ¬ nonFunction (.uadd (.pi false .u64 .u64) (.natural 0)) := by
  intro allowed
  exact allowed false .u64 .u64 (.zero _)

theorem untyped_proof_slots_remain_distinct :
    Conversion.equal 8 (.pack (.var 7) (.var 2) (.var 0)) (.pack (.var 7) (.var 2) (.var 1)) = false := by cbv

theorem head_exposure_propagates_bounded_refusal (failed : Conversion.normalize? fuel t = none) :
    Checker.expose fuel (some t) = none := by
  simpa only [Checker.expose,Option.bind_some] using failed

theorem failed_inference_stays_unexposed : Checker.expose 8 none = none := rfl

theorem old_conversion_embeds_in_actual_base (h : Jihoo.NativeKernel.Conversion.Conv a b) :
    Conversion.Conv a b := Conversion.ofLegacy h

theorem old_pure_typing_has_ghost_embedding (h : Jihoo.NativeKernel.HasType context mode t T) :
    HasType environment context true t T := ofPure h

end Jihoo.NativeKernel.Environment.ACUIntegrationExamples
