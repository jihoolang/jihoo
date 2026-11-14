import Jihoo.NativeTypeUniqueness

/-! Cross-mode uniqueness, universe ceilings and dependency-index regressions.
Positive typings come from the data-input checker; negative statements exclude
all declarative derivations, including arbitrary chains of type conversions. -/
namespace Jihoo.NativeKernel.TypeUniquenessExamples
open Conversion

private def values : Term := .elements 2 [.integer (-7), .integer 9]
private def identity : Term := .lam false (.univ 0) (.lam false (.var 0) (.var 0))
private def predicate : Term := .lam false .u64 (.eq (.var 0) (.var 0))

 theorem highest_universe_type : HasType [] true (.univ 31) (.univ 32) :=
  Checker.infer_sound (fuel := 8) (by cbv)

 theorem highest_universe_not_itself : ¬ HasType [] true (.univ 31) (.univ 31) :=
  HasType.no_type_in_type

 theorem successor_level_forced (h : HasType Γ mode (.univ 31) (.univ n)) : n = 32 :=
  h.universe_successor

 theorem ceiling_uniform (T : Term) : ¬ HasType Γ mode (.univ 32) T :=
  HasType.universe_limit_rejected (by decide)

 theorem scalar_cross_mode_separate (hu : HasType Γ false t .u64) : ¬ HasType Γ true t .i64 :=
  fun hi => hu.no_scalar_confusion hi

 theorem polymorphic_type_modes_agree
    (h : HasType [] true (.app (.app identity .u64) (.natural 7)) T) : Conv .u64 T := by
  exact Checker.infer_unique (fuel := 24) (mode := false) (by cbv) h

 theorem array_length_cannot_be_forged : ¬ HasType [] true values (.array (.natural 3)) := by
  intro forged
  have accepted : HasType [] false values (.array (.natural 2)) :=
    Checker.infer_sound (fuel := 8) (by cbv)
  have wrong : 2 = 3 := accepted.array_length_unique forged
  cases wrong

 theorem erased_function_flag_cannot_change :
    ¬ HasType [] true (.lam true .u64 (.refl (.var 0))) (.pi false .u64 T) := by
  intro forged
  have accepted : HasType [] false (.lam true .u64 (.refl (.var 0)))
      (.pi true .u64 (.eq (.var 0) (.var 0))) :=
    Checker.infer_sound (fuel := 12) (by cbv)
  have flags := accepted.function_unique forged
  cases flags.1

 theorem equality_proof_cannot_change_numerals :
    ¬ HasType Γ mode (.refl a) (.eq (.natural 0) (.natural 1)) :=
  HasType.refl_false_equality_rejected (by decide)

 theorem proposition_and_type_separate (hp : HasType Γ false t .prop) :
    ¬ HasType Γ true t (.univ n) := fun hu => hp.sorts_do_not_collapse hu

 theorem predicative_maximum_forced
    (h : HasType [] true (.pi false (.univ 0) (.univ 1)) (.univ n)) : n = 2 := by
  have accepted : HasType [] true (.pi false (.univ 0) (.univ 1)) (.univ 2) :=
    Checker.infer_sound (fuel := 12) (by cbv)
  exact h.universe_level_unique accepted

 theorem refinement_predicate_forced
    (h : HasType [] true (.pack predicate (.natural 7) (.refl (.natural 7))) (.refine q)) :
    Conv predicate q := by
  have accepted : HasType [] false (.pack predicate (.natural 7) (.refl (.natural 7))) (.refine predicate) :=
    Checker.infer_sound (fuel := 16) (by cbv)
  exact accepted.refinement_predicate_unique h

theorem conditional_scalar_type_unique :
    ¬ HasType [] true (.ifLt (.natural 0) (.natural 1) (.natural 7) (.natural 9)) .i64 := by
  intro forged
  have accepted : HasType [] false (.ifLt (.natural 0) (.natural 1) (.natural 7) (.natural 9)) .u64 :=
    Checker.infer_sound (fuel := 12) (by cbv)
  exact accepted.no_scalar_confusion forged

theorem conditional_function_type_unique
    (h : HasType [] true
      (.ifEq (.natural 0) (.natural 0) (.lam false .u64 (.var 0)) (.lam false .u64 (.var 0)))
      (.pi e A B)) : e = false ∧ Conv .u64 A ∧ Conv .u64 B := by
  have accepted : HasType [] false
      (.ifEq (.natural 0) (.natural 0) (.lam false .u64 (.var 0)) (.lam false .u64 (.var 0)))
      (.pi false .u64 .u64) := Checker.infer_sound (fuel := 16) (by cbv)
  have unique := h.function_unique accepted
  exact ⟨unique.1, .symm unique.2.1, .symm unique.2.2⟩

theorem absurd_target_type_unique
    (h : HasType [⟨.lt (.natural 0) (.natural 0), true⟩] true (.absurd .u64 (.var 0)) T) :
    Conv .u64 T := by
  exact Checker.infer_unique (fuel := 12) (mode := false) (by cbv) h

theorem absurd_universe_ceiling_preserved
    (h : HasType [⟨.lt (.natural 0) (.natural 0), true⟩] true (.absurd (.univ 31) (.var 0)) (.univ n)) :
    n = 31 := by
  have accepted : HasType [⟨.lt (.natural 0) (.natural 0), true⟩] false
      (.absurd (.univ 31) (.var 0)) (.univ 31) := Checker.infer_sound (fuel := 12) (by cbv)
  exact h.universe_level_unique accepted

private def foldBody : Term :=
  .lam false .u64 (.lam true (.lt (.var 0) (.natural 2))
    (.lam false .i64 (.arith .add (.var 0) (.integer 1))))

private def dataMotive : Term := .lam false .u64 .u64
private def dataBody : Term :=
  .lam false .u64 (.lam true (.lt (.var 0) (.natural 2))
    (.lam false .u64 (.uadd (.var 0) (.natural 1))))

private def proofMotive : Term := .lam false .u64 (.eq (.var 0) (.var 0))
private def proofBody : Term :=
  .lam false .u64 (.lam true (.lt (.var 0) (.natural 2))
    (.lam true (.eq (.var 1) (.var 1)) (.refl (.uadd (.var 2) (.natural 1)))))

theorem fold_result_cannot_be_unsigned :
    ¬ HasType [] true (.fold (.natural 2) (.integer 0) foldBody) .u64 := by
  intro forged
  have accepted : HasType [] false (.fold (.natural 2) (.integer 0) foldBody) .i64 :=
    Checker.infer_sound (fuel := 32) (by cbv)
  exact forged.no_scalar_confusion accepted

theorem data_loop_motive_result_unique
    (h : HasType [] true (.loop (.natural 2) dataMotive (.natural 0) dataBody) T) :
    Conv (.app dataMotive (.natural 2)) T :=
  Checker.infer_unique (fuel := 32) (mode := false) (by cbv) h

theorem proof_loop_endpoint_cannot_be_forged :
    ¬ HasType [] true (.loop (.natural 2) proofMotive (.refl (.natural 0)) proofBody)
      (.eq (.natural 2) (.natural 3)) := by
  intro forged
  have accepted : HasType [] false (.loop (.natural 2) proofMotive (.refl (.natural 0)) proofBody)
      (.eq (.natural 2) (.natural 2)) := Checker.check_sound (fuel := 32) (by cbv)
  have wrong : 2 = 3 := (accepted.equality_indices_unique forged).2.natural_injective
  cases wrong

theorem loop_proof_data_flag_cannot_change
    (h : HasType [] true proofMotive (.pi false .u64 (.univ 0))) : False := by
  have accepted : HasType [] false proofMotive (.pi false .u64 .prop) :=
    Checker.infer_sound (fuel := 16) (by cbv)
  have flags : true = false := accepted.loop_proof_flag_unique h
  cases flags

end Jihoo.NativeKernel.TypeUniquenessExamples
