import Jihoo.NativeBackMetatheory
import Jihoo.NativeEnvironmentExtension

namespace Jihoo.NativeKernel.Environment

theorem Owned.of_conversion (converted : Conversion.Conv A B) (owned : Owned env B) : Owned env A := by
  cases owned with
  | buffer final => exact .buffer (.trans converted final)
  | family found boxed final => exact .family found boxed (.trans converted final)

/-- Full ACU congruence changes neither the original loop bound's position nor
the accumulator's two distinct weakenings in the exact native telescope. -/
theorem foldAccumulatorBodyType_congr
    (count : Conversion.Conv n m) (accumulator : Conversion.Conv A B) :
    Conversion.Conv (foldAccumulatorBodyType n A) (foldAccumulatorBodyType m B) := by
  have proofType : Conversion.Conv (.lt (.var 0) (n.rename Nat.succ)) (.lt (.var 0) (m.rename Nat.succ)) :=
    .node .lt (.cons (.refl _) (.cons (count.renaming Nat.succ) .nil))
  have stepType : Conversion.Conv
      (.pi false (A.rename (fun x => x + 2)) (A.rename (fun x => x + 3)))
      (.pi false (B.rename (fun x => x + 2)) (B.rename (fun x => x + 3))) :=
    .node (.pi false) (.cons (accumulator.renaming (fun x => x + 2))
      (.cons (accumulator.renaming (fun x => x + 3)) .nil))
  exact .node (.pi false) (.cons (.refl _) (.cons
    (.node (.pi true) (.cons proofType (.cons stepType .nil))) .nil))


theorem foldAccumulatorBodyType_count_congr (converted : Conversion.Conv n m) :
    Conversion.Conv (foldAccumulatorBodyType n accumulator) (foldAccumulatorBodyType m accumulator) :=
  foldAccumulatorBodyType_congr converted (.refl _)

theorem foldAccumulatorBodyType_accumulator_congr (converted : Conversion.Conv A B) :
    Conversion.Conv (foldAccumulatorBodyType count A) (foldAccumulatorBodyType count B) :=
  foldAccumulatorBodyType_congr (.refl _) converted

theorem ghost_iteration_body_allowed (env : Environment) (body : Term) : IterationBodyAllowed env true body :=
  Or.inl rfl

theorem ghost_iteration_motive_allowed (env : Environment) (proof : Bool) (motive : Term) :
    IterationMotiveAllowed env true proof motive := Or.inl rfl

end Jihoo.NativeKernel.Environment
