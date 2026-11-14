import Jihoo.NativeBackMetatheory
import Jihoo.NativeEnvironmentExtension

namespace Jihoo.NativeKernel.Environment

theorem Owned.of_conversion (converted : Conversion.Conv env A B) (owned : Owned env B) : Owned env A := by
  cases owned with
  | buffer final => exact .buffer (.trans converted final)
  | family found boxed final => exact .family found boxed (.trans converted final)

/-- Full ACU congruence changes neither the original loop bound's position nor
the accumulator's two distinct weakenings in the exact native telescope. -/
theorem foldAccumulatorBodyType_congr (closed : Conversion.Closed env)
    (count : Conversion.Conv env n m) (accumulator : Conversion.Conv env A B) :
    Conversion.Conv env (foldAccumulatorBodyType n A) (foldAccumulatorBodyType m B) := by
  have proofType : Conversion.Conv env (.lt (.var 0) (n.rename Nat.succ)) (.lt (.var 0) (m.rename Nat.succ)) :=
    .node .lt (.cons (.refl _) (.cons (count.renaming Nat.succ closed) .nil))
  have stepType : Conversion.Conv env
      (.pi false (A.rename (fun x => x + 2)) (A.rename (fun x => x + 3)))
      (.pi false (B.rename (fun x => x + 2)) (B.rename (fun x => x + 3))) :=
    .node (.pi false) (.cons (accumulator.renaming (fun x => x + 2) closed)
      (.cons (accumulator.renaming (fun x => x + 3) closed) .nil))
  exact .node (.pi false) (.cons (.refl _) (.cons
    (.node (.pi true) (.cons proofType (.cons stepType .nil))) .nil))


theorem foldAccumulatorBodyType_count_congr (closed : Conversion.Closed env) (converted : Conversion.Conv env n m) :
    Conversion.Conv env (foldAccumulatorBodyType n accumulator) (foldAccumulatorBodyType m accumulator) :=
  foldAccumulatorBodyType_congr closed converted (.refl _)

theorem foldAccumulatorBodyType_accumulator_congr (closed : Conversion.Closed env) (converted : Conversion.Conv env A B) :
    Conversion.Conv env (foldAccumulatorBodyType count A) (foldAccumulatorBodyType count B) :=
  foldAccumulatorBodyType_congr closed (.refl _) converted

theorem ghost_iteration_body_allowed (env : Environment) (body : Term) : IterationBodyAllowed env true body :=
  Or.inl rfl

theorem ghost_iteration_motive_allowed (env : Environment) (proof : Bool) (motive : Term) :
    IterationMotiveAllowed env true proof motive := Or.inl rfl

end Jihoo.NativeKernel.Environment
