import Jihoo.SizedErasureCompiler
import Jihoo.SizedErasureForward
import Jihoo.SizedCompositionExamples

/-! Kernel-checked compaction of the complete dependent composition fixture.
The target is one fixed compact syntax tree for every closing n/m/i, including
both comparison arms. No source type/proof node IDs occur in the target. -/
namespace Jihoo.SizedErasureExamples
open SizedErasure

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

abbrev graph := SizedCompositionGraph.graph

def inputMask : Mask := [true, true, true, true]
def runtimeEnv (n m i value : Nat) : Env :=
  [.scalar value, .nat i, .nat m, .nat n]

/-- Actual compact indices are explicit, so this checks more than existence
of an unspecified target. In particular the true branches add no ghost slot. -/
def target : Term :=
  .app (.allocate (.var 3) (.var 0))
    (.ifLt (.var 2) (.var 4)
      (.ownedLend 0 (.var 4) (.var 3)
        (.app (.app (.var 1) (.var 0))
          (.ifLt (.literal 0) (.var 6)
            (.lend 0 (.literal 0) (.free 3 (.free 0 (.var 1))))
            (.free 1 (.free 0 (.var 4))))))
      (.free 0 (.scalar 99)))

theorem compiled : compileTarget graph 128 inputMask 81 = some target := by rfl

theorem erased : Erases graph inputMask 81 target := compileTarget_correct compiled

theorem no_fuel : compileTarget graph 0 inputMask 81 = none := by rfl

/-- Runtime payload use cannot read a slot declared erased. -/
theorem erased_payload_rejected :
    compileTarget graph 128 [false, true, true, true] 81 = none := by rfl

theorem inputs_related (n m i value : Nat) :
    EnvRel inputMask (SizedCompositionExamples.inputEnv n m i value) (runtimeEnv n m i value) :=
  .consKeep (.scalar value) (.consKeep (.nat i) (.consKeep (.nat m) (.consKeep (.nat n) .nil)))

/-- The first true comparison arm really has six source slots but only five
runtime slots, retaining the original owner at compact index zero. -/
theorem outer_true_compacted (n m i value owner : Nat) :
    EnvRel (false :: true :: inputMask)
      (.ghost :: .owner owner :: SizedCompositionExamples.inputEnv n m i value)
      (.owner owner :: runtimeEnv n m i value) ∧
    (.ghost :: .owner owner :: SizedCompositionExamples.inputEnv n m i value).length = 6 ∧
    (.owner owner :: runtimeEnv n m i value).length = 5 ∧
    rank (false :: true :: inputMask) 1 = 0 :=
  ⟨.consGhost (.consKeep (.owner owner) (inputs_related n m i value)), rfl, rfl, rfl⟩

/-- The second true comparison removes another proof slot. The moved owner,
original owner, and stale copy aliases remain runtime values; only proof slots
are removed. Static source authority, not slot deletion, rejects stale aliases. -/
def innerMask : Mask := [false, true, true, true, false, true, true, true, true, true]

theorem inner_true_compacted (n m i value original copied : Nat) :
    EnvRel innerMask
      ([.ghost, .owner copied, .owner original, .owner copied, .ghost, .owner original] ++
        SizedCompositionExamples.inputEnv n m i value)
      ([.owner copied, .owner original, .owner copied, .owner original] ++ runtimeEnv n m i value) ∧
    innerMask.length = 10 ∧ rank innerMask innerMask.length = 8 ∧
    rank innerMask 1 = 0 ∧ rank (true :: true :: innerMask) 4 = 3 :=
  ⟨.consGhost (.consKeep (.owner copied) (.consKeep (.owner original)
    (.consKeep (.owner copied) (.consGhost (.consKeep (.owner original) (inputs_related n m i value)))))),
    rfl, rfl, rfl, rfl⟩

/-- The compiler and bridge derive a target execution, rather than assuming
that the independent compact interpreter happens to run. -/
theorem target_total (n m i value : Nat) :
    ∃ result events t, Eval (runtimeEnv n m i value) target SizedBufferHeap.empty result events t ∧
      SizedBufferHeap.Steps SizedBufferHeap.empty events t ∧ SizedBufferHeap.Valid t ∧
      SizedCoreTyping.Post .scalar t result.embed ∧ SizedCoreTyping.Account [] result.embed events :=
  erased.total_accounted (inputs_related n m i value) (SizedCompositionExamples.body_typed n m i)
    (SizedCompositionExamples.input_agrees n m i value) ⟨rfl, by simp⟩
    SizedBufferHeap.empty_valid LinearHeapPrograms.empty_owns

theorem every_target_value
    (run : Eval (runtimeEnv n m i value) target SizedBufferHeap.empty result events t) :
    result = .scalar (if i < n then value else 99) := by
  have source := erased.backward (inputs_related n m i value) run
  have eq := SizedCompositionExamples.every_run_value source
  exact Value.embed_inj.mp eq

theorem every_target_no_live
    (run : Eval (runtimeEnv n m i value) target SizedBufferHeap.empty result events t) :
    ∀ x, t.heap.live x = false :=
  SizedCompositionExamples.every_run_no_live (erased.backward (inputs_related n m i value) run)

theorem every_target_safe
    (run : Eval (runtimeEnv n m i value) target SizedBufferHeap.empty result events t) :
    SizedBufferHeap.Steps SizedBufferHeap.empty events t ∧ SizedBufferHeap.Valid t ∧
      SizedCoreTyping.Post .scalar t result.embed :=
  erased.every_run_safe (inputs_related n m i value) (SizedCompositionExamples.body_typed n m i)
    (SizedCompositionExamples.input_agrees n m i value) ⟨rfl, by simp⟩
    SizedBufferHeap.empty_valid LinearHeapPrograms.empty_owns run

theorem every_target_accounted
    (run : Eval (runtimeEnv n m i value) target SizedBufferHeap.empty result events t) :
    SizedCoreTyping.Account [] result.embed events :=
  erased.every_run_accounted (inputs_related n m i value) (SizedCompositionExamples.body_typed n m i)
    (SizedCompositionExamples.input_agrees n m i value) ⟨rfl, by simp⟩
    SizedBufferHeap.empty_valid LinearHeapPrograms.empty_owns run

end Jihoo.SizedErasureExamples
