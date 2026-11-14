import Jihoo.NativeAtomicSupport
import Jihoo.NativeQuotientTypingBoundary
import Jihoo.NativeAtomicObservation
import Jihoo.NativeSemanticUniverseBoundary

/-! Real semantic certificates use independent actual typing, concrete forward
normalization, and recomputed checked program history. -/
namespace Jihoo.NativeKernel.Environment.Semantics.Examples

private theorem emptyHistory : UnifiedProgram.UnifiedProgramChecked [] [] empty := .empty

private theorem emptyWellFormed : UnifiedProgram.EnvWellFormed empty :=
  UnifiedProgram.checkProgram_wellFormed
    (by cbv : UnifiedProgram.checkProgram 24 24 [] [] = some empty)

private def reflexiveFunction : Term := .lam false .u64 (.refl (.var 0))
private def applied : Term := .app reflexiveFunction (.natural 7)
private def equalSeven : Term := .eq (.natural 7) (.natural 7)

theorem dependent_beta_realized : AtomicTruth empty equalSeven := by
  have typed : HasType empty [] false applied equalSeven := Checker.check_sound
    (by cbv : Checker.check 24 empty [] false applied equalSeven = true)
  have normalized : Conversion.normalize? empty 4 applied = some (.refl (.natural 7)) := by cbv
  have output : HasType empty [] true (.refl (.natural 7)) equalSeven := .refl (.natural (by decide))
  have supportedOutput : AtomicSupported output := .refl (.natural (by decide))
  have support : AtomicSupported typed := .forward emptyHistory typed
    (Conversion.normalize?_forward normalized) supportedOutput
  exact support.realize emptyWellFormed

/-- Saturated dependent functions use actual beta conversion, while the
native domain formation is independently checked above. -/
theorem dependent_candidate_lambda :
    pi (proposition (env := empty) True) (constant (equality (.natural 7) (.natural 7))) reflexiveFunction := by
  apply pi_lambda
  intro argument admitted
  exact .refl _

theorem observed_addition : ∃ observed : NumeralObservation empty (.uadd (.natural 2) (.natural 3)), observed.value = 5 :=
  observeNumeral_sound (by cbv : observeNumeral empty 4 (.uadd (.natural 2) (.natural 3)) = some 5)

theorem bounded_cancellation_realized : AtomicTruth empty (.lt (.natural 1) (.natural 3)) := by
  have one : HasType empty [] true (.natural 1) .u64 := .natural (by decide)
  have three : HasType empty [] true (.natural 3) .u64 := .natural (by decide)
  have two : HasType empty [] true (.natural 2) .u64 := .natural (by decide)
  have initial : HasType empty [] true (.decide (.natural 1) (.natural 3)) (.lt (.natural 1) (.natural 3)) :=
    .decide (by decide) (by decide) (by decide)
  have initialSupported : AtomicSupported initial := .decide (by decide) (by decide) (by decide)
  let n1 := NumeralObservation.literal (env := empty) (value := 1) (by decide)
  let n3 := NumeralObservation.literal (env := empty) (value := 3) (by decide)
  let n2 := NumeralObservation.literal (env := empty) (value := 2) (by decide)
  have added := HasType.ltAdd (ghost := true) one three two initial
  have addedSupported : AtomicSupported added :=
    .ltAdd one three two initial initialSupported n1 n3 n2 (by decide) (by decide)
  have cancelled := HasType.ltCancel (ghost := true) one three two added
  have cancelledSupported : AtomicSupported cancelled :=
    .ltCancel one three two added addedSupported n1 n3 n2 (by decide) (by decide)
  exact cancelledSupported.realize emptyWellFormed

private def declaration : GlobalDeclaration := ⟨.eq (.natural 0) (.natural 0),.refl (.natural 0)⟩
private def checkedEnv : Environment := ⟨#[declaration],#[]⟩
private theorem checkedHistory : UnifiedProgram.UnifiedProgramChecked [declaration] [] checkedEnv :=
  UnifiedProgram.checkProgram_sound
    (by cbv : UnifiedProgram.checkProgram 24 24 [declaration] [] = some checkedEnv)

/-- The proof realization comes from the actual earlier prefix's body, never
from an assumed semantic interpretation of the final environment table. -/
theorem checked_global_realized : AtomicTruth checkedEnv (.eq (.natural 0) (.natural 0)) := by
  have found : checkedEnv.globals[0]? = some declaration := rfl
  obtain ⟨origin⟩ := global_origin checkedHistory found
  have body : HasType origin.earlier [] true declaration.value declaration.type := .refl (.natural (by decide))
  have supportedBody : AtomicSupported body := .refl (.natural (by decide))
  have global : HasType checkedEnv [] true (.node (.global 0) [])
      (declaration.type.rename (fun x => x + ([] : Context).length)) := .global found
  have supportedGlobal : AtomicSupported global := .global checkedHistory found origin body supportedBody
  simpa only [declaration,Term.rename,renameArgs,Op.binders,liftRenaming] using supportedGlobal.realize checkedHistory.wellFormed

private abbrev allocated : Term := .alloc (.natural 2) (.integer 0)
private abbrev proof : Term := .decide (.natural 0) (.natural 2)
private def continuation : Term :=
  .lam false .i64 (.lam false (.buffer (.natural 2)) (.free (.var 0) (.refl (.natural 0))))
private abbrev answer : Term := .eq (.natural 0) (.natural 0)

theorem load_logical_realized : AtomicTruth empty answer := by
  have owner : HasType empty [] true allocated (.buffer (.natural 2)) :=
    Checker.infer_sound (fuel := 24) (by cbv)
  have index : HasType empty [] true (.natural 0) .u64 := .natural (by decide)
  have bound : HasType empty [] true proof (.lt (.natural 0) (.natural 2)) := .decide (by decide) (by decide) (by decide)
  have function : HasType empty [] true continuation (.pi false .i64 (.pi false (.buffer (.natural 2)) answer)) :=
    Checker.check_sound (by cbv : Checker.check 32 empty [] true continuation
      (.pi false .i64 (.pi false (.buffer (.natural 2)) answer)) = true)
  have valueConv : Conversion.Conv empty .i64 .i64 := .refl _
  have ownerConv : Conversion.Conv empty (.buffer (.natural 2)) (.buffer ((Term.natural 2).rename Nat.succ)) := by
    simpa only [Term.rename,renameArgs] using EnvironmentDelta.Basis.Conv.refl (.buffer (.natural 2))
  have resultConv : Conversion.Conv empty answer answer := .refl _
  have lowered : PartialRenaming.shift (-2) 0 answer = some answer := by cbv
  have witness := load_logical_witness emptyWellFormed.closed owner function valueConv ownerConv resultConv lowered
  have normalized : Conversion.normalize? empty 64 (.app (.app continuation (.integer 0)) allocated) =
      some (.free allocated (.refl (.natural 0))) := by cbv
  have body : HasType empty [] true (.refl (.natural 0)) answer := .refl (.natural (by decide))
  have supportedBody : AtomicSupported body := .refl (.natural (by decide))
  have rest : HasType empty [] true (.free allocated (.refl (.natural 0))) answer := .free owner body
  have supportedRest : AtomicSupported rest := .free owner body supportedBody
  have supportedWitness : AtomicSupported witness :=
    .forward emptyHistory witness (Conversion.normalize?_forward normalized) supportedRest
  have loaded := HasType.load owner index bound function valueConv ownerConv resultConv lowered (Or.inl rfl)
  have supportedLoad : AtomicSupported loaded :=
    .load emptyWellFormed.closed owner index bound function valueConv ownerConv resultConv lowered (Or.inl rfl) supportedWitness
  exact supportedLoad.realize emptyWellFormed

theorem false_equality_certificate_rejected
    (typed : HasType empty [] mode term (.eq (.natural 0) (.natural 1))) : ¬ AtomicSupported typed :=
  no_supported_false_equality emptyWellFormed (by decide) typed

theorem false_less_certificate_rejected
    (typed : HasType empty [] mode term (.lt (.natural 0) (.natural 0))) : ¬ AtomicSupported typed :=
  no_supported_false_less emptyWellFormed (by decide) typed

example : validateAtomic 24 4 empty applied (.equal 7 7) = true := by cbv
example : validateAtomic 24 4 empty applied (.equal 7 8) = false := by cbv
example : validateAtomic 24 4 empty (.strict .u64 proof) (.less 0 2) = true := by cbv
example : validateAtomic 24 4 empty (.free allocated proof) (.less 0 2) = true := by cbv

/-- These proofs have constructive support above; the small executable head
observer declines opaque Load; checked delta normalization now exposes the Global proof. -/
example : validateAtomic 32 4 empty (.load allocated (.natural 0) proof continuation) (.equal 0 0) = false := by cbv
example : validateAtomic 24 4 checkedEnv (.node (.global 0) []) (.equal 0 0) = true := by cbv
example : Checker.infer 4 empty [] true (.univ 31) = some (.univ 32) := by cbv
example : Checker.infer 4 empty [] true (.univ 32) = none := by cbv

theorem arbitrary_false_eq_observation_rejected (term : Term) :
    validateAtomic typingFuel normalizationFuel empty term (.equal 0 1) = false :=
  false_claim_rejected UnifiedProgram.UnifiedProgramChecked.empty (by change 0 ≠ 1; decide)

theorem arbitrary_false_lt_observation_rejected (term : Term) :
    validateAtomic typingFuel normalizationFuel empty term (.less 0 0) = false :=
  false_claim_rejected UnifiedProgram.UnifiedProgramChecked.empty (by change ¬ (0 : Nat) < 0; decide)

end Jihoo.NativeKernel.Environment.Semantics.Examples
