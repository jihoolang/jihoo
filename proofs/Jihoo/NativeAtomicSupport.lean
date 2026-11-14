import Jihoo.NativeSemanticResourceWitnesses

/-! A constructive first-stage semantic certificate indexed by an actual
unified HasType derivation. Its constructors replay actual native rules;
none accepts the truth of its conclusion as an oracle. Arithmetic observations
are real full-conversion certificates. Global support descends through a
validated earlier program prefix. Full universe/family/iteration realization
is deliberately not asserted by this initial atomic stage. -/
namespace Jihoo.NativeKernel.Environment.Semantics
open Jihoo.NativeKernel.Environment.Conversion

structure GlobalOrigin {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}
    {env : Environment} {index : Nat} {declaration : GlobalDeclaration}
    (_history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (_found : env.globals[index]? = some declaration) where
  prefixDefinitions : List GlobalDeclaration
  prefixFamilies : List FamilyDeclaration
  earlier : Environment
  source : GlobalDeclaration
  history : UnifiedProgram.UnifiedProgramChecked prefixDefinitions prefixFamilies earlier
  size : earlier.globals.size = index
  checked : UnifiedProgram.DeclarationChecked earlier source declaration
  extension : Environment.Extends earlier env

theorem global_origin (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (found : env.globals[index]? = some declaration) : Nonempty (GlobalOrigin history found) := by
  obtain ⟨ds,fs,earlier,source,prior,size,checked,extension⟩ := history.global_prefix found
  exact ⟨⟨ds,fs,earlier,source,prior,size,checked,extension⟩⟩

/-- This finite semantic trace annotates existing typing derivations. It is not
an alternative public typing judgment and is not claimed to cover all HasType. -/
inductive AtomicSupported : {env : Environment} → {ctx : Context} → {mode : Bool} →
    {term type : Term} → HasType env ctx mode term type → Prop where
  | refl (value : HasType env ctx true a .u64) : AtomicSupported (HasType.refl (ghost := mode) value)
  | decide (left : a < 2^64) (right : b < 2^64) (ordered : a < b) :
      AtomicSupported (HasType.decide (env := env) (ctx := ctx) (ghost := mode) left right ordered)
  | decideConverted (left : HasType env ctx true a .u64) (right : HasType env ctx true b .u64)
      (leftConv : Conv env a (.natural m)) (rightConv : Conv env b (.natural n))
      (leftBound : m < 2^64) (rightBound : n < 2^64) (ordered : m < n) :
      AtomicSupported (HasType.decideConverted (ghost := mode) left right leftConv rightConv leftBound rightBound ordered)
  | zeroLe (typed : HasType env ctx true a .u64) (observed : NumeralObservation env a)
      (bound : observed.value + 1 < 2^64) : AtomicSupported (HasType.zeroLe (ghost := mode) typed)
  | ltAdd (left : HasType env ctx true a .u64) (right : HasType env ctx true b .u64)
      (step : HasType env ctx true c .u64) (proof : HasType env ctx true p (.lt a b))
      (supported : AtomicSupported proof)
      (first : NumeralObservation env a) (second : NumeralObservation env b) (third : NumeralObservation env c)
      (leftBound : first.value + third.value < 2^64) (rightBound : second.value + third.value < 2^64) :
      AtomicSupported (HasType.ltAdd (ghost := mode) left right step proof)
  | ltCancel (left : HasType env ctx true a .u64) (right : HasType env ctx true b .u64)
      (step : HasType env ctx true c .u64) (proof : HasType env ctx true p (.lt (.uadd a c) (.uadd b c)))
      (supported : AtomicSupported proof)
      (first : NumeralObservation env a) (second : NumeralObservation env b) (third : NumeralObservation env c)
      (leftBound : first.value + third.value < 2^64) (rightBound : second.value + third.value < 2^64) :
      AtomicSupported (HasType.ltCancel (ghost := mode) left right step proof)
  | ltLe (left : HasType env ctx true a .u64) (middle : HasType env ctx true b .u64)
      (right : HasType env ctx true c .u64) (lower : HasType env ctx true p (.lt a b))
      (upper : HasType env ctx true q (.lt b (.uadd c (.natural 1))))
      (lowerSupported : AtomicSupported lower) (upperSupported : AtomicSupported upper)
      (first : NumeralObservation env a) (second : NumeralObservation env b) (third : NumeralObservation env c)
      (bound : third.value + 1 < 2^64) : AtomicSupported (HasType.ltLe (ghost := mode) left middle right lower upper)
  | transport (predicate : HasType env ctx true f (.pi false .u64 .prop))
      (equality : HasType env ctx true e (.eq a b)) (evidence : HasType env ctx true p (.app f a))
      (equalSupported : AtomicSupported equality) (evidenceSupported : AtomicSupported evidence) :
      AtomicSupported (HasType.transport (ghost := mode) predicate equality evidence)
  | strict (first : HasType env ctx mode a A) (second : HasType env ctx mode b B)
      (supported : AtomicSupported second) : AtomicSupported (HasType.strict first second)
  | free (owner : HasType env ctx mode buffer (.buffer n)) (rest : HasType env ctx mode term T)
      (supported : AtomicSupported rest) : AtomicSupported (HasType.free owner rest)
  | drop (found : env.families[family]? = some entry) (boxed : entry.boxed = true)
      (owner : HasType env ctx mode value (.node (.ind family count) indices))
      (rest : HasType env ctx mode term T) (supported : AtomicSupported rest) :
      AtomicSupported (HasType.drop found boxed owner rest)
  | ifLt (left : HasType env ctx mode a .u64) (right : HasType env ctx mode b .u64)
      (yes : HasType env (⟨.lt a b,true⟩ :: ctx) mode yesTerm (T.rename Nat.succ))
      (no : HasType env ctx mode noTerm T) (supported : AtomicSupported no) :
      AtomicSupported (HasType.ifLt left right yes no)
  | ifEq (left : HasType env ctx mode a .u64) (right : HasType env ctx mode b .u64)
      (yes : HasType env (⟨.eq a b,true⟩ :: ctx) mode yesTerm (T.rename Nat.succ))
      (no : HasType env ctx mode noTerm T) (supported : AtomicSupported no) :
      AtomicSupported (HasType.ifEq left right yes no)
  | absurd {sort : SortTag} (target : HasType env ctx true T sort.term)
      (proof : HasType env ctx true p (.lt index (.natural 0))) (supported : AtomicSupported proof)
      (allowed : absurdAllowed env mode T) : AtomicSupported (HasType.absurd target proof allowed)
  | convert (typed : HasType env ctx mode term A) (converted : Conv env A B)
      (supported : AtomicSupported typed) : AtomicSupported (HasType.convert typed converted)
  | reduction (wellFormed : UnifiedProgram.EnvWellFormed env) (typed : HasType env ctx mode term T)
      (step : ACU.MixedRed term output) (supported : AtomicSupported (typed.ghostMixedRed wellFormed step)) :
      AtomicSupported typed
  | forward (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
      (typed : HasType env ctx mode term T) (step : EnvironmentDelta.Forward env term output)
      (supported : AtomicSupported (typed.ghostForward history step)) : AtomicSupported typed
  | global (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
      (found : env.globals[index]? = some declaration) (origin : GlobalOrigin history found)
      (valueTyped : HasType origin.earlier [] bodyMode declaration.value declaration.type)
      (supported : AtomicSupported valueTyped) :
      AtomicSupported (HasType.global (ctx := ctx) (ghost := mode) found)
  | load (closed : Conversion.Closed env) (owner : HasType env ctx mode buffer (.buffer count)) (index : HasType env ctx mode i .u64)
      (proof : HasType env ctx true p (.lt i count))
      (continuation : HasType env ctx mode function (.pi false valueDomain (.pi false ownerDomain result)))
      (valueConv : Conv env valueDomain .i64) (ownerConv : Conv env ownerDomain (.buffer (count.rename Nat.succ)))
      (resultConv : Conv env result normal) (lowered : PartialRenaming.shift (-2) 0 normal = some outside)
      (allowed : continuationAllowed env mode outside)
      (supported : AtomicSupported (load_logical_witness closed owner continuation valueConv ownerConv resultConv lowered)) :
      AtomicSupported (HasType.load owner index proof continuation valueConv ownerConv resultConv lowered allowed)

theorem AtomicSupported.realize {typed : HasType env ctx mode term type} (supported : AtomicSupported typed) : ∀ (_wf : UnifiedProgram.EnvWellFormed env), AtomicTruth env type := by
  induction supported with
  | refl => intro wf; exact .equality (.refl _)
  | decide left right ordered => intro wf; exact .less (.refl _) (.refl _) ordered
  | decideConverted left right leftConv rightConv leftBound rightBound ordered =>
    intro wf
    exact .less leftConv rightConv ordered
  | zeroLe typed observed bound => intro wf; exact .zeroLe observed bound
  | ltAdd left right step proof supported first second third leftBound rightBound ih =>
    intro wf
    exact AtomicTruth.ltAdd wf (ih wf) first second third leftBound rightBound
  | ltCancel left right step proof supported first second third leftBound rightBound ih =>
    intro wf
    exact AtomicTruth.ltCancel wf (ih wf) first second third leftBound rightBound
  | ltLe left middle right lower upper lowerSupported upperSupported first second third bound lo hi =>
    intro wf
    exact AtomicTruth.ltLe wf (lo wf) (hi wf) first second third bound
  | transport predicate equality evidence equalSupported evidenceSupported he hp => intro wf; exact AtomicTruth.transport wf (hp wf) (he wf)
  | strict first second supported ih => intro wf; exact ih wf
  | free owner rest supported ih => intro wf; exact ih wf
  | drop found boxed owner rest supported ih => intro wf; exact ih wf
  | ifLt left right yes no supported ih => intro wf; exact ih wf
  | ifEq left right yes no supported ih => intro wf; exact ih wf
  | absurd target proof supported allowed ih => intro wf; exact False.elim (AtomicTruth.less_zero_false wf (ih wf) (.refl _))
  | convert typed converted supported ih => intro wf; exact .convert (ih wf) converted
  | reduction wellFormed typed step supported ih => intro wf; exact ih wf
  | forward history typed step supported ih => intro wf; exact ih wf
  | global history found origin valueTyped supported ih =>
    intro wf
    simpa only [closed_rename origin.checked.closed.1] using (ih origin.history.wellFormed).extend origin.extension
  | load closed owner index proof continuation valueConv ownerConv resultConv lowered allowed supported ih => intro wf; exact ih wf

theorem no_supported_false_equality (wf : UnifiedProgram.EnvWellFormed env) (different : m ≠ n)
    (typed : HasType env [] mode term (.eq (.natural m) (.natural n))) : ¬ AtomicSupported typed :=
  fun supported => AtomicTruth.no_false_equality wf different (supported.realize wf)

theorem no_supported_false_less (wf : UnifiedProgram.EnvWellFormed env) (unordered : ¬ m < n)
    (typed : HasType env [] mode term (.lt (.natural m) (.natural n))) : ¬ AtomicSupported typed :=
  fun supported => AtomicTruth.no_false_less wf unordered (supported.realize wf)

end Jihoo.NativeKernel.Environment.Semantics
