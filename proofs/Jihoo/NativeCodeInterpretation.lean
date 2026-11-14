import Jihoo.NativeKindRealization
import Jihoo.NativeKindSpine
import Jihoo.NativeContextModes

/-! Admissible code-closing interpretations retain actual source context
formation, lookup-by-lookup ghost typing, and the same executable code argument
gates for first-order kinds. No arbitrary code-substitution theorem is assumed.
The resource contract of function values is a separate obligation. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

structure Interpretation (env : Environment) (ctx : Context) (values : Nat → Term) : Prop where
  formed : ContextFormed env ctx
  typed : Ghost.Substitution env ctx [] values
  arguments : ∀ index kind, LookupKind env ctx index kind → Admitted env kind (values index)

/-- Actual checker traces establish the representation part of an admissible
interpretation. Callers supply terms and successful checks, never plain flags. -/
theorem Interpretation.ofChecked
    (formed : contextOK fuel env ctx = true)
    (typed : Ghost.Substitution env ctx [] values)
    (arguments : ∀ index kind, LookupKind env ctx index kind →
      Checker.check fuel env [] false (values index) kind.term = true ∧
        Checker.applicationOK fuel env false kind.term (values index) = true) :
    Interpretation env ctx values :=
  ⟨contextOK_sound formed,typed,fun index kind found =>
    ⟨fuel,(arguments index kind found).1,(arguments index kind found).2⟩⟩

/-- Kind soundness for every authenticated abstract type/family spine. The
U64 indices may be arbitrary typed code trees, including memory expressions;
only the actual ghost substitution theorem is used to close them. -/
theorem Spine.realizes (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (spine : Spine env ctx term kind) (closing : Interpretation env ctx values) :
    Realizes env kind (term.subst values) := by
  induction spine with
  | @var index kind found =>
      simpa only [Term.subst] using (closing.arguments index kind found).realizes history
  | @app function erased result fuel argument head checked ih =>
      have indexTyped := (Checker.check_sound checked).ghostSubstitution history.wellFormed closing.typed
      have closedIndex : HasType env [] true (argument.subst values) .u64 := by
        simpa only [Term.subst, substArgs] using indexTyped
      simpa only [Term.subst, substArgs, Op.binders, liftSub] using ih.index closedIndex

theorem Spine.closed_not_owned (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (spine : Spine env ctx term kind) (closing : Interpretation env ctx values) :
    ¬ Owned env (term.subst values) := (spine.realizes history closing).not_owned history

theorem Spine.closed_nonFunction (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (spine : Spine env ctx term kind) (closing : Interpretation env ctx values) :
    PiSeparated env (term.subst values) := (spine.realizes history closing).nonFunction history

theorem Spine.closed_not_ref (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (spine : Spine env ctx term kind) (closing : Interpretation env ctx values) :
    ¬ Conversion.Conv env (term.subst values) (.ref owner) := (spine.realizes history closing).not_ref history

theorem Spine.closed_not_back (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (spine : Spine env ctx term kind) (closing : Interpretation env ctx values) :
    ¬ Conversion.Conv env (term.subst values) (.back erased owner motive) := (spine.realizes history closing).not_back history

/-- This is the abstract arm retained by ContextModes.resolve. The statement
uses the original source domain and its certified normalization. -/
theorem abstractDomain_not_owned (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (normalized : Conversion.Conv env domain normal)
    (spine : Spine env ctx normal (.type level)) (closing : Interpretation env ctx values) :
    ¬ Owned env (domain.subst values) := by
  intro owned
  exact spine.closed_not_owned history closing (owned.congr (normalized.substitution values history.wellFormed.closed))

end Jihoo.NativeKernel.Environment.CodeKinds
