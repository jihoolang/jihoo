import Jihoo.NativeKindPrefixInterpretation

/-! Representation classification of runtime binders under authentic code
closure. Known heads use checked metadata; abstract heads use the actual kind
interpretation. No variable is declared nonowning merely by its syntax. -/
namespace Jihoo.NativeKernel.Environment.ContextModes
open CodeKinds
open Jihoo.Quantity
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

def UnownedHead (env : Environment) (op : Op) : Prop :=
  EnvironmentDelta.Basis.rigid op = true ∧ op ≠ .buffer ∧
    ∀ family count, op = .ind family count →
      ∃ entry, env.families[family]? = some entry ∧ entry.boxed = false

theorem head_unrestricted (accepted : head env term = some .unrestricted) :
    ∃ op children, term = .node op children ∧ UnownedHead env op := by
  cases term with
  | var index => simp [head,NativeQuantity.binderMode] at accepted
  | node op children =>
      refine ⟨op,children,rfl,?_⟩
      cases op <;> simp_all [head,NativeQuantity.binderMode,UnownedHead,
        EnvironmentDelta.Basis.rigid,GlobalEnvironment.ordinary,ACU.fullRigid,
        NativeKernel.Conversion.rigid,ACU.arithmeticRigid]
      case buffer =>
        cases children with
        | nil => contradiction
        | cons first rest => cases rest <;> simp at accepted

theorem UnownedHead.extend (extension : Extends before after) (head : UnownedHead before op) :
    UnownedHead after op := by
  refine ⟨head.1,head.2.1,?_⟩
  intro family count same
  obtain ⟨entry,found,flat⟩ := head.2.2 family count same
  exact ⟨entry,extension.families _ _ found,flat⟩

theorem UnownedHead.not_owned (head : UnownedHead env op)
    (admissible : EnvironmentDelta.Admissible env) : ¬ Owned env (.node op children) := by
  intro owned
  cases owned with
  | buffer converted =>
      exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint head.1 rfl head.2.1 converted admissible
  | family found boxed converted =>
      have same := (converted.full_rigid_node_injective head.1 rfl admissible).1
      obtain ⟨flatEntry,selected,flat⟩ := head.2.2 _ _ same
      have equal := Option.some.inj (selected.symm.trans found)
      subst flatEntry
      simp_all

/-- Classification is stable when actual earlier metadata and actual kind
arguments are interpreted in a later checked world. -/
theorem Resolved.unrestricted_not_owned_in_extension
    (extension : Extends before after)
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations after)
    (resolved : Resolved before ctx false domain .unrestricted)
    (closing : Interpretation after ctx values) : ¬ Owned after (domain.subst values) := by
  cases resolved with
  | head normalized known =>
      obtain ⟨op,children,rfl,unowned⟩ := head_unrestricted known
      have converted := (Conversion.normalize?_sound normalized).extend extension
      have shifted := converted.substitution values history.wellFormed.closed
      intro owned
      exact (unowned.extend extension).not_owned history.wellFormed.admissible
        (by simpa only [Term.subst] using owned.congr shifted)
  | abstract normalized spine =>
      exact abstractDomain_not_owned_in_extension extension history
        (Conversion.normalize?_sound normalized) spine closing

theorem Resolved.unrestricted_not_owned
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (resolved : Resolved env ctx false domain .unrestricted)
    (closing : Interpretation env ctx values) : ¬ Owned env (domain.subst values) :=
  resolved.unrestricted_not_owned_in_extension (Extends.refl _) history closing

end Jihoo.NativeKernel.Environment.ContextModes
