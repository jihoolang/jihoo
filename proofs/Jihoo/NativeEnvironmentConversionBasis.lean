import Jihoo.NativeEnvironmentDeltaConversion
import Jihoo.NativeEnvironmentPrefix

/-! Genuine environment-indexed conversion for the native typing rules.
Its constructors are explicit equations and congruence, never a comparison
oracle. Checked-environment projection proves its forward confluence and
injectivity. Computational soundness itself needs no external certificate. -/
namespace Jihoo.NativeKernel.EnvironmentDelta.Basis

abbrev ListRel := NativeKernel.Conversion.ListRel

def Closed (env : Environment) : Prop :=
  ∀ (index : Nat) (declaration : Environment.GlobalDeclaration), env.globals[index]? = some declaration →
    declaration.value.Scoped 0

inductive Conv (env : Environment) : Term → Term → Prop where
  | legacy : NativeKernel.Conversion.Conv a b → Conv env a b
  | acu : ACU.Conv a b → Conv env a b
  | delta : env.globals[index]? = some declaration → Conv env (.node (.global index) []) declaration.value
  | refl (term : Term) : Conv env term term
  | symm : Conv env a b → Conv env b a
  | trans : Conv env a b → Conv env b c → Conv env a c
  | node (op : Op) : NativeKernel.Conversion.ListRel (Conv env) xs ys → Conv env (.node op xs) (.node op ys)

theorem Conv.extend (converted : Conv before a b) (extension : Environment.Extends before after) :
    Conv after a b := by
  induction converted using Conv.rec (motive_2 := fun xs ys _ => ListRel (Conv after) xs ys) with
  | legacy original => exact .legacy original
  | acu original => exact .acu original
  | delta found => exact .delta (extension.globals _ _ found)
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ first second => exact .trans first second
  | node op children ih => exact .node op ih
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

theorem Conv.renaming (converted : Conv env a b) (ρ : Nat → Nat) (closed : Closed env) :
    Conv env (a.rename ρ) (b.rename ρ) := by
  induction converted using Conv.rec
    (motive_2 := fun xs ys _ => ∀ op offset ρ,
      ListRel (Conv env) (renameArgs op ρ offset xs) (renameArgs op ρ offset ys)) generalizing ρ with
  | legacy original => exact .legacy (original.renaming ρ)
  | acu original => exact .acu (original.renaming ρ)
  | delta found =>
      simpa only [Term.rename, renameArgs, Environment.closed_rename (closed _ _ found)] using Conv.delta found
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih ρ)
  | trans _ _ first second => exact .trans (first ρ) (second ρ)
  | node op children ih => simpa only [Term.rename] using Conv.node op (ih op 0 ρ)
  | nil => intros; simp only [renameArgs]; exact .nil
  | cons first rest ihfirst ihrest =>
      rename_i op offset ρ
      simp only [renameArgs]
      exact .cons (ihfirst _) (ihrest op (offset + 1) ρ)

theorem Conv.substitution (converted : Conv env a b) (σ : Nat → Term) (closed : Closed env) :
    Conv env (a.subst σ) (b.subst σ) := by
  induction converted using Conv.rec
    (motive_2 := fun xs ys _ => ∀ op offset σ,
      ListRel (Conv env) (substArgs op σ offset xs) (substArgs op σ offset ys)) generalizing σ with
  | legacy original => exact .legacy (original.substitution σ)
  | acu original => exact .acu (original.substitution σ)
  | delta found =>
      simpa only [Term.subst, substArgs, Environment.closed_subst (closed _ _ found)] using Conv.delta found
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih σ)
  | trans _ _ first second => exact .trans (first σ) (second σ)
  | node op children ih => simpa only [Term.subst] using Conv.node op (ih op 0 σ)
  | nil => intros; simp only [substArgs]; exact .nil
  | cons first rest ihfirst ihrest =>
      rename_i op offset σ
      simp only [substArgs]
      exact .cons (ihfirst _) (ihrest op (offset + 1) σ)

private theorem lift_related (closed : Closed env) {σ τ : Nat → Term}
    (related : ∀ x, Conv env (σ x) (τ x)) (n : Nat) :
    ∀ x, Conv env (liftSub n σ x) (liftSub n τ x) := by
  induction n with
  | zero => exact related
  | succ n ih =>
      intro x
      cases x with
      | zero => exact .refl _
      | succ x => exact (ih x).renaming Nat.succ closed

theorem Conv.subst_congr (closed : Closed env) {σ τ : Nat → Term}
    (related : ∀ x, Conv env (σ x) (τ x)) (term : Term) :
    Conv env (term.subst σ) (term.subst τ) := by
  induction term using Term.rec
    (motive_2 := fun xs => ∀ op offset σ τ, (∀ x, Conv env (σ x) (τ x)) →
      ListRel (Conv env) (substArgs op σ offset xs) (substArgs op τ offset xs)) generalizing σ τ with
  | var x => simp only [Term.subst]; exact related x
  | node op children ih => simpa only [Term.subst] using Conv.node op (ih op 0 σ τ related)
  | nil => intros; simp only [substArgs]; exact .nil
  | cons first rest ihfirst ihrest =>
      rename_i op offset σ τ related
      simp only [substArgs]
      exact .cons (ihfirst (lift_related closed related _)) (ihrest op (offset + 1) σ τ related)

theorem Conv.toProjected (converted : Conv env a b) (admissible : EnvironmentDelta.Admissible env) :
    EnvironmentDelta.Conv env a b := by
  induction converted using Conv.rec
    (motive_2 := fun xs ys _ => ListRel (EnvironmentDelta.Conv env) xs ys) with
  | legacy original => exact EnvironmentDelta.expand_legacy admissible original
  | acu original => exact EnvironmentDelta.expand_acu admissible original
  | delta found => exact EnvironmentDelta.Conv.delta admissible found
  | refl => exact EnvironmentDelta.Conv.refl _ _
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | node op children ih => exact EnvironmentDelta.Conv.node op ih
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

theorem forward_toConv (forward : EnvironmentDelta.Forward env a b) : Conv env a b := by
  induction forward using EnvironmentDelta.Forward.rec
    (motive_2 := fun xs ys _ => ListRel (Conv env) xs ys) with
  | refl => exact .refl _
  | delta found => exact .delta found
  | acu reduced => exact .acu reduced.toConv
  | trans _ _ first second => exact first.trans second
  | node op children ih => exact .node op ih
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

theorem Conv.ofProjected (converted : EnvironmentDelta.Conv env a b) : Conv env a b := by
  obtain ⟨common, first, second⟩ := converted.church_rosser
  exact (forward_toConv first).trans (forward_toConv second).symm

theorem conv_iff_projected (admissible : EnvironmentDelta.Admissible env) :
    Conv env a b ↔ EnvironmentDelta.Conv env a b :=
  ⟨fun converted => converted.toProjected admissible, Conv.ofProjected⟩

theorem Conv.church_rosser (converted : Conv env a b) (admissible : EnvironmentDelta.Admissible env) :
    ∃ common, EnvironmentDelta.Forward env a common ∧ EnvironmentDelta.Forward env b common :=
  (converted.toProjected admissible).church_rosser

theorem Conv.pi_injective (converted : Conv env (.pi erased domain body) (.pi erased' domain' body'))
    (admissible : EnvironmentDelta.Admissible env) :
    erased = erased' ∧ Conv env domain domain' ∧ Conv env body body' := by
  obtain ⟨same, first, second⟩ := (converted.toProjected admissible).pi_injective
  exact ⟨same, .ofProjected first, .ofProjected second⟩

theorem Conv.sort_injective {s r : SortTag} (converted : Conv env s.term r.term)
    (admissible : EnvironmentDelta.Admissible env) : s = r :=
  (converted.toProjected admissible).sort_injective

end Jihoo.NativeKernel.EnvironmentDelta.Basis
