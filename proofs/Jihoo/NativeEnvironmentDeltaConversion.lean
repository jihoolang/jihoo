import Jihoo.NativeEnvironmentDelta
import Jihoo.NativeACUForwardConfluence

/-! Environment-indexed delta/ACU conversion with finite forward witnesses.
This relation unfolds only interpreted checked entries. Its integration into
the executable typing judgment is a subsequent step, not an assumed theorem.
-/
namespace Jihoo.NativeKernel.EnvironmentDelta

open Conversion (ListRel)

private theorem expand_single (env : Environment) (argument : Term) :
    (fun x => expand env (single argument x)) = single (expand env argument) := by
  funext x
  cases x <;> simp only [single, expand]

private theorem expanded_node (op : Op)
    (children : ListRel ACU.Conv (expandArgs env xs) (expandArgs env ys)) :
    ACU.Conv (expand env (.node op xs)) (expand env (.node op ys)) := by
  cases xs <;> cases ys
  all_goals simp only [expandArgs] at children
  all_goals first
    | exact .refl _
    | solve | cases children
    | simpa only [expand_node_cons] using ACU.Conv.node op children

theorem expand_legacy (admissible : Admissible env) (converted : Conversion.Conv a b) :
    ACU.Conv (expand env a) (expand env b) := by
  induction converted using Conversion.Conv.rec
    (motive_2 := fun xs ys _ => ListRel ACU.Conv (expandArgs env xs) (expandArgs env ys)) with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | node op _ children => exact expanded_node op children
  | beta erased domain body argument =>
      simpa only [expand, expandArgs, expand_substitution admissible, expand_single] using
        ACU.Conv.legacy (Conversion.Conv.beta erased (expand env domain) (expand env body) (expand env argument))
  | add a b bound =>
      simpa only [expand, expandArgs] using ACU.Conv.legacy (Conversion.Conv.add a b bound)
  | sub a b proof lower upper =>
      simpa only [expand, expandArgs] using ACU.Conv.legacy (Conversion.Conv.sub a b (expand env proof) lower upper)
  | read count xs index proof value selected =>
      simpa only [expand, expandArgs, expandArgs_map, List.map_cons, List.map_nil] using
        ACU.Conv.legacy (Conversion.Conv.read count (xs.map (expand env)) index (expand env proof) (expand env value)
          (by simp only [List.getElem?_map, selected, Option.map_some]))
  | witnessPack predicate value proof =>
      simpa only [expand, expandArgs] using
        ACU.Conv.legacy (Conversion.Conv.witnessPack (expand env predicate) (expand env value) (expand env proof))
  | proofPack predicate value proof =>
      simpa only [expand, expandArgs] using
        ACU.Conv.legacy (Conversion.Conv.proofPack (expand env predicate) (expand env value) (expand env proof))
  | derefBorrow value =>
      simpa only [expand, expandArgs] using ACU.Conv.legacy (Conversion.Conv.derefBorrow (expand env value))
  | borrowDeref value =>
      simpa only [expand, expandArgs] using ACU.Conv.legacy (Conversion.Conv.borrowDeref (expand env value))
  | transportRefl motive value proof =>
      simpa only [expand, expandArgs] using
        ACU.Conv.legacy (Conversion.Conv.transportRefl (expand env motive) (expand env value) (expand env proof))
  | ifLtTrue a b yes no holds =>
      simpa only [expand, expandArgs, expand_substitution admissible, expand_single] using
        ACU.Conv.legacy (Conversion.Conv.ifLtTrue a b (expand env yes) (expand env no) holds)
  | ifLtFalse a b yes no holds =>
      simpa only [expand, expandArgs] using
        ACU.Conv.legacy (Conversion.Conv.ifLtFalse a b (expand env yes) (expand env no) holds)
  | ifEqTrue value yes no =>
      simpa only [expand, expandArgs, expand_substitution admissible, expand_single] using
        ACU.Conv.legacy (Conversion.Conv.ifEqTrue value (expand env yes) (expand env no))
  | ifEqFalse a b yes no unequal =>
      simpa only [expand, expandArgs] using
        ACU.Conv.legacy (Conversion.Conv.ifEqFalse a b (expand env yes) (expand env no) unequal)
  | nil => simp only [expandArgs]; exact .nil
  | cons _ _ first rest => simp only [expandArgs]; exact .cons first rest

theorem expand_acu (admissible : Admissible env) (converted : ACU.Conv a b) :
    ACU.Conv (expand env a) (expand env b) := by
  induction converted using ACU.Conv.rec
    (motive_2 := fun xs ys _ => ListRel ACU.Conv (expandArgs env xs) (expandArgs env ys)) with
  | legacy old => exact expand_legacy admissible old
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | node op _ children => exact expanded_node op children
  | assoc a b c =>
      simpa only [expand, expandArgs] using ACU.Conv.assoc (expand env a) (expand env b) (expand env c)
  | comm a b => simpa only [expand, expandArgs] using ACU.Conv.comm (expand env a) (expand env b)
  | zero a => simpa only [expand, expandArgs] using ACU.Conv.zero (expand env a)
  | nil => simp only [expandArgs]; exact .nil
  | cons _ _ first rest => simp only [expandArgs]; exact .cons first rest

def Conv (env : Environment) (a b : Term) : Prop := ACU.Conv (expand env a) (expand env b)

theorem Conv.refl (env : Environment) (term : Term) : Conv env term term := ACU.Conv.refl _
theorem Conv.symm (converted : Conv env a b) : Conv env b a := ACU.Conv.symm converted
theorem Conv.trans (first : Conv env a b) (second : Conv env b c) : Conv env a c := ACU.Conv.trans first second
theorem Conv.ofACU (admissible : Admissible env) (converted : ACU.Conv a b) : Conv env a b :=
  expand_acu admissible converted

theorem Conv.node (op : Op) (children : ListRel (Conv env) xs ys) : Conv env (.node op xs) (.node op ys) := by
  apply expanded_node op
  induction children with
  | nil => simp only [expandArgs]; exact .nil
  | cons first rest ih => simp only [expandArgs]; exact .cons first ih

theorem Conv.renaming (admissible : Admissible env) (converted : Conv env a b) (ρ : Nat → Nat) :
    Conv env (a.rename ρ) (b.rename ρ) := by
  change ACU.Conv _ _
  rw [expand_renaming admissible, expand_renaming admissible]
  exact ACU.Conv.renaming converted ρ

theorem Conv.substitution (admissible : Admissible env) (converted : Conv env a b) (σ : Nat → Term) :
    Conv env (a.subst σ) (b.subst σ) := by
  change ACU.Conv _ _
  rw [expand_substitution admissible, expand_substitution admissible]
  exact ACU.Conv.substitution converted (fun x => expand env (σ x))

theorem Conv.delta (admissible : Admissible env) (found : env.globals[index]? = some declaration) :
    Conv env (.node (.global index) []) declaration.value := by
  change ACU.Conv _ _
  rw [expand_global found, expand_globalFree (admissible.transparent _ _ found)]
  exact .refl _

theorem Conv.pi_injective (converted : Conv env (.pi erased domain body) (.pi erased' domain' body')) :
    erased = erased' ∧ Conv env domain domain' ∧ Conv env body body' := by
  have actual : ACU.Conv (.pi erased (expand env domain) (expand env body))
      (.pi erased' (expand env domain') (expand env body')) := by
    simpa only [Conv, expand, expandArgs] using converted
  exact actual.full_pi_injective

private theorem expand_sort (env : Environment) (sort : SortTag) : expand env sort.term = sort.term := by
  cases sort <;> simp only [SortTag.term, expand, expandArgs]

theorem Conv.sort_injective {first second : SortTag} (converted : Conv env first.term second.term) : first = second := by
  have actual : ACU.Conv first.term second.term := by simpa only [Conv, expand_sort] using converted
  exact actual.full_sort_injective

/-- A finite forward derivation uses only lookup delta, actual finite ACU
reduction, contextual traversal and composition. No reverse beta is a step. -/
inductive Forward (env : Environment) : Term → Term → Prop where
  | refl : Forward env term term
  | delta : env.globals[index]? = some declaration → Forward env (.node (.global index) []) declaration.value
  | acu : ACU.MixedRed a b → Forward env a b
  | trans : Forward env a b → Forward env b c → Forward env a c
  | node (op : Op) : ListRel (Forward env) xs ys → Forward env (.node op xs) (.node op ys)

theorem expand_forward (env : Environment) (term : Term) : Forward env term (expand env term) := by
  induction term using Term.rec
    (motive_2 := fun terms => ListRel (Forward env) terms (expandArgs env terms)) with
  | var => simp only [expand]; exact .refl
  | node op terms ih =>
      cases terms with
      | nil =>
          cases op <;> simp only [expand, expandArgs]
          all_goals first | exact .refl | skip
          rename_i index
          cases found : env.globals[index]? with
          | none => exact .refl
          | some declaration => exact .delta found
      | cons first rest => simpa only [expand_node_cons, expandArgs] using Forward.node op ih
  | nil => simp only [expandArgs]; exact .nil
  | cons term terms first rest => simp only [expandArgs]; exact .cons first rest

theorem Conv.church_rosser (converted : Conv env a b) : ∃ common, Forward env a common ∧ Forward env b common := by
  obtain ⟨common, first, second⟩ := ACU.Conv.church_rosser converted
  exact ⟨common, .trans (expand_forward env a) (.acu first), .trans (expand_forward env b) (.acu second)⟩

theorem Forward.toConv (forward : Forward env a b) (admissible : Admissible env) : Conv env a b := by
  induction forward using Forward.rec
    (motive_2 := fun xs ys _ => ListRel (Conv env) xs ys) with
  | refl => exact Conv.refl _ _
  | delta found => exact Conv.delta admissible found
  | acu reduced => exact Conv.ofACU admissible reduced.toConv
  | trans first second ihfirst ihsecond => exact ihfirst.trans ihsecond
  | node op children ih => exact Conv.node op ih
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

theorem conv_iff_forward_join (admissible : Admissible env) :
    Conv env a b ↔ ∃ common, Forward env a common ∧ Forward env b common := by
  constructor
  · exact Conv.church_rosser
  · rintro ⟨common, first, second⟩
    exact (first.toConv admissible).trans (second.toConv admissible).symm

theorem Forward.confluence (first : Forward env a b) (second : Forward env a c)
    (admissible : Admissible env) : ∃ common, Forward env b common ∧ Forward env c common :=
  ((first.toConv admissible).symm.trans (second.toConv admissible)).church_rosser

end Jihoo.NativeKernel.EnvironmentDelta
