import Jihoo.NativeEnvironmentDeltaConversion
import Jihoo.NativeACUBoundedNormalizer

/-! Concrete bounded delta/ACU normalization. Expansion precharges repeated
stored bodies against one shared output allowance before ACU normalization.
Unknown globals, malformed nodes and exhausted budgets propagate failure. -/
namespace Jihoo.NativeKernel.EnvironmentDelta

theorem expansion_eq_expand (expanded : GlobalEnvironment.Expansion env.globals term result) :
    expand env term = result := by
  induction expanded using GlobalEnvironment.Expansion.rec
    (motive_2 := fun xs ys _ => expandArgs env xs = ys) with
  | var => simp only [expand]
  | global found => exact expand_global found
  | node op ordinary children ih => rw [expand_ordinary ordinary, ih]
  | nil => simp only [expandArgs]
  | cons first rest ihfirst ihrest => simp only [expandArgs, ihfirst, ihrest]

namespace Bounded

def normalize (env : Environment) (fuel limit : Nat) (term : Term) : Option Term := do
  if fuel ≤ 128 ∧ 0 < limit ∧ limit ≤ 200000 then
    let (expanded, _) ← GlobalEnvironment.expandWork fuel env.globals limit term
    ACU.Bounded.run fuel limit expanded
  else none

def equal (env : Environment) (fuel limit : Nat) (first second : Term) : Bool :=
  match normalize env fuel limit first, normalize env fuel limit second with
  | some a, some b => a.equal b
  | _, _ => false

private theorem normalize_parts (accepted : normalize env fuel limit term = some result) :
    ∃ expanded remaining,
      GlobalEnvironment.expandWork fuel env.globals limit term = some (expanded, remaining) ∧
      ACU.Bounded.run fuel limit expanded = some result := by
  unfold normalize at accepted
  split at accepted
  · cases expandedAt : GlobalEnvironment.expandWork fuel env.globals limit term with
    | none => simp only [expandedAt, Bind.bind, Option.bind] at accepted; contradiction
    | some pair =>
        obtain ⟨expanded, remaining⟩ := pair
        simp only [expandedAt, Bind.bind, Option.bind] at accepted
        exact ⟨expanded, remaining, rfl, accepted⟩
  · contradiction

theorem normalize_forward (accepted : normalize env fuel limit term = some result) : Forward env term result := by
  obtain ⟨expanded, remaining, expandedAt, normalized⟩ := normalize_parts accepted
  have same := expansion_eq_expand (env := env) (GlobalEnvironment.expandWork_sound expandedAt)
  exact .trans (by simpa only [same] using expand_forward env term) (.acu (ACU.Bounded.run_forward normalized))

theorem normalize_sound (accepted : normalize env fuel limit term = some result) (admissible : Admissible env) :
    Conv env term result := (normalize_forward accepted).toConv admissible

theorem normalize_within (accepted : normalize env fuel limit term = some result) :
    Conversion.treeSize result ≤ limit ∧ Conversion.treeDepth result ≤ 128 := by
  obtain ⟨expanded, remaining, expandedAt, normalized⟩ := normalize_parts accepted
  exact ACU.Bounded.run_within normalized

theorem equal_common_reduct (accepted : equal env fuel limit first second = true) :
    ∃ common, Forward env first common ∧ Forward env second common := by
  unfold equal at accepted
  split at accepted
  · rename_i a b firstRun secondRun
    have same := (Term.equal_iff _ _).mp accepted
    subst b
    exact ⟨a, normalize_forward firstRun, normalize_forward secondRun⟩
  · contradiction

theorem equal_sound (accepted : equal env fuel limit first second = true) (admissible : Admissible env) :
    Conv env first second := by
  obtain ⟨common, firstPath, secondPath⟩ := equal_common_reduct accepted
  exact (firstPath.toConv admissible).trans (secondPath.toConv admissible).symm

end Bounded
end Jihoo.NativeKernel.EnvironmentDelta
