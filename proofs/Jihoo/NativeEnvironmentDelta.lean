import Jihoo.NativeClosedTerm
import Jihoo.NativeGlobalEnvironment

/-! Checked-environment delta expansion on the actual native syntax.
Stored entries are interpreted declarations, rather than unchecked external
definitions. This layer does not silently add family iota or proof irrelevance.
-/
namespace Jihoo.NativeKernel.EnvironmentDelta

structure Admissible (env : Environment) : Prop where
  closed : ∀ (index : Nat) (declaration : Environment.GlobalDeclaration), env.globals[index]? = some declaration → declaration.value.Scoped 0
  transparent : ∀ (index : Nat) (declaration : Environment.GlobalDeclaration), env.globals[index]? = some declaration →
    GlobalEnvironment.GlobalFree declaration.value

mutual
  /-- One pass suffices for already expanded stored bodies. Unresolved globals
  and malformed nonempty Global nodes remain visible, never guessed. -/
  def expand (env : Environment) : Term → Term
    | .var x => .var x
    | .node (.global index) [] =>
        match env.globals[index]? with
        | some declaration => declaration.value
        | none => .node (.global index) []
    | .node op arguments => .node op (expandArgs env arguments)
  termination_by term => sizeOf term

  def expandArgs (env : Environment) : List Term → List Term
    | [] => []
    | term :: terms => expand env term :: expandArgs env terms
  termination_by terms => sizeOf terms
end

theorem expandArgs_map (env : Environment) (terms : List Term) :
    expandArgs env terms = terms.map (expand env) := by
  induction terms with
  | nil => simp only [expandArgs, List.map_nil]
  | cons term terms ih => simp only [expandArgs, List.map_cons, ih]

theorem expand_ordinary (ordinary : GlobalEnvironment.ordinary op = true) :
    expand env (.node op arguments) = .node op (expandArgs env arguments) := by
  cases op <;> simp_all only [GlobalEnvironment.ordinary, Bool.false_eq_true, expand]

theorem expand_node_cons (env : Environment) (op : Op) (first : Term) (rest : List Term) :
    expand env (.node op (first :: rest)) = .node op (expand env first :: expandArgs env rest) := by
  cases op <;> simp only [expand, expandArgs]

theorem expand_global (found : env.globals[index]? = some declaration) :
    expand env (.node (.global index) []) = declaration.value := by simp only [expand, found]

theorem expand_globalFree (free : GlobalEnvironment.GlobalFree term) : expand env term = term := by
  induction term using Term.rec
    (motive_2 := fun terms => (∀ term ∈ terms, GlobalEnvironment.GlobalFree term) → expandArgs env terms = terms) with
  | var => simp only [expand]
  | node op terms ih =>
      rw [GlobalEnvironment.GlobalFree] at free
      obtain ⟨ordinary, children⟩ := free
      rw [expand_ordinary ordinary, ih children]
  | nil => intros; simp only [expandArgs]
  | cons term terms iht ihterms =>
      rename_i free
      simp only [expandArgs, iht (free _ (by simp)), ihterms (fun term member => free term (by simp [member]))]

theorem expand_idempotent (admissible : Admissible env) (term : Term) :
    expand env (expand env term) = expand env term := by
  induction term using Term.rec
    (motive_2 := fun terms => expandArgs env (expandArgs env terms) = expandArgs env terms) with
  | var => simp only [expand]
  | node op terms ih =>
      cases terms with
      | nil =>
          cases op <;> simp only [expand, expandArgs]
          rename_i index
          cases found : env.globals[index]? with
          | none => simp only [found, expand]
          | some declaration => simpa only [found] using expand_globalFree (admissible.transparent _ _ found)
      | cons first rest =>
          simpa only [expand_node_cons, expandArgs] using congrArg (Term.node op) ih
  | nil => simp only [expandArgs]
  | cons term terms iht ihterms => simp only [expandArgs, iht, ihterms]

theorem expand_renaming (admissible : Admissible env) (term : Term) (ρ : Nat → Nat) :
    expand env (term.rename ρ) = (expand env term).rename ρ := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ op offset ρ,
      expandArgs env (renameArgs op ρ offset terms) = renameArgs op ρ offset (expandArgs env terms)) generalizing ρ with
  | var => simp only [expand, Term.rename]
  | node op terms ih =>
      cases terms with
      | nil =>
          cases op <;> simp only [Term.rename, renameArgs, expand, expandArgs]
          rename_i index
          cases found : env.globals[index]? with
          | none => simp only [Term.rename, renameArgs]
          | some declaration =>
              simpa only [found] using (Environment.closed_rename (admissible.closed _ _ found) ρ).symm
      | cons first rest =>
          simpa only [Term.rename, renameArgs, expand_node_cons, expandArgs] using
            congrArg (Term.node op) (ih op 0 ρ)
  | nil => intros; simp only [expandArgs, renameArgs]
  | cons term terms iht ihterms =>
      rename_i op offset ρ
      simp only [renameArgs, expandArgs, iht, ihterms]

theorem expand_liftSub (admissible : Admissible env) (binders : Nat) (σ : Nat → Term) (index : Nat) :
    expand env (liftSub binders σ index) = liftSub binders (fun x => expand env (σ x)) index := by
  induction binders generalizing index with
  | zero => rfl
  | succ binders ih =>
      cases index with
      | zero => simp only [liftSub, liftSubOne, expand]
      | succ index => simp only [liftSub, liftSubOne, expand_renaming admissible, ih]

theorem expand_substitution (admissible : Admissible env) (term : Term) (σ : Nat → Term) :
    expand env (term.subst σ) = (expand env term).subst (fun x => expand env (σ x)) := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ op offset σ,
      expandArgs env (substArgs op σ offset terms) =
        substArgs op (fun x => expand env (σ x)) offset (expandArgs env terms)) generalizing σ with
  | var => simp only [expand, Term.subst]
  | node op terms ih =>
      cases terms with
      | nil =>
          cases op <;> simp only [Term.subst, substArgs, expand, expandArgs]
          rename_i index
          cases found : env.globals[index]? with
          | none => simp only [Term.subst, substArgs]
          | some declaration =>
              simpa only [found] using (Environment.closed_subst (admissible.closed _ _ found)
                (fun x => expand env (σ x))).symm
      | cons first rest =>
          simpa only [Term.subst, substArgs, expand_node_cons, expandArgs] using
            congrArg (Term.node op) (ih op 0 σ)
  | nil => intros; simp only [expandArgs, substArgs]
  | cons term terms iht ihterms =>
      rename_i op offset σ
      simp only [substArgs, expandArgs, iht]
      rw [ihterms]
      congr 2
      exact funext (expand_liftSub admissible _ σ)

end Jihoo.NativeKernel.EnvironmentDelta
