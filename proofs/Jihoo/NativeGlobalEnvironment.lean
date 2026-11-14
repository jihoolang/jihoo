import Jihoo.NativeDefinitions
import Jihoo.NativeTypeUniqueness

/-! Sequential transparent-global checking on the complete native syntax.
Every declaration is expanded against the previously checked prefix, then its
sort determines its body's code/ghost mode. No external declaration, signature
or caller-supplied mode is trusted. Native opaque code uses of proof globals
can be rejected by this conservative expansion path. Family environments are
not admitted by this module. -/
namespace Jihoo.NativeKernel.GlobalEnvironment

abbrev Declaration := Definitions.Definition
abbrev Environment := Array Declaration

def nodeLimit : Nat := 200000
def depthLimit : Nat := 128

def ordinary : Op → Bool
  | .global _ => false
  | _ => true

/-- Global-free expanded entries contain no residual opaque lookup. -/
def GlobalFree : Term → Prop
  | .var _ => True
  | .node op args => ordinary op = true ∧ ∀ t ∈ args, GlobalFree t

/-- The independent transparent interpretation of a source term. A global
lookup inserts an existing body; it does not invent a new binding or recurse
through an unvalidated external declaration. -/
inductive Expansion (env : Environment) : Term → Term → Prop where
  | var (x : Nat) : Expansion env (.var x) (.var x)
  | global {g : Nat} {d : Declaration} : env[g]? = some d →
      Expansion env (.node (.global g) []) d.value
  | node (op : Op) : ordinary op = true → Conversion.ListRel (Expansion env) xs ys →
      Expansion env (.node op xs) (.node op ys)

/-- Traverse a child list with one shared remaining occurrence budget. -/
def mapBudget (f : Nat → Term → Option (Term × Nat)) : Nat → List Term → Option (List Term × Nat)
  | remaining, [] => some ([], remaining)
  | remaining, t :: ts => do
      let (u, remaining) ← f remaining t
      let (us, remaining) ← mapBudget f remaining ts
      pure (u :: us, remaining)

/-- The full cost of an already expanded body is charged before returning it.
Repeated globals therefore consume repeated logical tree occurrences; guards
precede insertion and do not rely on sharing in the Lean runtime. -/
def expandWork : Nat → Environment → Nat → Term → Option (Term × Nat)
  | 0, _, _, _ => none
  | _ + 1, _, 0, _ => none
  | fuel + 1, env, remaining + 1, term =>
      match term with
      | .var x => some (.var x, remaining)
      | .node op args =>
          if ordinary op then do
            let (args, remaining) ← mapBudget (expandWork fuel env) remaining args
            pure (.node op args, remaining)
          else
            match op, args with
            | .global g, [] => do
                let d ← env[g]?
                let cost := Conversion.treeSize d.value
                if cost ≤ remaining + 1 ∧ Conversion.treeDepth d.value ≤ depthLimit
                then some (d.value, remaining + 1 - cost) else none
            | _, _ => none

def expand (fuel : Nat) (env : Environment) (term : Term) : Option Term := do
  let (result, _) ← expandWork fuel env nodeLimit term
  if Conversion.treeDepth result ≤ depthLimit then some result else none

/-- Prefix entries are in the same oldest-first order as native Global IDs. -/
inductive SequentiallyChecked : List Declaration → Environment → Prop where
  | empty : SequentiallyChecked [] #[]
  | append : SequentiallyChecked raw env →
      Expansion env d.type expanded.type → Expansion env d.value expanded.value →
      Definitions.Valid expanded →
      SequentiallyChecked (raw ++ [d]) (env.push expanded)

def checkDeclaration (fuel : Nat) (env : Environment) (d : Declaration) : Option Declaration := do
  let type ← expand fuel env d.type
  let value ← expand fuel env d.value
  let expanded : Declaration := ⟨type, value⟩
  if Definitions.check fuel expanded then some expanded else none

def checkFrom (fuel : Nat) (env : Environment) : List Declaration → Option Environment
  | [] => some env
  | d :: ds => do
      let expanded ← checkDeclaration fuel env d
      checkFrom fuel (env.push expanded) ds

/-- Check declarations sequentially; the current declaration is never visible
while its annotation or body is being expanded. -/
def checkProgram (fuel : Nat) (ds : List Declaration) : Option Environment := checkFrom fuel #[] ds

def validateProgram (fuel : Nat) (ds : List Declaration) : Bool := (checkProgram fuel ds).isSome

private theorem mapBudget_sound {f : Nat → Term → Option (Term × Nat)}
    (hf : ∀ remaining t u rest, f remaining t = some (u, rest) → Expansion env t u)
    (h : mapBudget f remaining ts = some (us, rest)) : Conversion.ListRel (Expansion env) ts us := by
  induction ts generalizing remaining us rest with
  | nil => simp [mapBudget] at h; cases h.1; exact .nil
  | cons t ts ih =>
      simp only [mapBudget] at h
      cases hu : f remaining t with
      | none => simp [hu] at h
      | some result =>
          rcases result with ⟨u, remaining'⟩
          simp only [hu, Bind.bind, Option.bind] at h
          cases hus : mapBudget f remaining' ts with
          | none => simp [hus] at h
          | some result =>
              rcases result with ⟨us', rest'⟩
              simp only [hus] at h
              rcases h with ⟨rfl, rfl⟩
              exact .cons (hf remaining t u remaining' hu) (ih hus)

 theorem expandWork_sound (h : expandWork fuel env remaining t = some (u, rest)) : Expansion env t u := by
  induction fuel generalizing remaining t u rest with
  | zero => simp [expandWork] at h
  | succ fuel ih =>
      cases remaining with
      | zero => simp [expandWork] at h
      | succ remaining =>
          cases t with
          | var x =>
              simp only [expandWork, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              exact .var x
          | node op args =>
              simp only [expandWork] at h
              split at h
              · rename_i ordinary
                cases hs : mapBudget (expandWork fuel env) remaining args with
                | none => simp [hs] at h
                | some result =>
                    rcases result with ⟨us, left⟩
                    simp only [hs, Bind.bind, Option.bind] at h
                    rcases h with ⟨rfl,rfl⟩
                    exact .node op ordinary (mapBudget_sound (fun _ _ _ _ h => ih h) hs)
              · split at h
                · rename_i g hNotOrdinary
                  cases hd : env[g]? with
                  | none => simp [hd] at h
                  | some d =>
                      simp only [hd, Bind.bind, Option.bind] at h
                      split at h
                      · cases h; exact .global hd
                      · contradiction
                · contradiction

 theorem expand_sound (h : expand fuel env t = some u) : Expansion env t u := by
  unfold expand at h
  cases hw : expandWork fuel env nodeLimit t with
  | none => simp [hw] at h
  | some result =>
      rcases result with ⟨value, left⟩
      simp only [hw, Bind.bind, Option.bind] at h
      split at h
      · cases h; exact expandWork_sound hw
      · contradiction

 theorem checkDeclaration_sound (h : checkDeclaration fuel env d = some expanded) :
    Expansion env d.type expanded.type ∧ Expansion env d.value expanded.value ∧ Definitions.Valid expanded := by
  unfold checkDeclaration at h
  cases ht : expand fuel env d.type with
  | none => simp [ht] at h
  | some type =>
      simp only [ht, Bind.bind, Option.bind] at h
      cases hv : expand fuel env d.value with
      | none => simp [hv] at h
      | some value =>
          simp only [hv] at h
          split at h
          · rename_i checked
            cases h
            exact ⟨expand_sound ht, expand_sound hv, Definitions.check_sound checked⟩
          · contradiction

 theorem checkFrom_sound (history : SequentiallyChecked raw env)
    (h : checkFrom fuel env ds = some result) : SequentiallyChecked (raw ++ ds) result := by
  induction ds generalizing raw env with
  | nil => simp only [checkFrom, Option.some.injEq] at h; subst result; simpa using history
  | cons d ds ih =>
      simp only [checkFrom] at h
      cases he : checkDeclaration fuel env d with
      | none => simp [he] at h
      | some expanded =>
          simp only [he, Bind.bind, Option.bind] at h
          obtain ⟨ht,hv,valid⟩ := checkDeclaration_sound he
          have next := SequentiallyChecked.append history ht hv valid
          simpa only [List.append_assoc, List.singleton_append] using ih next h

 theorem checkProgram_sound (h : checkProgram fuel ds = some env) : SequentiallyChecked ds env := by
  simpa only [List.nil_append] using checkFrom_sound SequentiallyChecked.empty h

 theorem validateProgram_sound (h : validateProgram fuel ds = true) : ∃ env, SequentiallyChecked ds env := by
  unfold validateProgram at h
  cases hc : checkProgram fuel ds with
  | none => simp [hc] at h
  | some env => exact ⟨env, checkProgram_sound hc⟩

/-- Raw references must point strictly into the already checked prefix. -/
def Before (bound : Nat) : Term → Prop
  | .var _ => True
  | .node (.global g) args => args = [] ∧ g < bound
  | .node _ args => ∀ t ∈ args, Before bound t

 theorem Expansion.before (h : Expansion env t u) : Before env.size t := by
  induction h using Expansion.rec
    (motive_2 := fun xs ys _ => ∀ t ∈ xs, Before env.size t) with
  | var => simp [Before]
  | global found =>
      obtain ⟨inside,_⟩ := Array.getElem?_eq_some_iff.mp found
      simp only [Before]
      exact ⟨True.intro,inside⟩
  | node op hOrd hs ih =>
      cases op <;> simp only [ordinary] at hOrd
      all_goals first | contradiction | (simpa only [Before] using ih)
  | nil => rename_i t ht; cases ht
  | cons h hs ih ihts =>
      rename_i t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ih
      · exact ihts t ht

 theorem Expansion.globalFree (h : Expansion env t u)
    (henv : ∀ d ∈ env.toList, GlobalFree d.value) : GlobalFree u := by
  induction h using Expansion.rec
    (motive_2 := fun xs ys _ => ∀ t ∈ ys, GlobalFree t) with
  | var => simp [GlobalFree]
  | global found => exact henv _ (List.mem_of_getElem? (by simpa using found))
  | node op hOrd hs ih => simp only [GlobalFree]; exact ⟨hOrd,ih⟩
  | nil => rename_i t ht; cases ht
  | cons h hs ih ihts =>
      rename_i t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ih
      · exact ihts t ht

 theorem SequentiallyChecked.length (checked : SequentiallyChecked raw env) : env.size = raw.length := by
  induction checked with
  | empty => rfl
  | append history ht hv valid ih => simp [ih]

 theorem SequentiallyChecked.valid (checked : SequentiallyChecked raw env) :
    ∀ d ∈ env.toList, Definitions.Valid d := by
  induction checked with
  | empty => simp
  | append history ht hv valid ih =>
      intro d hd
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl
      · exact ih d hd
      · exact valid

 theorem SequentiallyChecked.globalFree (checked : SequentiallyChecked raw env) :
    ∀ d ∈ env.toList, GlobalFree d.type ∧ GlobalFree d.value := by
  induction checked with
  | empty => simp
  | append history ht hv valid ih =>
      intro d hd
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl
      · exact ih d hd
      · exact ⟨ht.globalFree (fun d hd => (ih d hd).2), hv.globalFree (fun d hd => (ih d hd).2)⟩

 theorem SequentiallyChecked.closed (checked : SequentiallyChecked raw env) :
    ∀ d ∈ env.toList, d.type.Scoped 0 ∧ d.value.Scoped 0 ∧ d.type.WellFormed ∧ d.value.WellFormed := by
  intro d hd
  obtain ⟨sort,formed,typed⟩ := checked.valid d hd
  exact ⟨formed.term_scoped,typed.term_scoped,formed.term_wellFormed,typed.term_wellFormed⟩

 theorem SequentiallyChecked.ordered (checked : SequentiallyChecked raw env)
    (found : raw[i]? = some d) : Before i d.type ∧ Before i d.value := by
  induction checked generalizing i d with
  | empty => simp at found
  | @append raw env declaration expanded history ht hv valid ih =>
      by_cases earlier : i < raw.length
      · rw [List.getElem?_append_left earlier] at found
        exact ih found
      · have later : raw.length ≤ i := by omega
        rw [List.getElem?_append_right later] at found
        cases diff : i - raw.length with
        | zero =>
            simp only [diff,List.getElem?_cons_zero,Option.some.injEq] at found
            subst d
            have same : i = raw.length := by omega
            subst i
            simpa only [history.length] using And.intro ht.before hv.before
        | succ j => simp [diff] at found

 theorem checkProgram_entries (h : checkProgram fuel raw = some env) :
    env.size = raw.length ∧
    (∀ d ∈ env.toList, Definitions.Valid d ∧ GlobalFree d.type ∧ GlobalFree d.value ∧
      d.type.Scoped 0 ∧ d.value.Scoped 0 ∧ d.type.WellFormed ∧ d.value.WellFormed) := by
  have checked := checkProgram_sound h
  refine ⟨checked.length,?_⟩
  intro d hd
  have free := checked.globalFree d hd
  have closed := checked.closed d hd
  exact ⟨checked.valid d hd,free.1,free.2,closed⟩

 theorem checkProgram_no_forward (h : checkProgram fuel raw = some env) (found : raw[i]? = some d) :
    Before i d.type ∧ Before i d.value := (checkProgram_sound h).ordered found

 theorem checkProgram_result_unique (h : checkProgram fuel raw = some env)
    (h' : checkProgram fuel raw = some env') : env = env' := Option.some.inj (h.symm.trans h')

private theorem mapBudget_budget {f : Nat → Term → Option (Term × Nat)}
    (hf : ∀ remaining t u rest, f remaining t = some (u,rest) → Conversion.treeSize u + rest ≤ remaining)
    (h : mapBudget f remaining ts = some (us,rest)) :
    (us.map Conversion.treeSize).sum + rest ≤ remaining := by
  induction ts generalizing remaining us rest with
  | nil =>
      simp only [mapBudget,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      simp
  | cons t ts ih =>
      simp only [mapBudget] at h
      cases hu : f remaining t with
      | none => simp [hu] at h
      | some result =>
          rcases result with ⟨u,remaining'⟩
          simp only [hu,Bind.bind,Option.bind] at h
          cases hus : mapBudget f remaining' ts with
          | none => simp [hus] at h
          | some result =>
              rcases result with ⟨us',rest'⟩
              simp only [hus] at h
              rcases h with ⟨rfl,rfl⟩
              have head := hf remaining t u remaining' hu
              have tail := ih hus
              simp only [List.map_cons,List.sum_cons]
              omega

/-- Accepted expansion accounts for every resulting tree occurrence before
insertion, including each repeated copy of a previously checked global body. -/
theorem expandWork_budget (h : expandWork fuel env remaining t = some (u,rest)) :
    Conversion.treeSize u + rest ≤ remaining := by
  induction fuel generalizing remaining t u rest with
  | zero => simp [expandWork] at h
  | succ fuel ih =>
      cases remaining with
      | zero => simp [expandWork] at h
      | succ remaining =>
          cases t with
          | var x =>
              simp only [expandWork,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              simp [Conversion.treeSize,Nat.add_comm]
          | node op args =>
              simp only [expandWork] at h
              split at h
              · cases hs : mapBudget (expandWork fuel env) remaining args with
                | none => simp [hs] at h
                | some result =>
                    rcases result with ⟨us,left⟩
                    simp only [hs,Bind.bind,Option.bind] at h
                    rcases h with ⟨rfl,rfl⟩
                    have budget := mapBudget_budget (fun _ _ _ _ h => ih h) hs
                    simp only [Conversion.treeSize]
                    omega
              · split at h
                · rename_i g hNotOrdinary
                  cases hd : env[g]? with
                  | none => simp [hd] at h
                  | some d =>
                      simp only [hd,Bind.bind,Option.bind] at h
                      split at h
                      · rename_i safe
                        cases h
                        omega
                      · contradiction
                · contradiction

theorem expand_nodes (h : expand fuel env t = some u) : Conversion.treeSize u ≤ nodeLimit := by
  unfold expand at h
  cases hw : expandWork fuel env nodeLimit t with
  | none => simp [hw] at h
  | some result =>
      rcases result with ⟨value,left⟩
      simp only [hw,Bind.bind,Option.bind] at h
      split at h
      · cases h
        have budget := expandWork_budget hw
        omega
      · contradiction

theorem expand_depth (h : expand fuel env t = some u) : Conversion.treeDepth u ≤ depthLimit := by
  unfold expand at h
  cases hw : expandWork fuel env nodeLimit t with
  | none => simp [hw] at h
  | some result =>
      rcases result with ⟨value,left⟩
      simp only [hw,Bind.bind,Option.bind] at h
      split at h
      · rename_i depth
        cases h
        exact depth
      · contradiction

/-- Appending a checked declaration cannot change an earlier lookup or its
transparent interpretation. Current/self references were excluded at admission. -/
theorem Expansion.extend (h : Expansion env t u) (next : Declaration) :
    Expansion (env.push next) t u := by
  induction h using Expansion.rec
    (motive_2 := fun xs ys _ => Conversion.ListRel (Expansion (env.push next)) xs ys) with
  | var x => exact .var x
  | global found =>
      obtain ⟨inside,value⟩ := Array.getElem?_eq_some_iff.mp found
      exact .global (by rw [Array.getElem?_push_lt inside, value])
  | node op hOrd hs ih => exact .node op hOrd ih
  | nil => exact .nil
  | cons h hs ih ihts => exact .cons ih ihts

/-- The final environment retains the exact expansion of every source
annotation/body at its original declaration index. -/
theorem SequentiallyChecked.correspondence {i : Nat} {d expanded : Declaration} (checked : SequentiallyChecked raw env)
    (source : raw[i]? = some d) (target : env[i]? = some expanded) :
    Expansion env d.type expanded.type ∧ Expansion env d.value expanded.value ∧ Definitions.Valid expanded := by
  induction checked generalizing i d expanded with
  | empty => simp at source
  | @append raw env entry declaration history ht hv valid ih =>
      by_cases earlier : i < raw.length
      · rw [List.getElem?_append_left earlier] at source
        have inside : i < env.size := by simpa only [history.length] using earlier
        have old : env[i]? = some expanded := by
          rw [Array.getElem?_eq_getElem inside]
          simpa only [Array.getElem?_push_lt inside] using target
        obtain ⟨type,value,valid⟩ := ih source old
        exact ⟨type.extend entry,value.extend entry,valid⟩
      · have later : raw.length ≤ i := by omega
        rw [List.getElem?_append_right later] at source
        cases diff : i - raw.length with
        | zero =>
            simp only [diff,List.getElem?_cons_zero,Option.some.injEq] at source
            subst d
            have same : i = raw.length := by omega
            subst i
            rw [← history.length,Array.getElem?_push_size] at target
            cases target
            exact ⟨ht.extend entry,hv.extend entry,valid⟩
        | succ j => simp [diff] at source

theorem checkProgram_correspondence {i : Nat} {d expanded : Declaration} (h : checkProgram fuel raw = some env)
    (source : raw[i]? = some d) (target : env[i]? = some expanded) :
    Expansion env d.type expanded.type ∧ Expansion env d.value expanded.value ∧ Definitions.Valid expanded :=
  (checkProgram_sound h).correspondence source target

/-- Global lookup never treats an unvalidated annotation as an axiom: every
visible value has its stored type, with its declaration's actual body mode. -/
theorem checked_global_typed {g : Nat} {d : Declaration} (checked : SequentiallyChecked raw env)
    (found : env[g]? = some d) :
    ∃ sort : SortTag, HasType [] true d.type sort.term ∧
      HasType [] (Definitions.bodyMode sort) d.value d.type :=
  checked.valid d (List.mem_of_getElem? (by simpa using found))

/-- Any inferred/derived type of a visible expanded body belongs to its checked
declared type's genuine native conversion class, across mode changes as well. -/
theorem checked_global_type_unique {g : Nat} {d : Declaration} (checked : SequentiallyChecked raw env)
    (found : env[g]? = some d) (typed : HasType [] mode d.value T) : Conversion.Conv d.type T := by
  obtain ⟨sort,formed,body⟩ := checked_global_typed checked found
  exact body.unique typed

end Jihoo.NativeKernel.GlobalEnvironment
