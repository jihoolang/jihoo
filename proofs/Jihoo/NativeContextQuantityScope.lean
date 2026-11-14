import Jihoo.NativeContextQuantity
import Jihoo.NativeControlScope

namespace Jihoo.NativeKernel.Environment.ContextQuantity
open Jihoo.Quantity NativeQuantity CallReplay
variable {control : Control} {controls : List Control} {child : Term}
variable {terms arguments : List Term}

private theorem bind_some {value : Option α} {next : α → Option β}
    (h : (value.bind next) = some result) : ∃ first, value = some first ∧ next first = some result :=
  Option.bind_eq_some_iff.mp h

private theorem source_child (scope : (Term.node op arguments).Scoped depth)
    (found : arguments[index]? = some child) : child.Scoped (depth + op.binders index) := by
  cases scope with | node children => exact children _ _ found

private theorem source_children (scope : (Term.node op arguments).Scoped depth)
    (binders : ∀ index, op.binders index = 0) : ∀ child ∈ arguments, child.Scoped depth := by
  intro child member
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  simpa only [binders, Nat.add_zero] using source_child scope found

 theorem openHead_scope (opened : openHead fuel env ctx head supplied = some result)
    (scope : head.Scoped ctx.length) :
    result.body.Scoped result.context.length ∧ result.context.length = ctx.length + result.modes.length := by
  induction fuel generalizing ctx head supplied result with
  | zero => simp [openHead] at opened
  | succ fuel ih =>
      simp only [openHead] at opened
      split at opened
      · rename_i erased domain body argument rest
        split at opened
        · contradiction
        · obtain ⟨mode, resolved, opened⟩ := bind_some opened
          obtain ⟨inside, found, same⟩ := bind_some opened
          cases same
          have bodyScope := source_child scope (by rfl : [domain,body][1]? = some body)
          have next := ih found (by simpa only [Op.binders,List.length_cons] using bodyScope)
          exact ⟨next.1,by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next.2⟩
      · cases opened; exact ⟨scope,by simp⟩

 theorem replay_arguments_scoped (trace : CallReplay.Steps env ctx ghost signature arguments entries result) :
    ∀ argument ∈ arguments, argument.Scoped ctx.length := by
  induction trace with
  | nil => intro argument member; cases member
  | cons _ checked _ _ _ ih =>
      intro argument member
      rcases List.mem_cons.mp member with rfl | member
      · exact (Checker.check_sound checked).term_scoped
      · exact ih _ member

 theorem runtimeArguments_members (member : argument ∈ runtimeArguments entries) :
    argument ∈ entries.map Argument.value := by
  unfold runtimeArguments at member
  obtain ⟨entry, found, selected⟩ := List.mem_filterMap.mp member
  split at selected
  · contradiction
  · cases selected
    exact List.mem_map.mpr ⟨entry,found,rfl⟩

private theorem mapM_scope {visit : Term → Option Control}
    (preserves : ∀ term control, visit term = some control → term.Scoped depth → ControlScoped depth control)
    (source : ∀ term ∈ terms, term.Scoped depth) (h : terms.mapM visit = some controls) :
    ∀ control ∈ controls, ControlScoped depth control := by
  induction terms generalizing controls with
  | nil => simp only [List.mapM_nil] at h; cases h; intro control member; cases member
  | cons term rest ih =>
      simp only [List.mapM_cons] at h
      obtain ⟨head, first, h⟩ := bind_some h
      obtain ⟨tail, second, same⟩ := bind_some h
      cases same
      intro control member
      rcases List.mem_cons.mp member with rfl | member
      · exact preserves _ _ first (source _ (by simp))
      · exact ih (fun _ member => source _ (List.mem_cons_of_mem _ member)) second _ member

private theorem fetch_scope {visit : Term → Option Control}
    (preserves : ∀ term control, visit term = some control → term.Scoped depth → ControlScoped depth control)
    (source : ∀ term ∈ terms, term.Scoped depth) (h : fetch visit terms index = some control) :
    ControlScoped depth control := by
  obtain ⟨term, found, projected⟩ := bind_some h
  exact preserves _ _ projected (source _ (List.mem_of_getElem? found))

private theorem fields_scope {visit : Term → Option Control}
    (preserves : ∀ term control, visit term = some control → term.Scoped depth → ControlScoped depth control)
    (source : ∀ term ∈ terms, term.Scoped depth) (h : fields visit terms indices = some control) :
    ControlScoped depth control := by
  induction indices generalizing control with
  | nil => simp only [fields, Option.some.injEq] at h; cases h; trivial
  | cons index rest ih =>
      simp only [fields] at h
      obtain ⟨first, head, h⟩ := bind_some h
      obtain ⟨second, tail, same⟩ := bind_some h
      cases same
      exact ⟨fetch_scope preserves source head,ih tail⟩

private theorem relevant_subset {fieldList : List Field} (h : EnvironmentQuantity.relevantFields data fieldList arguments = some relevant) :
    ∀ argument ∈ relevant, argument ∈ arguments := by
  induction fieldList generalizing arguments relevant with
  | nil => cases arguments <;> simp_all [EnvironmentQuantity.relevantFields]
  | cons field rest ih =>
      cases arguments with
      | nil => simp [EnvironmentQuantity.relevantFields] at h
      | cons argument arguments =>
          simp only [EnvironmentQuantity.relevantFields] at h
          obtain ⟨tail, found, same⟩ := bind_some h
          cases same
          split
          · intro value member
            rcases List.mem_cons.mp member with rfl | member
            · simp
            · exact List.mem_cons_of_mem _ (ih found _ member)
          · intro value member; exact List.mem_cons_of_mem _ (ih found _ member)

end Jihoo.NativeKernel.Environment.ContextQuantity
