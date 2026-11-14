import Jihoo.NativePlainIndexForward
import Jihoo.NativeRepresentationViews

namespace Jihoo.NativeKernel.Environment.Representation
open Environment.Conversion

private theorem instantiatePlain (wf : UnifiedProgram.EnvWellFormed env)
    (body : PlainIndices env (⟨domain,erased⟩ :: ctx) term)
    (argument : HasType env ctx true value domain) (plain : PlainIndices env ctx value) :
    PlainIndices env ctx (term.subst (single value)) := by
  apply body.substitution wf (Ghost.Substitution.single erased argument)
  intro index
  cases index with
  | zero => exact plain
  | succ => exact .var

private theorem naturalPlain (n : Nat) : PlainIndices env ctx (.natural n) :=
  .node rfl (by intro child member; cases member)

private theorem reflPlain (n : Nat) : PlainIndices env ctx (.refl (.natural n)) :=
  .node rfl (by intro child member; obtain rfl := List.mem_singleton.mp member; exact naturalPlain n)

private theorem decidePlain (m n : Nat) : PlainIndices env ctx (.decide (.natural m) (.natural n)) := by
  apply PlainIndices.node rfl
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact naturalPlain m
  · exact naturalPlain n

private theorem elementsNotIndex (wf : UnifiedProgram.EnvWellFormed env) (typed : HasType env ctx true (.elements count values) .u64) : False := by
  have converted : Conv env (.array (.natural values.length)) .u64 := typed.principalView
  exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint rfl rfl (by intro equality; cases equality) converted wf.admissible

private theorem packNotIndex (wf : UnifiedProgram.EnvWellFormed env) (typed : HasType env ctx true (.pack predicate value proof) .u64) : False := by
  have converted : Conv env (.refine predicate) .u64 := typed.principalView
  exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint rfl rfl (by intro equality; cases equality) converted wf.admissible

private theorem borrowNotIndex (wf : UnifiedProgram.EnvWellFormed env) (typed : HasType env ctx true (.borrow value) .u64) : False := by
  obtain ⟨type, _, converted⟩ := typed.borrowView
  exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint rfl rfl (by intro equality; cases equality) converted wf.admissible

 theorem compute_plain_transform (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (step : ACU.Computes input output) : PlainTransform env input output := by
  refine ⟨.acu (.compute step),?_⟩
  intro ctx mode type typed plain
  cases step with
  | beta erased domain body argument =>
      cases plain with
      | index indexTyped => exact .index (indexTyped.ghostMixedRed history.wellFormed (.compute (.beta erased domain body argument)))
      | node _ children =>
          have functionPlain := children (.lam erased domain body) (by simp)
          have argumentPlain := children argument (by simp)
          obtain ⟨_,_,_,functionTyped,argumentTyped,_,_⟩ := typed.appView
          obtain ⟨_,_,_,_,functionType⟩ := functionTyped.lamView
          exact instantiatePlain history.wellFormed (functionPlain.lambdaBody history)
            (argumentTyped.ghost.convert (functionType.pi_injective history.wellFormed.admissible).2.1.symm) argumentPlain
  | sub m n proof smaller valid => exact naturalPlain _
  | read count values index proof value selected =>
      cases plain with
      | index indexTyped => exact .index (indexTyped.ghostMixedRed history.wellFormed (.compute (.read count values index proof output selected)))
      | node _ children =>
          have arrayPlain := children (.elements count values) (by simp)
          exact arrayPlain.children (by intro i; rfl) (elementsNotIndex history.wellFormed) output (List.mem_of_getElem? selected)
  | witnessPack predicate value proof =>
      cases plain with
      | index indexTyped => exact .index (indexTyped.ghostMixedRed history.wellFormed (.compute (.witnessPack predicate output proof)))
      | node _ children =>
          have package := children (.pack predicate output proof) (by simp)
          exact package.children (by intro i; rfl) (packNotIndex history.wellFormed) output (by simp)
  | proofPack predicate value proof =>
      cases plain with
      | index indexTyped => exact .index (indexTyped.ghostMixedRed history.wellFormed (.compute (.proofPack predicate value output)))
      | node _ children =>
          have package := children (.pack predicate value output) (by simp)
          exact package.children (by intro i; rfl) (packNotIndex history.wellFormed) output (by simp)
  | derefBorrow value =>
      cases plain with
      | index indexTyped => exact .index (indexTyped.ghostMixedRed history.wellFormed (.compute (.derefBorrow output)))
      | node _ children =>
          have borrow := children (.borrow output) (by simp)
          exact borrow.children (by intro i; rfl) (borrowNotIndex history.wellFormed) output (by simp)
  | borrowDeref value =>
      cases plain with
      | index indexTyped => exact .index (indexTyped.ghostMixedRed history.wellFormed (.compute (.borrowDeref output)))
      | node _ children =>
          have reference := children (.deref output) (by simp)
          cases reference with
          | index indexTyped =>
              obtain ⟨ownerType, owned, innerTyped⟩ := borrow_owned_view typed
              exact False.elim (owned_not_u64 history.wellFormed owned (innerTyped.unique history.wellFormed indexTyped))
          | node _ children => exact children output (by simp)
  | transportRefl family index proof =>
      cases plain with
      | index indexTyped => exact .index (indexTyped.ghostMixedRed history.wellFormed (.compute (.transportRefl family index output)))
      | node _ children => exact children output (by simp)
  | ifLtTrue m n yes no less =>
      cases plain with
      | index indexTyped => exact .index (indexTyped.ghostMixedRed history.wellFormed (.compute (.ifLtTrue m n yes no less)))
      | node head _ => simp [plainNode] at head
      | ifLt left right yesPlain _ =>
          obtain ⟨_,leftTyped,rightTyped,_,_,_⟩ := typed.ifLtView
          exact instantiatePlain history.wellFormed yesPlain
            (HasType.decide leftTyped.naturalView.1 rightTyped.naturalView.1 less) (decidePlain m n)
  | ifLtFalse m n yes no less =>
      cases plain with
      | index indexTyped => exact .index (indexTyped.ghostMixedRed history.wellFormed (.compute (.ifLtFalse m n yes output less)))
      | node head _ => simp [plainNode] at head
      | ifLt _ _ _ noPlain => exact noPlain
  | ifEqTrue n yes no =>
      cases plain with
      | index indexTyped => exact .index (indexTyped.ghostMixedRed history.wellFormed (.compute (.ifEqTrue n yes no)))
      | node head _ => simp [plainNode] at head
      | ifEq _ _ yesPlain _ =>
          obtain ⟨_,leftTyped,_,_,_,_⟩ := typed.ifEqView
          exact instantiatePlain history.wellFormed yesPlain (HasType.refl leftTyped.ghost) (reflPlain n)
  | ifEqFalse m n yes no different =>
      cases plain with
      | index indexTyped => exact .index (indexTyped.ghostMixedRed history.wellFormed (.compute (.ifEqFalse m n yes output different)))
      | node head _ => simp [plainNode] at head
      | ifEq _ _ _ noPlain => exact noPlain

 theorem mixed_plain_transform (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (step : ACU.MixedRed input output) : PlainTransform env input output := by
  induction step using ACU.MixedRed.rec
    (motive_2 := fun xs ys _ => ListRel (PlainTransform env) xs ys) with
  | refl term => exact .refl term
  | trans first second ihfirst ihsecond => exact ihfirst.trans history ihsecond
  | node op children ih => exact .node history ih
  | arithmetic step => exact arithmetic_plain_transform history step
  | compute step => exact compute_plain_transform history step
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

/-- Actual delta contraction is allowed only inside an independently typed
U64 hole; a structural global is never a plain representation node. -/
theorem forward_plain_transform (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (step : EnvironmentDelta.Forward env input output) : PlainTransform env input output := by
  induction step using EnvironmentDelta.Forward.rec
    (motive_2 := fun xs ys _ => ListRel (PlainTransform env) xs ys) with
  | refl => exact .refl _
  | trans first second ihfirst ihsecond => exact ihfirst.trans history ihsecond
  | acu reduced => exact mixed_plain_transform history reduced
  | node op children ih => exact .node history ih
  | delta found =>
      refine ⟨.delta found,?_⟩
      intro ctx mode type typed plain
      cases plain with
      | index indexTyped => exact .index (indexTyped.ghostForward history (.delta found))
      | node head _ => simp [plainNode] at head
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

end Jihoo.NativeKernel.Environment.Representation
