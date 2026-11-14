import Jihoo.NativeQuantity

/-! Concrete projection commutes with full-native variable substitution,
including evidence and explicit lambda binders. The complete Option-valued
checker result is preserved for a queried owner with a unique preimage; merging
aliases still permits projected-trace accounting but requires rechecking demand.
This does not substitute effectful expressions or prove runtime heap safety. -/
namespace Jihoo.NativeKernel.NativeQuantity

open Jihoo.Quantity

theorem binderMode_rename (erased : Bool) (t : Term) (ρ : Nat → Nat) :
    binderMode erased (t.rename ρ) = binderMode erased t := by
  cases erased <;> simp only [binderMode, Bool.false_eq_true, ↓reduceIte]
  case false =>
    cases t with
    | var => simp [Term.rename]
    | node op args =>
      cases op <;> cases args with
      | nil => simp [Term.rename, renameArgs]
      | cons a rest =>
        cases rest with
        | nil => simp [Term.rename, renameArgs]
        | cons b tail => cases tail <;> simp [Term.rename, renameArgs]

theorem reclose_rename (c : Control) (ρ : Nat → Nat) :
    reclose (c.rename ρ) = (reclose c).rename ρ := by
  cases c <;> rfl

theorem openScopes_rename (n : Nat) (c : Control) (ρ : Nat → Nat) :
    openScopes n (c.rename ρ) = (openScopes n c).map (Control.rename ρ) := by
  induction n generalizing c ρ with
  | zero => simp only [openScopes, reclose_rename, Option.map_some]
  | succ n ih =>
      cases c <;> simp only [Control.rename, openScopes, Option.map_none]
      case scope mode body =>
        rw [ih]
        cases openScopes n body <;> rfl

theorem openFunctions_rename (n : Nat) (c : Control) (ρ : Nat → Nat) :
    openFunctions n (c.rename ρ) = (openFunctions n c).map (Control.rename ρ) := by
  cases n with
  | zero => rfl
  | succ n =>
      cases c <;> simp only [Control.rename, openFunctions, Option.map_none]
      case closure body => exact openScopes_rename _ _ _

theorem lambdaHead_rename (t : Term) (ρ : Nat → Nat) :
    lambdaHead (t.rename ρ) = lambdaHead t := by
  cases t with
  | var => simp [Term.rename, lambdaHead]
  | node op args =>
      cases op <;> cases args with
      | nil => simp [Term.rename, renameArgs, lambdaHead]
      | cons a args =>
          cases args with
          | nil => simp [Term.rename, renameArgs, lambdaHead]
          | cons b args => cases args <;> simp [Term.rename, renameArgs, lambdaHead]

theorem functionTail_rename (t : Term) (c : Control) (ρ : Nat → Nat) :
    functionTail (t.rename ρ) (c.rename ρ) = (functionTail t c).rename ρ := by
  simp only [functionTail, lambdaHead_rename]
  split
  · cases c <;> rfl
  · rfl

theorem caseBody_rename (n : Nat) (c : Control) (ρ : Nat → Nat) :
    caseBody n (c.rename ρ) = (caseBody n c).rename ρ := by
  unfold caseBody
  rw [openFunctions_rename]
  cases openFunctions n c <;> rfl

theorem renameArgs_length (op : Op) (ρ : Nat → Nat) (offset : Nat) (xs : List Term) :
    (renameArgs op ρ offset xs).length = xs.length := by
  induction xs generalizing offset <;> simp [renameArgs, *]

theorem renameArgs_get (op : Op) (ρ : Nat → Nat) (offset i : Nat) (xs : List Term) :
    (renameArgs op ρ offset xs)[i]? =
      (xs[i]?).map (Term.rename (liftRenaming (op.binders (offset + i)) ρ)) := by
  induction xs generalizing offset i with
  | nil => simp [renameArgs]
  | cons t ts ih =>
    cases i with
    | zero => simp [renameArgs]
    | succ i =>
      simpa [renameArgs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (ih (offset + 1) i)

theorem liftRenaming_one (ρ : Nat → Nat) : liftRenaming 1 ρ = Jihoo.Quantity.lift ρ := by
  funext x; cases x <;> rfl

private theorem fetch_rename {f : Term → Option Control}
    (h : ∀ t ρ, f (t.rename ρ) = (f t).map (Control.rename ρ)) :
    fetch f (renameArgs op ρ 0 xs) i =
      (fetch f xs i).map (Control.rename (liftRenaming (op.binders i) ρ)) := by
  unfold fetch
  rw [renameArgs_get]
  simp only [Nat.zero_add]
  cases xs[i]? <;> simp [h]

private theorem fields_rename {f : Term → Option Control}
    (h : ∀ t ρ, f (t.rename ρ) = (f t).map (Control.rename ρ))
    (hz : ∀ i ∈ indices, op.binders i = 0) :
    fields f (renameArgs op ρ 0 xs) indices =
      (fields f xs indices).map (Control.rename ρ) := by
  induction indices with
  | nil => rfl
  | cons i is ih =>
      simp only [fields, fetch_rename h, hz i (by simp), liftRenaming]
      rw [ih (fun j hj => hz j (by simp [hj]))]
      cases fetch f xs i <;> cases fields f xs is <;> rfl

theorem liftRenaming_add (a b : Nat) (ρ : Nat → Nat) :
    liftRenaming a (liftRenaming b ρ) = liftRenaming (a + b) ρ := by
  induction a with
  | zero => simp [liftRenaming]
  | succ a ih => simp only [liftRenaming, Nat.succ_add, ih]

theorem scoped_get_rename (locals : List Bool) (ρ : Nat → Nat) (x : Nat) :
    locals[liftRenaming locals.length ρ x]? = locals[x]? := by
  induction locals generalizing x with
  | nil => simp
  | cons b bs ih =>
      cases x <;> simp [liftRenaming, Indexed.liftRenaming, ih]

theorem domainNonFunction_rename (t : Term) (ρ : Nat → Nat) :
    domainNonFunction (t.rename ρ) = domainNonFunction t := by
  cases t with
  | var => simp [Term.rename, domainNonFunction]
  | node op args => cases op <;> simp [Term.rename, domainNonFunction]

theorem callResult_rename (locals : List Bool) (t : Term) (ρ : Nat → Nat) :
    callResult locals (t.rename (liftRenaming locals.length ρ)) = callResult locals t := by
  cases t with
  | var => simp only [Term.rename, callResult, scoped_get_rename]
  | node op args => cases op <;> simp [Term.rename, callResult]

theorem splitSpine_rename (fuel : Nat) (head : Term) (args : List Term) (ρ : Nat → Nat) :
    splitSpine fuel (head.rename ρ) (args.map (Term.rename ρ)) =
      (splitSpine fuel head args).map
        (fun (head, args) => (head.rename ρ, args.map (Term.rename ρ))) := by
  induction fuel generalizing head args ρ with
  | zero => rfl
  | succ fuel ih =>
      cases head with
      | var x => simp [Term.rename, splitSpine]
      | node op children =>
          cases op <;> cases children with
          | nil => simp [Term.rename, renameArgs, splitSpine]
          | cons f tail =>
            cases tail with
            | nil => simp [Term.rename, renameArgs, splitSpine]
            | cons a rest =>
              cases rest <;> simp [Term.rename, renameArgs, Op.binders, liftRenaming, splitSpine]
              all_goals simpa only [List.map_cons] using ih f (a :: args) ρ

def CallPlan.renameAt (depth : Nat) (ρ : Nat → Nat) (p : CallPlan) : CallPlan :=
  ⟨p.modes, p.runtimeArgs.map (Term.rename ρ), p.body.rename (liftRenaming (p.modes.length + depth) ρ)⟩

theorem peelCallAux_rename (fuel : Nat) (locals : List Bool) (linearSeen : Bool) (head : Term)
    (args : List Term) (ρ : Nat → Nat) :
    peelCallAux fuel locals linearSeen (head.rename (liftRenaming locals.length ρ))
        (args.map (Term.rename ρ)) =
      (peelCallAux fuel locals linearSeen head args).map (CallPlan.renameAt locals.length ρ) := by
  induction fuel generalizing locals linearSeen head args ρ with
  | zero => rfl
  | succ fuel ih =>
    cases args with
    | nil =>
        simp only [List.map_nil, peelCallAux, callResult_rename]
        split <;> simp [CallPlan.renameAt]
    | cons a args =>
      cases head with
      | var x => simp [Term.rename, peelCallAux]
      | node op children =>
        cases op <;> cases children with
        | nil => simp [Term.rename, renameArgs, peelCallAux]
        | cons domain tail =>
          cases tail with
          | nil => simp [Term.rename, renameArgs, peelCallAux]
          | cons body rest =>
            cases rest <;> simp only [Term.rename, renameArgs, List.map_cons, Op.binders,
              liftRenaming, peelCallAux]
            all_goals first
            | rfl
            | (
              rename_i erased
              rw [binderMode_rename, domainNonFunction_rename]
              cases hd : binderMode erased domain with
              | none => rfl
              | some mode =>
                dsimp only [bind, pure, Option.bind]
                have hr := ih (domainNonFunction domain :: locals) (linearSeen || mode == .linear) body args ρ
                simp only [List.length_cons, liftRenaming] at hr
                rw [hr]
                cases peelCallAux fuel (domainNonFunction domain :: locals) (linearSeen || mode == .linear) body args <;>
                  cases erased <;> simp [CallPlan.renameAt, Nat.add_comm, Nat.add_left_comm])

theorem peelCall_rename (fuel : Nat) (locals : List Bool) (head : Term)
    (args : List Term) (ρ : Nat → Nat) :
    peelCall fuel locals (head.rename (liftRenaming locals.length ρ))
        (args.map (Term.rename ρ)) =
      (peelCall fuel locals head args).map (CallPlan.renameAt locals.length ρ) := by
  exact peelCallAux_rename fuel locals false head args ρ

theorem sequence_rename (cs : List Control) (ρ : Nat → Nat) :
    sequence (cs.map (Control.rename ρ)) = (sequence cs).rename ρ := by
  induction cs <;> simp [sequence, Control.rename, *]

theorem scopes_rename (modes : List BinderMode) (c : Control) (ρ : Nat → Nat) :
    (Control.scopes modes c).rename ρ = Control.scopes modes (c.rename (liftRenaming modes.length ρ)) := by
  induction modes generalizing ρ with
  | nil => rfl
  | cons mode modes ih =>
      change Control.scope mode ((Control.scopes modes c).rename (Jihoo.Quantity.lift ρ)) =
        Control.scope mode (Control.scopes modes (c.rename (liftRenaming (modes.length + 1) ρ)))
      rw [show Jihoo.Quantity.lift ρ = liftRenaming 1 ρ from rfl, ih, liftRenaming_add]

theorem finishCall_rename {f : Term → Option Control}
    (h : ∀ t ρ, f (t.rename ρ) = (f t).map (Control.rename ρ)) (p : CallPlan) (ρ : Nat → Nat) :
    finishCall f (p.renameAt 0 ρ) = (finishCall f p).map (Control.rename ρ) := by
  have hm : ∀ (ts : List Term), (ts.map (Term.rename ρ)).mapM f =
      (ts.mapM f).map (List.map (Control.rename ρ)) := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      simp only [List.map_cons, List.mapM_cons, h, ih]
      cases f t <;> cases ts.mapM f <;> rfl
  simp only [finishCall, CallPlan.renameAt, Nat.add_zero, hm, h]
  cases p.runtimeArgs.mapM f <;> cases f p.body <;>
    simp [sequence_rename, scopes_rename, Control.rename]

theorem projectCall_rename {f : Term → Option Control}
    (h : ∀ t ρ, f (t.rename ρ) = (f t).map (Control.rename ρ)) (fuel : Nat)
    (t : Term) (ρ : Nat → Nat) :
    projectCall fuel f (t.rename ρ) = (projectCall fuel f t).map (Control.rename ρ) := by
  unfold projectCall
  have hs := splitSpine_rename fuel t [] ρ
  simp only [List.map_nil] at hs
  rw [hs]
  cases splitSpine fuel t [] with
  | none => rfl
  | some pair =>
      obtain ⟨head, args⟩ := pair
      dsimp only [bind, pure, Option.bind, Option.map]
      rw [show head.rename ρ = head.rename (liftRenaming ([] : List Bool).length ρ) from rfl,
        peelCall_rename]
      cases hp : peelCall fuel [] head args with
      | none => rfl
      | some p => exact finishCall_rename h p ρ

theorem project_rename (fuel : Nat) (t : Term) (ρ : Nat → Nat) :
    project fuel (t.rename ρ) = (project fuel t).map (Control.rename ρ) := by
  induction fuel generalizing t ρ with
  | zero => rfl
  | succ fuel ih =>
    cases t with
    | var x => simp [Term.rename, project, Control.rename]
    | node op args =>
      simp only [Term.rename, project, renameArgs_length]
      by_cases harity : args.length != op.arity
      · simp [harity]
      · simp only [harity, Bool.false_eq_true, ↓reduceIte]
        cases op <;>
          simp only [fields, fetch_rename ih, Op.binders, liftRenaming,
            Option.map_none, Option.map_some]
        all_goals try rfl
        case app =>
          simpa only [Term.rename] using projectCall_rename ih fuel (.node .app args) ρ
        case elements count => exact fields_rename ih (by intro i hi; rfl)
        case give e => exact fields_rename ih (by intro i hi; rfl)
        case lam e =>
          rw [renameArgs_get]
          simp only [Op.binders, Nat.zero_add, liftRenaming]
          cases args[0]? with
          | none => rfl
          | some domain =>
            dsimp only [bind, pure, Option.bind, Option.map]
            rw [binderMode_rename]
            rw [renameArgs_get]
            simp only [Op.binders, Nat.zero_add]
            cases hb : args[1]? with
            | none => cases binderMode e domain <;> rfl
            | some body =>
                simp only [Option.map_some]
                cases hm : binderMode e domain
                · rfl
                · dsimp only [bind, Option.bind]
                  rw [ih]
                  cases hc : project fuel body <;> simp only [Option.map_none, Option.map_some]
                  simp only [functionTail_rename, Control.rename, liftRenaming_one]
        all_goals
          cases h0 : fetch (project fuel) args 0 <;>
            cases h1 : fetch (project fuel) args 1 <;>
            cases h2 : fetch (project fuel) args 2 <;>
            cases h3 : fetch (project fuel) args 3 <;>
            dsimp only [bind, pure, Option.bind, Option.map]
          all_goals first | rfl | simp only [caseBody_rename, Control.rename]

theorem variable_subst_eq_rename (t : Term) (ρ : Nat → Nat) :
    t.subst (fun x => .var (ρ x)) = t.rename ρ := by
  simpa only [Term.subst_id] using (Term.subst_rename t ρ Term.var).symm

theorem project_variable_subst (fuel : Nat) (t : Term) (ρ : Nat → Nat) :
    project fuel (t.subst (fun x => .var (ρ x))) =
      (project fuel t).map (Control.rename ρ) := by
  rw [variable_subst_eq_rename, project_rename]

/-- Preserves rejection as well as the accepted count. Other names may alias;
only the queried owner must have the stated unique preimage. -/
theorem demand_rename (c : Control) (h : ∀ x, ρ x = r ↔ x = s) :
    (c.rename ρ).demand r = c.demand s := by
  have hh : ∀ x, some (ρ x) = some r ↔ x = s := by simpa using h
  simpa only [Jihoo.Quantity.Substitution.relabel_some] using
    Jihoo.Quantity.Substitution.relabel_demand c hh

theorem project_variable_subst_demand (fuel : Nat) (t : Term) {ρ : Nat → Nat} {r s : Nat}
    (h : ∀ x, ρ x = r ↔ x = s) :
    (project fuel (t.subst (fun x => .var (ρ x)))).bind (Control.demand r) =
      (project fuel t).bind (Control.demand s) := by
  rw [project_variable_subst]
  cases project fuel t with
  | none => rfl
  | some c => exact demand_rename c h

theorem check_rename (fuel depth : Nat) (owners erased : List Nat) (t : Term)
    (hρ : Function.Injective ρ) :
    check fuel (ρ depth) (owners.map ρ) (erased.map ρ) (t.rename ρ) =
      check fuel depth owners erased t := by
  unfold check
  rw [project_rename]
  cases project fuel t with
  | none => rfl
  | some c =>
      simp only [Option.map_some]
      have hd : ∀ r, (c.rename ρ).demand (ρ r) = c.demand r := by
        intro r
        exact demand_rename c (fun x => ⟨fun hx => hρ hx, fun hx => congrArg ρ hx⟩)
      simp only [List.all_map, Function.comp_def, hd]

theorem Finishes.rename (run : Finishes fuel t events) (ρ : Nat → Nat) :
    Finishes fuel (t.rename ρ) (events.map ρ) := by
  obtain ⟨c, hc, hr⟩ := run
  exact ⟨c.rename ρ, by rw [project_rename, hc]; rfl, hr.rename ρ⟩

theorem Prefix.rename (run : Prefix fuel t events) (ρ : Nat → Nat) :
    Prefix fuel (t.rename ρ) (events.map ρ) := by
  obtain ⟨c, hc, hr⟩ := run
  exact ⟨c.rename ρ, by rw [project_rename, hc]; rfl, hr.rename ρ⟩

theorem alias_finished (h : check fuel depth owners erased (t.rename ρ) = true)
    (run : Finishes fuel t events) : ∀ r ∈ owners, (events.map ρ).count r = 1 :=
  checked_finished h (run.rename ρ)

theorem alias_prefix (h : check fuel depth owners erased (t.rename ρ) = true)
    (run : Prefix fuel t events) : ∀ r ∈ owners, (events.map ρ).count r ≤ 1 :=
  checked_prefix h (run.rename ρ)

end Jihoo.NativeKernel.NativeQuantity
