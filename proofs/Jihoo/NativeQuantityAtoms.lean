import Jihoo.NativeQuantitySubstitution

/-! Variable and Borrow(variable) substitution on full native terms. These are
the value shapes used by Core.dependent_lend; this module proves quantity
correspondence for substitution, not that an arbitrary Lend is well typed or
that its borrowed owner is live. Effects are deliberately not substitutable. -/
namespace Jihoo.NativeKernel.NativeQuantity

open Jihoo.Quantity
open Jihoo.Quantity.Substitution (Atom liftAtoms liftPartial)

def atomTerm : Atom → Term
  | .var x => .var x
  | .borrow x => .node .borrow [.var x]

def liftedAtoms : Nat → (Nat → Atom) → Nat → Atom
  | 0, σ => σ
  | n + 1, σ => liftAtoms (liftedAtoms n σ)

theorem atomTerm_shift (a : Atom) : atomTerm a.shift = (atomTerm a).rename Nat.succ := by
  cases a <;> simp [atomTerm, Atom.shift, Term.rename, renameArgs, Op.binders, liftRenaming]

theorem liftedAtoms_term (n : Nat) (σ : Nat → Atom) :
    (fun x => atomTerm (liftedAtoms n σ x)) = liftSub n (fun x => atomTerm (σ x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext x
      cases x with
      | zero => rfl
      | succ x =>
          simp only [liftedAtoms, liftAtoms, liftSub, liftSubOne, atomTerm_shift]
          exact congrArg (Term.rename Nat.succ) (congrFun ih x)

theorem liftedAtoms_event (σ : Nat → Atom) :
    (fun x => (liftedAtoms 1 σ x).event) = liftPartial (fun x => (σ x).event) := by
  funext x
  cases x with
  | zero => rfl
  | succ x => cases h : σ x <;> simp [liftedAtoms, liftAtoms, Atom.event, Atom.shift, liftPartial, h]

theorem liftAtoms_event (σ : Nat → Atom) :
    (fun x => (liftAtoms σ x).event) = liftPartial (fun x => (σ x).event) :=
  liftedAtoms_event σ

theorem binderMode_atom_subst (erased : Bool) (t : Term) (σ : Nat → Atom) :
    binderMode erased (t.subst (fun x => atomTerm (σ x))) = binderMode erased t := by
  cases erased <;> simp only [binderMode, Bool.false_eq_true, ↓reduceIte]
  case false =>
    cases t with
    | var x => cases h : σ x <;> simp [Term.subst, atomTerm, h]
    | node op args =>
      cases op <;> cases args with
      | nil => simp [Term.subst, substArgs]
      | cons a rest =>
        cases rest with
        | nil => simp [Term.subst, substArgs]
        | cons b tail => cases tail <;> simp [Term.subst, substArgs]

theorem reclose_relabel (c : Control) (ρ : Nat → Option Nat) :
    reclose (c.relabel ρ) = (reclose c).relabel ρ := by
  cases c <;> try rfl
  case use x => cases h : ρ x <;> simp [Control.relabel, reclose, h]

theorem openScopes_relabel (n : Nat) (c : Control) (ρ : Nat → Option Nat) :
    openScopes n (c.relabel ρ) = (openScopes n c).map (fun c => c.relabel ρ) := by
  induction n generalizing c ρ with
  | zero => simp only [openScopes, reclose_relabel, Option.map_some]
  | succ n ih =>
      cases c <;> simp only [Control.relabel, openScopes, Option.map_none]
      case use x => cases ρ x <;> rfl
      case scope mode body =>
        rw [ih]
        cases openScopes n body <;> rfl

theorem openFunctions_relabel (n : Nat) (c : Control) (ρ : Nat → Option Nat) :
    openFunctions n (c.relabel ρ) = (openFunctions n c).map (fun c => c.relabel ρ) := by
  cases n with
  | zero => rfl
  | succ n =>
      cases c <;> simp only [Control.relabel, openFunctions, Option.map_none]
      case use x => cases ρ x <;> rfl
      case closure body => exact openScopes_relabel _ _ _

theorem lambdaHead_atom_subst (t : Term) (σ : Nat → Atom) :
    lambdaHead (t.subst (fun x => atomTerm (σ x))) = lambdaHead t := by
  cases t with
  | var x => cases h : σ x <;> simp [Term.subst, atomTerm, h, lambdaHead]
  | node op args =>
      cases op <;> cases args with
      | nil => simp [Term.subst, substArgs, lambdaHead]
      | cons a args =>
          cases args with
          | nil => simp [Term.subst, substArgs, lambdaHead]
          | cons b args => cases args <;> simp [Term.subst, substArgs, lambdaHead]

theorem functionTail_atom_subst (t : Term) (c : Control) (σ : Nat → Atom) :
    functionTail (t.subst (fun x => atomTerm (σ x))) (c.relabel (fun x => (σ x).event)) =
      (functionTail t c).relabel (fun x => (σ x).event) := by
  simp only [functionTail, lambdaHead_atom_subst]
  split
  · cases c <;> try rfl
    case use x => cases h : σ x <;> simp [Control.relabel, unclose, Atom.event, h]
  · rfl

theorem caseBody_relabel (n : Nat) (c : Control) (ρ : Nat → Option Nat) :
    caseBody n (c.relabel ρ) = (caseBody n c).relabel ρ := by
  unfold caseBody
  rw [openFunctions_relabel]
  cases openFunctions n c <;> rfl

theorem substArgs_length (op : Op) (σ : Nat → Term) (offset : Nat) (xs : List Term) :
    (substArgs op σ offset xs).length = xs.length := by
  induction xs generalizing offset <;> simp [substArgs, *]

theorem substArgs_get (op : Op) (σ : Nat → Term) (offset i : Nat) (xs : List Term) :
    (substArgs op σ offset xs)[i]? =
      (xs[i]?).map (Term.subst (liftSub (op.binders (offset + i)) σ)) := by
  induction xs generalizing offset i with
  | nil => simp [substArgs]
  | cons t ts ih =>
    cases i with
    | zero => simp [substArgs]
    | succ i =>
      simpa [substArgs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (ih (offset + 1) i)

private theorem fetch_atom_subst {f : Term → Option Control} {σ : Nat → Atom}
    (h : ∀ (t : Term) (σ : Nat → Atom), f (t.subst (fun x => atomTerm (σ x))) =
      (f t).map (fun c => c.relabel (fun x => (σ x).event))) :
    fetch f (substArgs op (fun x => atomTerm (σ x)) 0 xs) i =
      (fetch f xs i).map (fun c => c.relabel
        (fun x => (liftedAtoms (op.binders i) σ x).event)) := by
  unfold fetch
  rw [substArgs_get]
  simp only [Nat.zero_add, ← liftedAtoms_term]
  cases xs[i]? <;> simp [h]

private theorem fields_atom_subst {f : Term → Option Control} {σ : Nat → Atom}
    (h : ∀ (t : Term) (σ : Nat → Atom), f (t.subst (fun x => atomTerm (σ x))) =
      (f t).map (fun c => c.relabel (fun x => (σ x).event)))
    (hz : ∀ i ∈ indices, op.binders i = 0) :
    fields f (substArgs op (fun x => atomTerm (σ x)) 0 xs) indices =
      (fields f xs indices).map (fun c => c.relabel (fun x => (σ x).event)) := by
  induction indices with
  | nil => rfl
  | cons i is ih =>
      simp only [fields, fetch_atom_subst h, hz i (by simp), liftedAtoms]
      rw [ih (fun j hj => hz j (by simp [hj]))]
      cases fetch f xs i <;> cases fields f xs is <;> rfl

theorem liftedAtoms_add (a b : Nat) (σ : Nat → Atom) :
    liftedAtoms a (liftedAtoms b σ) = liftedAtoms (a + b) σ := by
  induction a with
  | zero => simp [liftedAtoms]
  | succ a ih => simp only [liftedAtoms, Nat.succ_add, ih]

theorem callResult_shift (locals : List Bool) (t : Term) (b : Bool) :
    callResult (b :: locals) (t.rename Nat.succ) = callResult locals t := by
  cases t with
  | var => simp [Term.rename, callResult]
  | node op args => cases op <;> simp [Term.rename, callResult]

theorem callResult_liftSub (locals : List Bool) (σ : Nat → Atom) (x : Nat) :
    callResult locals (liftSub locals.length (fun x => atomTerm (σ x)) x) =
      locals[x]?.getD false := by
  induction locals generalizing x with
  | nil => cases h : σ x <;> simp [liftSub, atomTerm, h, callResult]
  | cons b locals ih =>
      cases x with
      | zero => rfl
      | succ x =>
          simpa only [List.length_cons, liftSub, liftSubOne, callResult_shift,
            List.getElem?_cons_succ] using ih x

theorem callResult_atom_subst (locals : List Bool) (t : Term) (σ : Nat → Atom) :
    callResult locals (t.subst (liftSub locals.length (fun x => atomTerm (σ x)))) =
      callResult locals t := by
  cases t with
  | var x => simpa only [Term.subst, callResult] using callResult_liftSub locals σ x
  | node op args => cases op <;> simp [Term.subst, callResult]

theorem domainNonFunction_atom_subst (t : Term) (σ : Nat → Atom) :
    domainNonFunction (t.subst (fun x => atomTerm (σ x))) = domainNonFunction t := by
  cases t with
  | var x => cases h : σ x <;> simp [Term.subst, atomTerm, h, domainNonFunction]
  | node op args => cases op <;> simp [Term.subst, domainNonFunction]

theorem splitSpine_atom_subst (fuel : Nat) (head : Term) (args : List Term) (σ : Nat → Atom) :
    splitSpine fuel (head.subst (fun x => atomTerm (σ x)))
        (args.map (Term.subst (fun x => atomTerm (σ x)))) =
      (splitSpine fuel head args).map
        (fun (head, args) => (head.subst (fun x => atomTerm (σ x)),
          args.map (Term.subst (fun x => atomTerm (σ x))))) := by
  induction fuel generalizing head args σ with
  | zero => rfl
  | succ fuel ih =>
      cases head with
      | var x => cases h : σ x <;> simp [Term.subst, atomTerm, h, splitSpine]
      | node op children =>
          cases op <;> cases children with
          | nil => simp [Term.subst, substArgs, splitSpine]
          | cons f tail =>
            cases tail with
            | nil => simp [Term.subst, substArgs, splitSpine]
            | cons a rest =>
              cases rest <;> simp [Term.subst, substArgs, Op.binders, liftSub, splitSpine]
              all_goals simpa only [List.map_cons] using ih f (a :: args) σ

def CallPlan.atomSubstAt (depth : Nat) (σ : Nat → Atom) (p : CallPlan) : CallPlan :=
  ⟨p.modes, p.runtimeArgs.map (Term.subst (fun x => atomTerm (σ x))),
    p.body.subst (liftSub (p.modes.length + depth) (fun x => atomTerm (σ x)))⟩

theorem peelCallAux_atom_subst (fuel : Nat) (locals : List Bool) (linearSeen : Bool) (head : Term)
    (args : List Term) (σ : Nat → Atom) :
    peelCallAux fuel locals linearSeen (head.subst (liftSub locals.length (fun x => atomTerm (σ x))))
        (args.map (Term.subst (fun x => atomTerm (σ x)))) =
      (peelCallAux fuel locals linearSeen head args).map (CallPlan.atomSubstAt locals.length σ) := by
  induction fuel generalizing locals linearSeen head args σ with
  | zero => rfl
  | succ fuel ih =>
    cases args with
    | nil =>
        simp only [List.map_nil, peelCallAux, callResult_atom_subst]
        split <;> simp [CallPlan.atomSubstAt]
    | cons a args =>
      cases head with
      | var x =>
          rw [Term.subst, ← liftedAtoms_term]
          cases h : liftedAtoms locals.length σ x <;> simp [atomTerm, h, peelCallAux]
      | node op children =>
        cases op <;> cases children with
        | nil => simp [Term.subst, substArgs, peelCallAux]
        | cons domain tail =>
          cases tail with
          | nil => simp [Term.subst, substArgs, peelCallAux]
          | cons body rest =>
            cases rest <;> simp only [Term.subst, substArgs, List.map_cons, Op.binders,
              liftSub, peelCallAux]
            all_goals first
            | rfl
            | (
              rename_i erased
              rw [← liftedAtoms_term, binderMode_atom_subst, domainNonFunction_atom_subst]
              cases hd : binderMode erased domain with
              | none => rfl
              | some mode =>
                dsimp only [bind, pure, Option.bind]
                have hr := ih (domainNonFunction domain :: locals) (linearSeen || mode == .linear) body args σ
                simp only [List.length_cons, liftSub] at hr
                rw [← liftedAtoms_term] at hr
                rw [hr]
                cases peelCallAux fuel (domainNonFunction domain :: locals) (linearSeen || mode == .linear) body args <;>
                  cases erased <;> simp [CallPlan.atomSubstAt, Nat.add_comm, Nat.add_left_comm])

theorem peelCall_atom_subst (fuel : Nat) (locals : List Bool) (head : Term)
    (args : List Term) (σ : Nat → Atom) :
    peelCall fuel locals (head.subst (liftSub locals.length (fun x => atomTerm (σ x))))
        (args.map (Term.subst (fun x => atomTerm (σ x)))) =
      (peelCall fuel locals head args).map (CallPlan.atomSubstAt locals.length σ) := by
  exact peelCallAux_atom_subst fuel locals false head args σ

theorem sequence_relabel (cs : List Control) (ρ : Nat → Option Nat) :
    sequence (cs.map (fun c => c.relabel ρ)) = (sequence cs).relabel ρ := by
  induction cs <;> simp [sequence, Control.relabel, *]

theorem scopes_relabel (modes : List BinderMode) (c : Control) (σ : Nat → Atom) :
    (Control.scopes modes c).relabel (fun x => (σ x).event) =
      Control.scopes modes (c.relabel (fun x => (liftedAtoms modes.length σ x).event)) := by
  induction modes generalizing σ with
  | nil => rfl
  | cons mode modes ih =>
      change Control.scope mode ((Control.scopes modes c).relabel (liftPartial (fun x => (σ x).event))) =
        Control.scope mode (Control.scopes modes
          (c.relabel (fun x => (liftedAtoms (modes.length + 1) σ x).event)))
      rw [← liftAtoms_event, ih]
      change Control.scope mode (Control.scopes modes
          (c.relabel (fun x => (liftedAtoms modes.length (liftedAtoms 1 σ) x).event))) = _
      rw [liftedAtoms_add]

theorem finishCall_atom_subst {f : Term → Option Control}
    (h : ∀ (t : Term) (σ : Nat → Atom), f (t.subst (fun x => atomTerm (σ x))) =
      (f t).map (fun c => c.relabel (fun x => (σ x).event))) (p : CallPlan) (σ : Nat → Atom) :
    finishCall f (p.atomSubstAt 0 σ) =
      (finishCall f p).map (fun c => c.relabel (fun x => (σ x).event)) := by
  have hm : ∀ (ts : List Term), (ts.map (Term.subst (fun x => atomTerm (σ x)))).mapM f =
      (ts.mapM f).map (List.map (fun c => c.relabel (fun x => (σ x).event))) := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      simp only [List.map_cons, List.mapM_cons, h, ih]
      cases f t <;> cases ts.mapM f <;> rfl
  simp only [finishCall, CallPlan.atomSubstAt, Nat.add_zero, hm, ← liftedAtoms_term, h]
  cases p.runtimeArgs.mapM f <;> cases f p.body <;>
    simp [sequence_relabel, scopes_relabel, Control.relabel]

theorem projectCall_atom_subst {f : Term → Option Control}
    (h : ∀ (t : Term) (σ : Nat → Atom), f (t.subst (fun x => atomTerm (σ x))) =
      (f t).map (fun c => c.relabel (fun x => (σ x).event))) (fuel : Nat)
    (t : Term) (σ : Nat → Atom) :
    projectCall fuel f (t.subst (fun x => atomTerm (σ x))) =
      (projectCall fuel f t).map (fun c => c.relabel (fun x => (σ x).event)) := by
  unfold projectCall
  have hs := splitSpine_atom_subst fuel t [] σ
  simp only [List.map_nil] at hs
  rw [hs]
  cases splitSpine fuel t [] with
  | none => rfl
  | some pair =>
      obtain ⟨head, args⟩ := pair
      dsimp only [bind, pure, Option.bind, Option.map]
      rw [show head.subst (fun x => atomTerm (σ x)) =
          head.subst (liftSub ([] : List Bool).length (fun x => atomTerm (σ x))) from rfl,
        peelCall_atom_subst]
      cases hp : peelCall fuel [] head args with
      | none => rfl
      | some p => exact finishCall_atom_subst h p σ

/-- Full syntax, all binding edges, complete Option result, no effectful
substitutions. A borrow has zero ownership demand but retains its owner index
in the concrete term, including under subsequent binders. -/
theorem project_atom_subst (fuel : Nat) (t : Term) (σ : Nat → Atom) :
    project fuel (t.subst (fun x => atomTerm (σ x))) =
      (project fuel t).map (fun c => c.relabel (fun x => (σ x).event)) := by
  induction fuel generalizing t σ with
  | zero => rfl
  | succ fuel ih =>
    cases t with
    | var x => cases h : σ x <;> simp [Term.subst, project, atomTerm, Atom.event, Control.relabel, Op.arity, h]
    | node op args =>
      simp only [Term.subst, project, substArgs_length]
      by_cases harity : args.length != op.arity
      · simp [harity]
      · simp only [harity, Bool.false_eq_true, ↓reduceIte]
        cases op <;>
          simp only [fields, fetch_atom_subst ih, Op.binders, liftedAtoms, liftAtoms_event,
            Option.map_none, Option.map_some]
        all_goals try rfl
        case app =>
          simpa only [Term.subst] using projectCall_atom_subst ih fuel (.node .app args) σ
        case elements count => exact fields_atom_subst ih (by intro i hi; rfl)
        case give e => exact fields_atom_subst ih (by intro i hi; rfl)
        case lam e =>
          rw [substArgs_get]
          simp only [Op.binders, Nat.zero_add, liftSub]
          cases args[0]? with
          | none => rfl
          | some domain =>
            dsimp only [bind, pure, Option.bind, Option.map]
            rw [binderMode_atom_subst]
            rw [substArgs_get]
            simp only [Op.binders, Nat.zero_add, ← liftedAtoms_term]
            cases hb : args[1]? with
            | none => cases binderMode e domain <;> rfl
            | some body =>
                simp only [Option.map_some]
                cases hm : binderMode e domain
                · rfl
                · dsimp only [bind, Option.bind]
                  rw [ih]
                  cases hc : project fuel body <;> simp only [Option.map_none, Option.map_some]
                  rw [functionTail_atom_subst]
                  simp only [Control.relabel, liftedAtoms_event]
        all_goals
          cases h0 : fetch (project fuel) args 0 <;>
            cases h1 : fetch (project fuel) args 1 <;>
            cases h2 : fetch (project fuel) args 2 <;>
            cases h3 : fetch (project fuel) args 3 <;>
            dsimp only [bind, pure, Option.bind, Option.map]
          all_goals first | rfl | simp only [caseBody_relabel, Control.relabel]

theorem project_atom_subst_demand (fuel : Nat) (t : Term) (σ : Nat → Atom)
    (h : ∀ x, (σ x).event = some r ↔ x = s) :
    (project fuel (t.subst (fun x => atomTerm (σ x)))).bind (Control.demand r) =
      (project fuel t).bind (Control.demand s) := by
  rw [project_atom_subst]
  cases project fuel t with
  | none => rfl
  | some c => exact Jihoo.Quantity.Substitution.relabel_demand c h

theorem Finishes.atom_subst (run : Finishes fuel t events) (σ : Nat → Atom) :
    Finishes fuel (t.subst (fun x => atomTerm (σ x)))
      (events.filterMap (fun x => (σ x).event)) := by
  obtain ⟨c, hc, hr⟩ := run
  exact ⟨c.relabel (fun x => (σ x).event), by rw [project_atom_subst, hc]; rfl,
    hr.relabel _⟩

theorem Prefix.atom_subst (run : Prefix fuel t events) (σ : Nat → Atom) :
    Prefix fuel (t.subst (fun x => atomTerm (σ x)))
      (events.filterMap (fun x => (σ x).event)) := by
  obtain ⟨c, hc, hr⟩ := run
  exact ⟨c.relabel (fun x => (σ x).event), by rw [project_atom_subst, hc]; rfl,
    hr.relabel _⟩

theorem reader_projection (fuel owner : Nat) (t : Term) :
    project fuel (t.subst (fun x => atomTerm (Jihoo.Quantity.Substitution.openBorrow owner x))) =
      (project fuel t).map (fun c => c.relabel Jihoo.Quantity.Substitution.dropBorrow) := by
  rw [project_atom_subst]
  congr 1
  funext c
  congr 1
  funext x
  cases x <;> rfl

theorem reader_demand (fuel owner r : Nat) (t : Term) :
    (project fuel (t.subst (fun x => atomTerm (Jihoo.Quantity.Substitution.openBorrow owner x)))).bind
        (Control.demand r) =
      (project fuel t).bind (fun c => (Control.scope .borrowed c).demand r) := by
  rw [reader_projection]
  cases project fuel t with
  | none => rfl
  | some c => exact Jihoo.Quantity.Substitution.drop_borrow_demand c

theorem reader_finished (run : Finishes fuel t events) (owner : Nat) :
    Finishes fuel
      (t.subst (fun x => atomTerm (Jihoo.Quantity.Substitution.openBorrow owner x)))
      (discharge events) := by
  have run' := run.atom_subst (Jihoo.Quantity.Substitution.openBorrow owner)
  have he : (fun x => (Jihoo.Quantity.Substitution.openBorrow owner x).event) =
      Jihoo.Quantity.Substitution.dropBorrow := by funext x; cases x <;> rfl
  simpa only [he, Jihoo.Quantity.Substitution.drop_borrow_trace] using run'

theorem reader_prefix (run : Prefix fuel t events) (owner : Nat) :
    Prefix fuel
      (t.subst (fun x => atomTerm (Jihoo.Quantity.Substitution.openBorrow owner x)))
      (discharge events) := by
  have run' := run.atom_subst (Jihoo.Quantity.Substitution.openBorrow owner)
  have he : (fun x => (Jihoo.Quantity.Substitution.openBorrow owner x).event) =
      Jihoo.Quantity.Substitution.dropBorrow := by funext x; cases x <;> rfl
  simpa only [he, Jihoo.Quantity.Substitution.drop_borrow_trace] using run'

theorem continuation_projection (fuel owner : Nat) (t : Term) :
    project fuel (t.subst (fun x => atomTerm (Jihoo.Quantity.Substitution.openVariable owner x))) =
      (project fuel t).map (Control.rename (openOwner owner)) := by
  rw [project_atom_subst]
  have he : (fun x => (Jihoo.Quantity.Substitution.openVariable owner x).event) =
      (fun x => some (openOwner owner x)) := by funext x; cases x <;> rfl
  simp only [he, Jihoo.Quantity.Substitution.relabel_some]

theorem continuation_finished (run : Finishes fuel t events) (owner : Nat) :
    Finishes fuel
      (t.subst (fun x => atomTerm (Jihoo.Quantity.Substitution.openVariable owner x)))
      (events.map (openOwner owner)) := by
  obtain ⟨c, hc, hr⟩ := run
  exact ⟨c.rename (openOwner owner), by rw [continuation_projection, hc]; rfl, hr.rename _⟩

theorem continuation_prefix (run : Prefix fuel t events) (owner : Nat) :
    Prefix fuel
      (t.subst (fun x => atomTerm (Jihoo.Quantity.Substitution.openVariable owner x)))
      (events.map (openOwner owner)) := by
  obtain ⟨c, hc, hr⟩ := run
  exact ⟨c.rename (openOwner owner), by rw [continuation_projection, hc]; rfl, hr.rename _⟩

end Jihoo.NativeKernel.NativeQuantity
