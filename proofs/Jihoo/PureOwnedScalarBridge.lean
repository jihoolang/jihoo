import Jihoo.PureOwnedScalar

/-! The finite graph evaluator realizes actual strict Raw beta evaluation.
The generic substitution endpoint remains valid for all existing Raw terms;
this execution theorem covers only the represented scalar let grammar. -/
namespace Jihoo.PureOwnedScalar
open HeapLeases ScopedLend OwnedScalarContext
open CoreBridge (Raw)

theorem pureContext_bind : pureContext (bindScalar ctx) =
    (pureContext ctx).extend .i64 := by
  funext k
  cases k with
  | zero => simp [pureContext, bindScalar, Raw.Context.extend, Raw.rename]
  | succ k =>
      simp only [pureContext, bindScalar, scalarShift, List.getElem?_cons_succ, List.getElem?_map,
        Raw.Context.extend]
      cases h : ctx[k]? with
      | none => rfl
      | some b => cases b <;> simp [Raw.rename]

theorem represented_typed (valid : Graph.valid g = true) (h : Represents g ctx m root t) :
    Raw.Beta.HasType (pureContext ctx) t .i64 := by
  induction h with
  | integer shape =>
      have bound := OwnedScalarReader.graph_integer_bound valid shape
      exact Raw.Beta.HasType.integer (by change -(2^63 : Int) ≤ (_ : Nat); omega)
        (by change ((_ : Nat) : Int) < (2^63 : Int); omega)
  | scalar _ lookup _ => exact .var (by simp [pureContext, lookup])
  | app _ _ _ ia ib =>
      rw [pureContext_bind] at ib
      have lam := Raw.Beta.HasType.lam Raw.Beta.IsType.i64 rfl ib
      simpa only [Raw.subst, Raw.proposition] using Raw.Beta.HasType.app lam ia

theorem closing_bind_zero : closing (bindScalar ctx) (v :: values) 0 = .integer (Int.ofNat v) := by
  simp [closing, bindScalar_scalarBindings]

theorem closing_bind_succ : closing (bindScalar ctx) (v :: values) (k + 1) = closing ctx values k := by
  simp [closing, bindScalar_scalarBindings]

theorem closing_instantiate {body : Raw} :
    (body.subst (Raw.liftSub (closing ctx values))).subst (Raw.single (.integer (Int.ofNat v))) =
      body.subst (closing (bindScalar ctx) (v :: values)) := by
  rw [Raw.subst_comp]
  congr 1
  funext k
  cases k with
  | zero => simp [Raw.liftSub, Raw.subst, Raw.single, closing_bind_zero]
  | succ k => simp [Raw.liftSub, Raw.subst_shift, closing_bind_succ]

theorem steps_trans (a : Raw.Beta.Evaluation.Steps t u) (b : Raw.Beta.Evaluation.Steps u v) :
    Raw.Beta.Evaluation.Steps t v := by
  induction a with
  | refl => exact b
  | next hs _ ih => exact .next hs (ih b)

theorem steps_frame (f : Raw.Beta.Evaluation.Frame) (run : Raw.Beta.Evaluation.Steps t u) :
    Raw.Beta.Evaluation.Steps (f.fill t) (f.fill u) := by
  induction run with
  | refl => exact .refl
  | next hs _ ih => exact .next (.context f hs) ih

theorem execution (represented : Represents g ctx m root t)
    (evaluated : Eval g ctx root values v) :
    Raw.Beta.Evaluation.Steps (t.subst (closing ctx values)) (.integer (Int.ofNat v)) := by
  induction represented generalizing values v with
  | integer shape =>
      cases evaluated with
      | integer other => have eq := shape.symm.trans other; cases eq; simp only [Raw.subst]; exact .refl
      | scalar other _ _ => have := shape.symm.trans other; contradiction
      | app other _ _ => obtain ⟨_, h⟩ := other.head; have := shape.symm.trans h; contradiction
  | scalar shape lookup _ =>
      cases evaluated with
      | integer other => have := shape.symm.trans other; contradiction
      | scalar other lookup' value =>
          have eq := shape.symm.trans other; cases eq
          have eq := lookup.symm.trans lookup'; cases eq
          simp only [Raw.subst, closing_scalar lookup value]
          exact .refl
      | app other _ _ => obtain ⟨_, h⟩ := other.head; have := shape.symm.trans h; contradiction
  | @app root argRoot bodyRoot ctx m a b shape _ _ ia ib =>
      cases evaluated with
      | integer other => obtain ⟨_, h⟩ := shape.head; have := h.symm.trans other; contradiction
      | scalar other _ _ => obtain ⟨_, h⟩ := shape.head; have := h.symm.trans other; contradiction
      | app shape' arg body =>
          obtain ⟨rfl, rfl⟩ := shape.unique shape'
          have first := steps_frame (.appArgument .i64 (b.subst (Raw.liftSub (closing ctx values)))) (ia arg)
          simp only [Raw.Beta.Evaluation.Frame.fill] at first
          simp only [Raw.subst]
          apply steps_trans first
          apply Raw.Beta.Evaluation.Steps.next (.betaRuntime (.integer _))
          rw [closing_instantiate]
          exact ib body

end Jihoo.PureOwnedScalar
