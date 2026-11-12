import Jihoo.SymbolicCoreIndices
import Jihoo.SizedCoreAccounting

/-! Instantiation into the established sized Core judgment. The induction
supplies allocation, read, release and alias-transfer premises from static
rules, including substitution of an argument into a dependent result type. -/
namespace Jihoo.SymbolicCoreTyping
open ScopedLend SymbolicCoreContext
open DependentBufferIndices (Expr)

theorem Index.total (typed : Index g ctx root e) (closing : Closes ctx closed) :
    ∃ n, e.eval (SizedBufferContext.naturalEnv closed) = some n ∧ n < 2^64 := by
  obtain ⟨n, value⟩ := closing.available typed.available
  exact ⟨n, value, typed.represents.eval_bound closing.validNats value⟩

theorem Scalar.instantiate (typed : Scalar g ctx root) (closing : Closes ctx closed) :
    SizedCoreTyping.ScalarTyped g closed root := by
  cases typed with
  | literal shape bound => exact .literal shape bound
  | var shape lookup => exact .var shape (closing.scalar_lookup lookup)

theorem Evidence.instantiate (typed : Evidence g ctx root a b)
    (closing : Closes ctx closed)
    (left : a.eval (SizedBufferContext.naturalEnv closed) = some i)
    (right : b.eval (SizedBufferContext.naturalEnv closed) = some n) :
    DependentBufferIndices.BoundEvidence g (SizedBufferContext.proofs closed) root i n := by
  cases typed with
  | decide shape l r bi bn truth =>
      simp only [Expr.eval, Option.some.injEq] at left right
      subst i; subst n
      exact .decide shape l r bi bn truth
  | var shape lookup =>
      obtain ⟨fact, found, fa, fb⟩ := closing.bound_lookup lookup
      have ia := Option.some.inj (left.symm.trans fa)
      have nb := Option.some.inj (right.symm.trans fb)
      subst i; subst n
      exact .var shape (by simp [SizedBufferContext.proofs, found])

theorem index_shift {e : Expr} (length : e.eval (SizedBufferContext.naturalEnv closed) = some n) :
    (shift e).eval (SizedBufferContext.naturalEnv (value :: closed)) = some n :=
  (e.eval_rename (by intro k; rfl)).trans length

/-- A single static derivation instantiates at every well-formed closing
context. The conclusion is the existing judgment, on exactly the same graph,
not an unrelated evaluator or an assumed safety certificate. -/
theorem Typing.instantiate (typed : Typing g ctx sizes root kind)
    (closing : Closes ctx closed)
    (inventory : SizesEval (SizedBufferContext.naturalEnv closed) sizes concrete)
    (result : ResultEval (SizedBufferContext.naturalEnv closed) kind resultKind) :
    SizedCoreTyping.Typing g closed concrete root resultKind := by
  induction typed generalizing closed concrete resultKind with
  | literal shape bound =>
      cases inventory
      cases resultKind <;> simp only [ResultEval] at result
      exact .literal shape bound
  | scalar shape lookup =>
      cases inventory
      cases resultKind <;> simp only [ResultEval] at result
      exact .scalar shape (closing.scalar_lookup lookup)
  | owner shape lookup =>
      cases inventory with
      | cons length rest =>
          cases rest
          cases resultKind <;> simp only [ResultEval] at result
          case owner n =>
            have eq := Option.some.inj (length.symm.trans result)
            subst n
            exact .owner shape (closing.owner_lookup lookup)
  | ownedLet shape lam varShape lookup size annotation body ih =>
      obtain ⟨n, found, length⟩ := inventory.lookup size
      apply SizedCoreTyping.Typing.ownedLet shape lam varShape (closing.owner_lookup lookup)
        found (annotation.instantiate length)
      apply ih closing.transferred
      · simpa only [naturalEnv_transferred, shiftSizes, shiftResult] using inventory.shift (value := SizedBufferContext.Entry.dead)
      · simpa only [naturalEnv_transferred, shiftSizes, shiftResult] using result.shift (value := SizedBufferContext.Entry.dead)
  | framedApp shape lam bound annotation argument body ia ib =>
      obtain ⟨n, length, _⟩ := annotation.choose_spec.2.total closing
      apply SizedCoreTyping.Typing.framedApp shape lam
        (by simpa only [← inventory.length] using bound) (annotation.instantiate length)
      · exact ia closing.producer ((inventory.take _).congr (naturalEnv_producer closed).symm)
          (by simpa only [ResultEval, naturalEnv_producer] using length)
      · apply ib closing.callBody
        · simpa only [naturalEnv_callBody, shiftSizes] using (SizesEval.cons length (inventory.drop _)).shift (value := SizedBufferContext.Entry.dead)
        · simpa only [naturalEnv_callBody, shiftResult] using result.shift (value := SizedBufferContext.Entry.dead)
  | naturalLet shape lam domain argument body ih =>
      obtain ⟨n, value, bound⟩ := argument.total closing
      exact .naturalLet shape lam domain (argument.instantiate value)
        (ih (closing.nat bound) inventory.shift (result.unbeta value))
  | allocate shape lam annotation alloc length initial body ih =>
      obtain ⟨n, value, bound⟩ := length.total closing
      apply SizedCoreTyping.Typing.allocate shape lam (annotation.instantiate value) alloc
        (length.instantiate value) (initial.instantiate closing)
      apply ih closing.fresh
      · have extended := SizesEval.cons value inventory
        simpa only [naturalEnv_fresh, shiftSizes, shiftResult] using extended.shift (value := SizedBufferContext.Entry.dead)
      · simpa only [naturalEnv_fresh, shiftSizes, shiftResult] using result.shift (value := SizedBufferContext.Entry.dead)
  | allocation shape length initial =>
      cases inventory
      cases resultKind <;> simp only [ResultEval] at result
      exact .allocation shape (length.instantiate result) (initial.instantiate closing)
  | free shape varShape lookup bound body ih =>
      apply SizedCoreTyping.Typing.free shape varShape (closing.owner_lookup lookup)
        (by simpa only [← inventory.length] using bound)
      apply ih closing.consumed
      · simpa only [naturalEnv_consumed] using inventory.eraseIdx _
      · simpa only [naturalEnv_consumed] using result
  | branch shape left right yes no iy ino =>
      obtain ⟨a, av, _⟩ := left.total closing
      obtain ⟨b, bv, _⟩ := right.total closing
      apply SizedCoreTyping.Typing.branch shape (left.instantiate av) (right.instantiate bv)
      · intro lt
        exact iy (closing.bound av bv lt) inventory.shift result.shift
      · intro _
        exact ino closing inventory result
  | lend shape varShape lookup size refTy ownerTy index evidence body ih =>
      obtain ⟨n, found, length⟩ := inventory.lookup size
      obtain ⟨i, iv, _⟩ := index.total closing.dead
      have shiftedLength := index_shift (value := SizedBufferContext.Entry.dead) length
      apply SizedCoreTyping.Typing.lend shape varShape (closing.owner_lookup lookup) found
        (refTy.instantiate length)
      · exact ownerTy.instantiate (index_shift length)
      · exact index.instantiate iv
      · exact evidence.instantiate closing.dead iv shiftedLength
      · exact ih closing.scalarReturned (by simpa [shiftSizes, List.map_map, Function.comp_def, SizedBufferContext.scalarReturned] using inventory.shift.shift)
          result.shift.shift
  | ownedLend shape varShape lookup size refTy length resultTy ownerTy index evidence body ih =>
      obtain ⟨n, found, nv⟩ := inventory.lookup size
      obtain ⟨m, mv, _⟩ := resultTy.choose_spec.2.total closing
      obtain ⟨i, iv, _⟩ := index.total closing.dead
      apply SizedCoreTyping.Typing.ownedLend shape varShape (closing.owner_lookup lookup) found
        (refTy.instantiate nv) (length.instantiate (index_shift mv)) (resultTy.instantiate mv)
        (ownerTy.instantiate (index_shift nv)) (index.instantiate iv)
        (evidence.instantiate closing.dead iv (index_shift nv))
      apply ih closing.ownedReturned
      · simpa only [naturalEnv_ownedReturned, shiftSizes, List.map_map, Function.comp_def] using
          (SizesEval.cons mv inventory).shift.shift (value := SizedBufferContext.Entry.dead)
      · simpa only [naturalEnv_ownedReturned, shiftResult] using result.shift.shift (value := SizedBufferContext.Entry.dead)

/-- Output interpretation is constructed, not an assumption of the final
safety theorem. Initial resource lengths are supplied by the input inventory. -/
theorem Typing.result_total (typed : Typing g ctx sizes root kind)
    (closing : Closes ctx closed)
    (inventory : SizesEval (SizedBufferContext.naturalEnv closed) sizes concrete) :
    ∃ resultKind, ResultEval (SizedBufferContext.naturalEnv closed) kind resultKind := by
  induction typed generalizing closed concrete with
  | literal _ _ | scalar _ _ => exact ⟨.scalar, trivial⟩
  | owner shape lookup =>
      cases inventory with
      | cons length rest => exact ⟨.owner _, length⟩
  | ownedLet shape lam varShape lookup size annotation body ih =>
      have inputs := inventory.shift (value := SizedBufferContext.Entry.dead)
      obtain ⟨resultKind, result⟩ := ih closing.transferred
        (inputs.congr (naturalEnv_transferred closed _).symm)
      refine ⟨resultKind, ?_⟩
      apply ResultEval.unshift (value := SizedBufferContext.Entry.dead)
      simpa only [naturalEnv_transferred, shiftResult] using result
  | framedApp shape lam bound annotation argument body ia ib =>
      obtain ⟨n, nv, _⟩ := annotation.choose_spec.2.total closing
      obtain ⟨rk, result⟩ := ib closing.callBody
        (((SizesEval.cons nv (inventory.drop _)).shift (value := SizedBufferContext.Entry.dead)).congr
          (naturalEnv_callBody closed).symm)
      exact ⟨rk, ResultEval.unshift (by simpa only [naturalEnv_callBody, shiftResult] using result)⟩
  | naturalLet shape lam domain argument body ih =>
      obtain ⟨n, value, bound⟩ := argument.total closing
      obtain ⟨resultKind, result⟩ := ih (closing.nat bound) inventory.shift
      exact ⟨resultKind, result.beta value⟩
  | allocate shape lam annotation alloc length initial body ih =>
      obtain ⟨n, value, _⟩ := length.total closing
      have extended := SizesEval.cons value inventory
      obtain ⟨resultKind, result⟩ := ih closing.fresh
        ((extended.shift (value := SizedBufferContext.Entry.dead)).congr (naturalEnv_fresh closed).symm)
      refine ⟨resultKind, ?_⟩
      apply ResultEval.unshift (value := SizedBufferContext.Entry.dead)
      simpa only [naturalEnv_fresh, shiftResult] using result
  | allocation shape length initial =>
      obtain ⟨n, value, _⟩ := length.total closing
      exact ⟨.owner n, value⟩
  | free shape varShape lookup bound body ih =>
      obtain ⟨resultKind, result⟩ := ih closing.consumed
        ((inventory.eraseIdx _).congr (naturalEnv_consumed closed _).symm)
      exact ⟨resultKind, result.congr (naturalEnv_consumed closed _)⟩
  | branch shape left right yes no iy ino => exact ino closing inventory
  | lend shape varShape lookup size refTy ownerTy index evidence body ih =>
      obtain ⟨resultKind, result⟩ := ih closing.scalarReturned
        (by simpa [shiftSizes, List.map_map, Function.comp_def, SizedBufferContext.scalarReturned] using inventory.shift.shift)
      exact ⟨resultKind, result.unshift.unshift⟩
  | ownedLend shape varShape lookup size refTy length resultTy ownerTy index evidence body ih =>
      obtain ⟨m, mv, _⟩ := resultTy.choose_spec.2.total closing
      obtain ⟨rk, result⟩ := ih closing.ownedReturned
        (by simpa only [naturalEnv_ownedReturned, shiftSizes, List.map_map, Function.comp_def] using
          (SizesEval.cons mv inventory).shift.shift (value := SizedBufferContext.Entry.dead))
      refine ⟨rk, ?_⟩
      apply ResultEval.unshift (value := SizedBufferContext.Entry.dead)
      apply ResultEval.unshift (value := SizedBufferContext.Entry.dead)
      simpa only [naturalEnv_ownedReturned, shiftResult] using result

/-- A value-independent derivation constructs a terminating source execution,
its safe primitive steps, exact ownership accounting, and the interpreted
result type. It assumes neither successful evaluation nor a safe trace. -/
theorem Typing.total_accounted (typed : Typing g ctx sizes root kind)
    (closing : Closes ctx closed)
    (inventory : SizesEval (SizedBufferContext.naturalEnv closed) sizes concrete)
    (agree : SizedBufferContext.Agrees closed owners env)
    (layout : SizedBufferContext.Layout s owners concrete)
    (valid : SizedBufferHeap.Valid s) (owned : LinearHeapPrograms.Owns s.heap owners) :
    ∃ resultKind value events t,
      ResultEval (SizedBufferContext.naturalEnv closed) kind resultKind ∧
      SizedCoreExecution.Eval g env root s value events t ∧
      SizedBufferHeap.Steps s events t ∧ SizedBufferHeap.Valid t ∧
      SizedCoreTyping.Post resultKind t value ∧ SizedCoreTyping.Account owners value events := by
  obtain ⟨resultKind, result⟩ := typed.result_total closing inventory
  obtain ⟨value, events, t, run, steps, vt, post, account⟩ :=
    (typed.instantiate closing inventory result).total_accounted agree layout valid owned
  exact ⟨resultKind, value, events, t, result, run, steps, vt, post, account⟩

/-- Every lexical run has the typing-derived steps and ownership accounting;
the source evaluator does not consult symbolic annotations or proof plans. -/
theorem Typing.every_run_accounted (typed : Typing g ctx sizes root kind)
    (closing : Closes ctx closed)
    (inventory : SizesEval (SizedBufferContext.naturalEnv closed) sizes concrete)
    (agree : SizedBufferContext.Agrees closed owners env)
    (layout : SizedBufferContext.Layout s owners concrete)
    (valid : SizedBufferHeap.Valid s) (owned : LinearHeapPrograms.Owns s.heap owners)
    (run : SizedCoreExecution.Eval g env root s value events t) :
    ∃ resultKind, ResultEval (SizedBufferContext.naturalEnv closed) kind resultKind ∧
      SizedBufferHeap.Steps s events t ∧ SizedBufferHeap.Valid t ∧
      SizedCoreTyping.Post resultKind t value ∧ SizedCoreTyping.Account owners value events := by
  obtain ⟨resultKind, v, es, u, result, canonical, steps, vu, post, account⟩ :=
    typed.total_accounted closing inventory agree layout valid owned
  obtain ⟨rfl, rfl, rfl⟩ := run.deterministic canonical
  exact ⟨resultKind, result, steps, vu, post, account⟩

end Jihoo.SymbolicCoreTyping
