import Jihoo.CommonCompositionContract

/-! A literal leaf only. No recursive correctness or compiler correspondence.
The caller supplies an installed assignment/goto block, fresh result local,
empty resource inventories, and a valid boundary; pending/ambient frames and
lexical contexts may be nonempty. Execution takes exactly two ticks in p. -/
namespace Jihoo.CommonLiteralBody
open CommonCompositionContract CommonDataTargetContext RecursiveLexicalFields

def block (slot n continuation : Nat) : ReferenceCfg.Block :=
  ⟨#[⟨⟨slot,false⟩, .use (.constant (.i64 n))⟩], .goto continuation⟩

def out (a : Boundary) (slot n continuation : Nat) : Boundary :=
  { a with target := { a.target with frame :=
      { a.target.frame with block := continuation, index := 0, locals := a.target.frame.locals.set! slot (some (.i64 n)) } } }

/-- Every other local, including untracked scratch locals, is unchanged. -/
theorem other_local (apart : other ≠ slot) :
    (out a slot n continuation).target.frame.locals[other]? = a.target.frame.locals[other]? := by
  simp only [out]
  unfold Array.set! Array.setIfInBounds
  split <;> simp [Ne.symm apart]

private theorem bindings_write (h : Bindings rs f ctx slots)
    (fresh : Fresh ctx slots dest) :
    Bindings rs { f with block := pc, index := 0, locals := f.locals.set! dest (some (.i64 n)) } ctx slots := by
  induction h with
  | nil => exact .nil
  | @cons e slot ctx slots head tail ih =>
    refine .cons ?_ (ih (fun k e slot he hs => fresh (k+1) e slot he hs))
    have apart : Active e → slot ≠ dest := fresh 0 e slot rfl rfl
    have keep : slot ≠ dest → ∀ v, Local f slot v → Local
        { f with block := pc, index := 0, locals := f.locals.set! dest (some (.i64 n)) } slot v := by
      intro ne v hv
      unfold Local at *
      simp only
      unfold Array.set! Array.setIfInBounds
      split <;> simpa [Ne.symm ne] using hv
    cases e with
    | data k => obtain ⟨i, hi, hv⟩ := head; exact ⟨i, hi, keep (apart trivial) _ hv⟩
    | buffer k => obtain ⟨x,j,hi,hv⟩ := head; exact ⟨x,j,hi,keep (apart trivial) _ hv⟩
    | nat k => exact keep (apart trivial) _ head
    | scalar => obtain ⟨v,hv⟩ := head; exact ⟨v,keep (apart trivial) _ hv⟩
    | ghost | dead => trivial

/-- Installation and bounds, rather than a run certificate, drive execution. -/
theorem run (a : Boundary) (fn : ReferenceCalls.Function)
    (installed : p[a.target.function]? = some fn)
    (code : fn.code.base.blocks[a.target.frame.block]? = some (block slot n continuation))
    (extension : (fn.code.exits[a.target.frame.block]?).join = none)
    (start : a.target.frame.index = 0)
    (ty : fn.code.base.locals[slot]? = some .i64)
    (space : slot < a.target.frame.locals.size)
    (next : continuation < fn.code.base.blocks.size)
    (signed : n < 2^63) (budget : a.target.stack.length ≤ limit) :
    CommonDataCaseRelocation.walk p 2 limit a.target =
      some ((out a slot n continuation).target, []) := by
  simp [CommonDataCaseRelocation.walk, ReferenceCalls.stackDepth,
    ReferenceCalls.tick, installed, ReferenceCalls.extension,
    ReferenceCfg.fetch, code, block, start, extension,
    ReferenceCfg.tick_eq_rawTick, ReferenceCfg.rawTick,
    ReferenceCfg.rvalue, ReferenceCfg.operand, ReferenceCfg.constant,
    BoundedMir.constant, BoundedMir.scalarBound, signed, ReferenceCfg.embedValue,
    ReferenceCfg.write, ty, ReferenceCfg.valueType, space,
    ReferenceCfg.advance, ReferenceCfg.jump, ReferenceCalls.liftLegacy,
    budget, Nat.not_lt.mpr budget, next, out]

theorem literal (a : Boundary) (fn : ReferenceCalls.Function)
    (shape : CommonDataSource.nodeAt g term = .core (.integer n))
    (signed : n < 2^63)
    (images : a.images = []) (buffers : a.buffers = []) (sizes : a.sizes = [])
    (valid : a.Valid) (fresh : Fresh a.ctx a.slots slot)
    (installed : p[a.target.function]? = some fn)
    (code : fn.code.base.blocks[a.target.frame.block]? = some (block slot n continuation))
    (extension : (fn.code.exits[a.target.frame.block]?).join = none)
    (start : a.target.frame.index = 0)
    (ty : fn.code.base.locals[slot]? = some .i64)
    (space : slot < a.target.frame.locals.size)
    (next : continuation < fn.code.base.blocks.size)
    (budget : a.target.stack.length ≤ limit) :
    BodyResult g term .scalar p limit 2 a (out a slot n continuation)
      (.scalar n) [] [] slot := by
  refine ⟨?_, .literal shape, ⟨run a fn installed code extension start ty space next signed budget,
    ?_, rfl, rfl, rfl⟩, ?_, ?_⟩
  · simpa [images, sizes] using (CommonDataSourceRules.Typing.literal (ctx := a.ctx) shape signed)
  · intro h
    exact ⟨{ h.toContext with bindings := bindings_write h.bindings fresh }, h.bufferSizes⟩
  · refine ⟨⟨n,rfl⟩, ?_⟩
    simpa [out, images, buffers, inventory, sources, footprint] using valid.owned
  · simp [out, Local, Array.set!, Array.setIfInBounds, space]
end Jihoo.CommonLiteralBody
