import Jihoo.SymbolicCommonDataContext

/-! Symbolic source typing for the fixed binary Tree, constant motive and
recursive uniform Buffer lifecycle fragment. Closing produces the established source rules
and their actual execution, without an execution premise. -/
namespace Jihoo.SymbolicCommonDataSource
open SymbolicCommonDataContext
open SymbolicCoreContext (Sizes SizesEval shiftSizes ListRel)
open CommonDataSourceRules (motiveKind)
open CommonDataSource (branchBody)

inductive Typing (g : CommonDataSource.Graph) :
    Context → Nat → Sizes → Nat → CommonData.Result → Prop where
  | literal : CommonDataSource.nodeAt g term = .core (.integer n) → n < 2^63 →
      Typing g ctx 0 [] term .scalar
  | empty : CommonDataSource.nodeAt g term = .con 0 0 [] → Typing g ctx 0 [] term .data
  | dataVar : CommonDataSource.nodeAt g term = .core (.var index) → ctx[index]? = some (.data 0) →
      Typing g ctx 1 [] term .data
  | construct : CommonDataSource.nodeAt g term = .con 0 1 [l,r] →
      CommonDataSource.nodeAt g l = .core (.var li) → ctx[li]? = some (.data 0) →
      CommonDataSource.nodeAt g r = .core (.var ri) → ctx[ri]? = some (.data 1) →
      Typing g ctx 2 [] term .data
  | bufferLet : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .core .i64 →
      SymbolicCoreTyping.Typing (CommonDataSourceExecution.sourceCore g) (project count ctx) sizes arg .scalar →
      Typing g (continuation count ctx) count [] body kind →
      Typing g ctx count sizes term kind
  | allocate : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .core (.buffer lengthTy) →
      SymbolicCoreTyping.BufferType (CommonDataSourceExecution.sourceCore g) (project count ctx) ty n →
      CommonDataSource.nodeAt g arg = .core (.alloc len init) →
      SymbolicCoreTyping.Index (CommonDataSourceExecution.sourceCore g) (project count ctx) len n →
      SymbolicCoreTyping.Scalar (CommonDataSourceExecution.sourceCore g) (project count ctx) init →
      Typing g (freshBuffer count ctx) count (shiftSizes (n :: sizes)) body kind →
      Typing g ctx count sizes term kind
  | freeBuffer : CommonDataSource.nodeAt g term = .core (.free owner body) →
      CommonDataSource.nodeAt g owner = .core (.var index) → ctx[index]? = some (.buffer (count+slot)) →
      slot < sizes.length →
      Typing g (consumeBuffer (count+slot) ctx) count (sizes.eraseIdx slot) body kind →
      Typing g ctx count sizes term kind
  | dataLet : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .ind 0 [] →
      Typing g ctx count sizes arg .data →
      Typing g (dataContinuation ctx) 1 [] body kind →
      Typing g ctx count sizes term kind
  | dataLetSplit : activeCount + retainedCount = count → usedSizes ++ savedSizes = sizes →
      CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .ind 0 [] →
      Typing g (argumentContext activeCount retainedCount usedSizes.length ctx)
        activeCount usedSizes arg .data →
      Typing g (capturedContext activeCount retainedCount usedSizes.length ctx)
        (retainedCount+1) (shiftSizes savedSizes) body kind →
      Typing g ctx count sizes term kind
  | drop : CommonDataSource.nodeAt g term = .drop 0 owner body →
      CommonDataSource.nodeAt g owner = .core (.var index) → ctx[index]? = some (.data 0) →
      Typing g (removeHead ctx) count sizes body kind →
      Typing g ctx (count+1) sizes term kind
  | caseTree : CommonDataSource.nodeAt g term = .caseOf 0 motive [nil,node] scrutinee →
      motiveKind g motive = some kind → branchBody g node = some body →
      CommonDataSource.nodeAt g scrutinee = .core (.var index) → ctx[index]? = some (.data 0) →
      Typing g (removeHead ctx) count sizes nil kind →
      Typing g (bindContext ctx) (count+2) (shiftSizes (shiftSizes sizes)) body kind →
      Typing g ctx (count+1) sizes term kind

private theorem sizes_split (h : SizesEval env (left ++ right) concrete) :
    ∃ ls rs, concrete = ls ++ rs ∧ SizesEval env left ls ∧ SizesEval env right rs := by
  induction left generalizing concrete with
  | nil => exact ⟨[], concrete, rfl, .nil, h⟩
  | cons a rest ih =>
    cases h with
    | cons head tail =>
      obtain ⟨ls,rs,rfl,hl,hr⟩ := ih tail
      exact ⟨_ :: ls,rs,rfl,.cons head hl,hr⟩

private theorem sizes_cons (h : SizesEval (naturalEnv closed) sizes concrete) :
    SizesEval (naturalEnv (entry :: closed)) (shiftSizes sizes) concrete :=
  h.rename (by intro k; rfl)

/-- Every suitable closing yields the old concrete source judgment. -/
theorem Typing.instantiate (typed : Typing g ctx count sizes term kind)
    (closing : Closes ctx closed)
    (inventory : SizesEval (naturalEnv closed) sizes concrete) :
    CommonDataSourceRules.Typing g closed count concrete term kind := by
  induction typed generalizing closed concrete with
  | literal shape bound => cases inventory; exact .literal shape bound
  | empty shape => cases inventory; exact .empty shape
  | dataVar shape lookup => cases inventory; exact .dataVar shape (data_lookup closing lookup)
  | construct shape left li right ri =>
    cases inventory
    exact .construct shape left (data_lookup closing li) right (data_lookup closing ri)
  | bufferLet shape fn ty arg body ih =>
    apply CommonDataSourceRules.Typing.bufferLet shape fn ty
    · simpa only [CommonDataSourceExecution.sourceCore_eq] using
        arg.instantiate (resultKind := .scalar) (projection closing)
          (inventory.congr (naturalEnv_skip closed).symm) trivial
    · exact ih closing.continuation .nil
  | allocate shape fn ty annotation alloc len init body ih =>
    obtain ⟨n,value,bound⟩ := len.total (projection closing)
    obtain ⟨indexRoot,domain,indexTyped⟩ := annotation
    apply CommonDataSourceRules.Typing.allocate shape fn ty
    · exact ⟨indexRoot,by simpa only [CommonDataSourceExecution.sourceCore_eq] using domain,
        ⟨_,by simpa only [CommonDataSourceExecution.sourceCore_eq] using indexTyped.represents,value⟩⟩
    · exact alloc
    · exact ⟨_,by simpa only [CommonDataSourceExecution.sourceCore_eq] using len.represents,value⟩
    · simpa only [CommonDataSourceExecution.sourceCore_eq] using init.instantiate (projection closing)
    · apply ih closing.freshBuffer
      apply sizes_cons
      apply SizesEval.congr _ (freshBufferEntry_env closed).symm
      exact .cons (by simpa only [naturalEnv_skip] using value) inventory
  | freeBuffer shape owner lookup bound body ih =>
    apply CommonDataSourceRules.Typing.freeBuffer shape owner (buffer_lookup closing lookup)
    · simpa only [inventory.length] using bound
    · apply ih closing.consumeBuffer
      exact (inventory.eraseIdx _).congr (consumeBufferEntry_env closed).symm
  | dataLet shape fn ty arg body ia ib =>
    exact .dataLet shape fn ty (ia closing inventory) (ib closing.dataContinuation .nil)
  | dataLetSplit counts sizes shape fn ty arg body ia ib =>
    subst sizes
    obtain ⟨used,saved,rfl,hu,hs⟩ := sizes_split inventory
    apply CommonDataSourceRules.Typing.dataLetSplit counts rfl shape fn ty
    · apply ia
      · simpa only [hu.length] using closing.argumentContext (a := _) (r := _) (b := _)
      · exact hu.congr (argumentEntry_env closed).symm
    · apply ib
      · simpa only [hu.length] using closing.capturedContext (a := _) (r := _) (b := _)
      · exact sizes_cons (hs.congr (capturedEntry_env closed).symm)
  | drop shape owner lookup body ih =>
    exact .drop shape owner (data_lookup closing lookup)
      (ih closing.removeHead (inventory.congr (removeEntry_env closed).symm))
  | caseTree shape motive branch scrutinee lookup nil node ihNil ihNode =>
    apply CommonDataSourceRules.Typing.caseTree shape motive branch scrutinee (data_lookup closing lookup)
    · exact ihNil closing.removeHead (inventory.congr (removeEntry_env closed).symm)
    · exact ihNode closing.bindContext (sizes_cons (sizes_cons (inventory.congr (retireEntry_env closed).symm)))

open CommonData RecursiveLexicalFields RecursiveFieldOwnership HeapLeases LinearHeapPrograms

/-- Produces an actual source execution, safe steps and exact resource accounting. -/
theorem Typing.total_accounted (typed : Typing g ctx count sizes term kind)
    (closing : Closes ctx closed) (inventory : SizesEval (naturalEnv closed) sizes concrete)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) closed env)
    (layout : SizedBufferContext.Layout s.buffers owners concrete) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) :
    ∃ v es t, CommonDataSourceExecution.Eval g env term s v es t ∧
      Steps s.buffers.heap es t.buffers.heap ∧ Valid t.buffers.heap ∧
      AccountedPost kind t v frame (footprint (caps trees owners)) es :=
  CommonDataSourceExecution.total_accounted (typed.instantiate closing inventory)
    length agreement layout valid owned fields

/-- The same safety and accounting hold for every execution of the source term. -/
theorem Typing.every_run_accounted (typed : Typing g ctx count sizes term kind)
    (closing : Closes ctx closed) (inventory : SizesEval (naturalEnv closed) sizes concrete)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) closed env)
    (layout : SizedBufferContext.Layout s.buffers owners concrete) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners))
    (run : CommonDataSourceExecution.Eval g env term s v es t) :
    Steps s.buffers.heap es t.buffers.heap ∧ Valid t.buffers.heap ∧
      AccountedPost kind t v frame (footprint (caps trees owners)) es := by
  obtain ⟨w,fs,u,canonical,steps,vt,post⟩ :=
    typed.total_accounted closing inventory length agreement layout valid owned fields
  obtain ⟨rfl,rfl,rfl⟩ := run.deterministic canonical
  exact ⟨steps,vt,post⟩

end Jihoo.SymbolicCommonDataSource
