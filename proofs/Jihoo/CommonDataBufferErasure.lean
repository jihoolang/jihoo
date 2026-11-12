import Jihoo.CommonDataErasure

/-! Independent extension of structural CommonData erasure. The existing shared typing
judgment supplies source totality without additional typing axioms. -/
namespace Jihoo.CommonDataBufferErasure
open RecursiveLexicalFields RecursiveFieldRuntime CommonDataSourceRules
open HeapLeases LinearHeapPrograms CommonDataErasure RecursiveBodyProjection

inductive Scalar where
  | literal (n : Nat)
  | var (slot : Nat)
  deriving Repr, DecidableEq

inductive ScalarLower (g : CommonDataSource.Graph) (slots : Slots) : Nat → Scalar → Prop where
  | literal : CommonDataSource.nodeAt g term = .core (.integer n) →
      ScalarLower g slots term (.literal n)
  | var : CommonDataSource.nodeAt g term = .core (.var k) → position slots k = some j →
      ScalarLower g slots term (.var j)

inductive ScalarEval (env : List Value) : Scalar → Nat → Prop where
  | literal : ScalarEval env (.literal n) n
  | var : (environment env)[j]? = some (.scalar n) → ScalarEval env (.var j) n

theorem core_shape (shape : CommonDataSource.nodeAt g term = .core node) :
    ScopedLend.Graph.nodeAt (CommonDataSourceExecution.sourceCore g) term = node := by
  cases found : g[term]? <;>
    simp_all [CommonDataSource.nodeAt, ScopedLend.Graph.nodeAt,
      CommonDataSourceExecution.sourceCore, CommonDataSourceExecution.coreNode,
      Array.getElem?_map]

theorem core_lookup (agreement : Env slots source compacted)
    (pos : position slots k = some j) :
    (environment compacted)[j]? = (environment source)[k]? := by
  simp only [environment, List.getElem?_map, agreement.lookup pos]

theorem ScalarLower.preserves (lower : ScalarLower g slots term a)
    (agreement : Env slots source compacted)
    (run : SizedCoreExecution.Scalar (CommonDataSourceExecution.sourceCore g)
      (environment source) term n) : ScalarEval compacted a n := by
  cases lower with
  | literal shape =>
    have h := core_shape shape
    cases run <;> simp_all
    exact .literal
  | var shape pos =>
    have h := core_shape shape
    cases run <;> simp_all
    exact .var ((core_lookup agreement pos).trans (by assumption))

theorem ScalarLower.run (lower : ScalarLower g slots term a)
    (agreement : Env slots source compacted)
    (run : SizedCoreExecution.Eval (CommonDataSourceExecution.sourceCore g)
      (environment source) term s (.scalar n) es t) :
    es = [] ∧ t = s ∧ ScalarEval compacted a n := by
  cases lower with
  | literal shape =>
    have h := core_shape shape
    cases run <;> simp_all
    · exact .literal
    all_goals rename_i lend rest; cases lend <;> simp_all
  | var shape pos =>
    have h := core_shape shape
    cases run <;> simp_all
    · exact .var ((core_lookup agreement pos).trans (by assumption))
    all_goals rename_i lend rest; cases lend <;> simp_all

theorem natural_value (shape : ScopedLend.Graph.nodeAt g term = .natural n)
    (run : DependentBufferIndices.Eval g env term m) : m = n := by
  obtain ⟨e, repr, value⟩ := run
  cases repr <;> simp_all [DependentBufferIndices.Expr.eval]

inductive Term where
  | literal (n : Nat)
  | empty
  | scalarLet (argument : Scalar) (body : Term)
  | allocate (length : Nat) (init : Scalar) (body : Term)
  | var (slot : Nat)
  | construct (left right : Nat)
  | letData (argument body : Term)
  | drop (owner : Nat) (body : Term)
  | freeBuffer (owner : Nat) (body : Term)
  | caseTree (scrutinee : Nat) (nil node : Term)
  deriving Repr, DecidableEq

/-- Structural lowering, including pure scalar atoms and direct constant-length allocation. -/
inductive Lower (g : CommonDataSource.Graph) : Slots → Nat → Term → Prop where
  | scalarLet : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .core .i64 →
      ScalarLower g slots arg a → Lower g (true :: slots) body b →
      Lower g slots term (.scalarLet a b)
  | allocate : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .core (.buffer annotation) →
      CommonDataSource.nodeAt g arg = .core (.alloc len init) →
      CommonDataSource.nodeAt g len = .core (.natural n) →
      ScalarLower g slots init a → Lower g (true :: slots) body b →
      Lower g slots term (.allocate n a b)
  | literal : CommonDataSource.nodeAt g term = .core (.integer n) → Lower g slots term (.literal n)
  | empty : CommonDataSource.nodeAt g term = .con 0 0 [] → Lower g slots term .empty
  | var : CommonDataSource.nodeAt g term = .core (.var k) → position slots k = some j →
      Lower g slots term (.var j)
  | construct : CommonDataSource.nodeAt g term = .con 0 1 [l,r] →
      CommonDataSource.nodeAt g l = .core (.var li) → position slots li = some lj →
      CommonDataSource.nodeAt g r = .core (.var ri) → position slots ri = some rj →
      Lower g slots term (.construct lj rj)
  | letData : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .ind 0 [] →
      Lower g slots arg a → Lower g (true :: slots) body b → Lower g slots term (.letData a b)
  | drop : CommonDataSource.nodeAt g term = .drop 0 owner body →
      CommonDataSource.nodeAt g owner = .core (.var k) → position slots k = some j →
      Lower g slots body b → Lower g slots term (.drop j b)
  | freeBuffer : CommonDataSource.nodeAt g term = .core (.free owner body) →
      CommonDataSource.nodeAt g owner = .core (.var k) → position slots k = some j →
      Lower g slots body b → Lower g slots term (.freeBuffer j b)
  | caseTree : CommonDataSource.nodeAt g term = .caseOf 0 motive [nil,node] scrutinee →
      motiveKind g motive = some kind → CommonDataSource.branchBody g node = some body →
      CommonDataSource.nodeAt g scrutinee = .core (.var k) → position slots k = some j →
      Lower g slots nil a → Lower g (true :: true :: slots) body b →
      Lower g slots term (.caseTree j a b)

/-- Target execution has no source graph, source environment, typing witness or
source execution premise. Heap operations and values remain the common model. -/
inductive Eval : List Value → Term → CommonData.State → Value → List Event → CommonData.State → Prop where
  | scalarLet : ScalarEval env a n → Eval (.scalar n :: env) b s result es t →
      Eval env (.scalarLet a b) s result es t
  | allocate : ScalarEval env a v →
      Eval (.buffer s.buffers.heap.nextObject :: env) b
        ⟨SizedBufferHeap.allocate s.buffers n v,s.cells⟩ result es t →
      Eval env (.allocate n a b) s result (.alloc s.buffers.heap.nextObject v :: es) t
  | literal : Eval env (.literal n) s (.scalar n) [] s
  | empty : Eval env .empty s (.data none) [] s
  | var : env[k]? = some (.data ref) → Eval env (.var k) s (.data ref) [] s
  | construct : env[l]? = some (.data left) → env[r]? = some (.data right) →
      Eval env (.construct l r) s (.data (some s.buffers.heap.nextObject))
        [.alloc s.buffers.heap.nextObject 0] (CommonData.allocate s left right)
  | letData : Eval env a s (.data ref) before middle →
      Eval (.data ref :: env) b middle result after t →
      Eval env (.letData a b) s result (before ++ after) t
  | drop : env[k]? = some (.data ref) → CommonData.Destroy ref s before middle →
      Eval env b middle result after t → Eval env (.drop k b) s result (before ++ after) t
  | freeBuffer : env[k]? = some (.buffer x) →
      Eval env b ⟨SizedBufferHeap.release s.buffers x,s.cells⟩ result es t →
      Eval env (.freeBuffer k b) s result (.free x :: es) t
  | emptyCase : env[k]? = some (.data none) → Eval env a s result es t →
      Eval env (.caseTree k a b) s result es t
  | nodeCase : enter s.recursive env k 0 = some (opened,parent) →
      Eval opened b s result es t →
      Eval env (.caseTree k a b) s result (es ++ [.free parent]) (CommonData.finish t parent)

/-- Preservation for every source run, including the exact trace and final store. -/
theorem Lower.preserves (lower : Lower g slots term target)
    (agreement : Env slots source compacted)
    (run : CommonDataSourceExecution.Eval g source term s v es t) :
    Eval compacted target s v es t := by
  induction lower generalizing source compacted s v es t with
  | scalarLet shape fn ty arg body ih =>
    cases run <;> simp_all
    obtain ⟨rfl, rfl, value⟩ := arg.run agreement (by assumption)
    simpa using Eval.scalarLet value (ih (.keep agreement) (by assumption))
  | allocate shape fn ty alloc len init body ih =>
    cases run <;> simp_all
    have ac := core_shape alloc
    rename_i coreRun rest
    cases coreRun <;> simp_all
    · have ln := natural_value (core_shape len) (by assumption)
      subst ln
      have value := init.preserves agreement (by assumption)
      simpa [SizedBufferHeap.Event.project] using Eval.allocate value
        (ih (.keep agreement) rest)
    all_goals rename_i lend nested; cases lend <;> simp_all
  | literal shape =>
    cases run <;> simp_all
    exact .literal
  | empty shape =>
    cases run <;> simp_all
    exact .empty
  | var shape pos =>
    cases run <;> simp_all
    exact .var ((agreement.lookup pos).trans (by assumption))
  | construct shape left lp right rp =>
    cases run <;> simp_all
    exact .construct ((agreement.lookup lp).trans (by assumption))
      ((agreement.lookup rp).trans (by assumption))
  | letData shape fn ty arg body ia ib =>
    cases run <;> simp_all
    exact .letData (ia agreement (by assumption)) (ib (.keep agreement) (by assumption))
  | drop shape owner pos body ih =>
    cases run <;> simp_all
    exact .drop ((agreement.lookup pos).trans (by assumption)) (by assumption)
      (ih agreement (by assumption))
  | freeBuffer shape owner pos body ih =>
    cases run <;> simp_all
    exact .freeBuffer ((agreement.lookup pos).trans (by assumption))
      (ih agreement (by assumption))
  | caseTree shape motive branch scrutinee pos nil node ia ib =>
    cases run <;> simp_all
    · exact .emptyCase ((agreement.lookup pos).trans (by assumption))
        (ia agreement (by assumption))
    · obtain ⟨opened, entered, related⟩ := agreement.enter pos (by assumption)
      exact .nodeCase entered (ib related (by assumption))

open CommonData RecursiveFieldOwnership

/-- Non-circular existence: source execution is obtained from source typing and
ownership; the caller supplies only a structural lowering certificate and slots. -/
theorem total_accounted
    (typed : CommonDataSourceRules.Typing g ctx count sizes term kind)
    (lower : Lower g slots term target) (compaction : Env slots source compacted)
    (length : trees.length = count) (agreement : Agrees (caps trees owners) ctx source)
    (layout : SizedBufferContext.Layout s.buffers owners sizes) (valid : Valid s.buffers.heap)
    (owned : Owns s.buffers.heap (footprint (caps trees owners) ++ frame))
    (fields : Fields s.cells (caps trees owners)) :
    ∃ v es t, Eval compacted target s v es t ∧ Steps s.buffers.heap es t.buffers.heap ∧
      Valid t.buffers.heap ∧ AccountedPost kind t v frame (footprint (caps trees owners)) es := by
  obtain ⟨v,es,t,run,steps,valid,post⟩ :=
    CommonDataSourceExecution.total_accounted typed length agreement layout valid owned fields
  exact ⟨v,es,t,lower.preserves compaction run,steps,valid,post⟩

end Jihoo.CommonDataBufferErasure
