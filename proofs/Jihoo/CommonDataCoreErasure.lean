import Jihoo.CommonDataBufferErasure
import Jihoo.SizedErasureForward
import Jihoo.CommonDataEnvironmentCompaction

/-! Shared compact Data target with full compact Core islands. The two masks
separate common lexical retention from the Core view, where Data is ghost. -/
namespace Jihoo.CommonDataCoreErasure
open RecursiveLexicalFields RecursiveFieldRuntime CommonDataSourceRules
open HeapLeases LinearHeapPrograms CommonDataErasure RecursiveBodyProjection

/-- Executable Core input projection; Data stays in the enclosing common runtime. -/
def coreEnv (env : List Value) : SizedErasure.Env :=
  (SizedErasure.compactEnv (environment env)).2

/-- Integration boundary for independent environment compaction laws.
No evaluation or lowering certificate occurs in this relation. -/
structure Bridge (slots : Slots) (mask : SizedErasure.Mask)
    (source compacted : List Value) : Prop where
  common : CommonDataErasure.Env slots source compacted
  core : SizedErasure.EnvRel mask (environment source) (coreEnv compacted)

/-- The independently proved compaction square discharges the Core bridge. -/
theorem Bridge.of_common (h : CommonDataErasure.Env slots source compacted) :
    Bridge slots (CommonDataEnvironmentCompaction.coreMask source) source compacted := by
  refine ⟨h, ?_⟩
  have related := CommonDataEnvironmentCompaction.core_related source
  rw [CommonDataEnvironmentCompaction.project_compact h] at related
  exact related

theorem Bridge.scalar (h : Bridge slots mask source compacted) :
    Bridge (true :: slots) (true :: mask) (.scalar n :: source) (.scalar n :: compacted) :=
  ⟨.keep h.common, .consKeep (.scalar n) h.core⟩

theorem Bridge.owner (h : Bridge slots mask source compacted) :
    Bridge (true :: slots) (true :: mask) (.buffer x :: source) (.buffer x :: compacted) :=
  ⟨.keep h.common, .consKeep (.owner x) h.core⟩

theorem Bridge.data (h : Bridge slots mask source compacted) :
    Bridge (true :: slots) (false :: mask) (.data ref :: source) (.data ref :: compacted) :=
  ⟨.keep h.common, .consGhost h.core⟩

theorem Bridge.enter (h : Bridge slots mask source compacted)
    (pos : position slots k = some j)
    (entered : enter s source k 0 = some (opened,parent)) :
    ∃ target, enter s compacted j 0 = some (target,parent) ∧
      Bridge (true :: true :: slots) (false :: false :: mask) opened target := by
  have lookup := h.common.lookup pos
  cases found : source[k]? with
  | none => simp [RecursiveLexicalFields.enter, found] at entered
  | some value =>
    cases value <;> try { simp [RecursiveLexicalFields.enter, found] at entered }
    case data ref =>
      cases ref with
      | none => simp [RecursiveLexicalFields.enter, found] at entered
      | some x =>
        by_cases live : s.heap.live x = true
        · cases cellFound : s.cells x with
          | none => simp [RecursiveLexicalFields.enter, found, live, cellFound] at entered
          | some cell =>
            simp [RecursiveLexicalFields.enter, found, live, cellFound] at entered
            rcases entered with ⟨rfl, rfl⟩
            exact ⟨bindValues 0 cell compacted,
              by simp [RecursiveLexicalFields.enter, lookup, found, live, cellFound], h.data.data⟩
        · simp [RecursiveLexicalFields.enter, found, live] at entered

inductive Term where
  | scalarLet (argument : SizedErasure.Term) (body : Term)
  | ownerLet (argument : SizedErasure.Term) (body : Term)
  | literal (n : Nat)
  | empty
  | var (slot : Nat)
  | construct (left right : Nat)
  | letData (argument body : Term)
  | drop (owner : Nat) (body : Term)
  | freeBuffer (owner : Nat) (body : Term)
  | caseTree (scrutinee : Nat) (nil node : Term)
  deriving Repr, DecidableEq

/-- Structural source-to-target lowering; arbitrary nested Case, Drop and Data
applications and explicit Buffer release are supported. Core islands reuse structural SizedErasure certificates. -/
inductive Lower (g : CommonDataSource.Graph) : Slots → SizedErasure.Mask → Nat → Term → Prop where
  | scalarLet : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .core .i64 →
      SizedErasure.Erases (CommonDataSourceExecution.sourceCore g) mask arg a →
      Lower g (true :: slots) (true :: mask) body b →
      Lower g slots mask term (.scalarLet a b)
  | ownerLet : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .core (.buffer annotation) →
      SizedErasure.Erases (CommonDataSourceExecution.sourceCore g) mask arg a →
      Lower g (true :: slots) (true :: mask) body b →
      Lower g slots mask term (.ownerLet a b)

  | literal : CommonDataSource.nodeAt g term = .core (.integer n) → Lower g slots mask term (.literal n)
  | empty : CommonDataSource.nodeAt g term = .con 0 0 [] → Lower g slots mask term .empty
  | var : CommonDataSource.nodeAt g term = .core (.var k) → position slots k = some j →
      Lower g slots mask term (.var j)
  | construct : CommonDataSource.nodeAt g term = .con 0 1 [l,r] →
      CommonDataSource.nodeAt g l = .core (.var li) → position slots li = some lj →
      CommonDataSource.nodeAt g r = .core (.var ri) → position slots ri = some rj →
      Lower g slots mask term (.construct lj rj)
  | letData : CommonDataSource.nodeAt g term = .core (.app fn arg) →
      CommonDataSource.nodeAt g fn = .core (.lam false ty body) →
      CommonDataSource.nodeAt g ty = .ind 0 [] →
      Lower g slots mask arg a → Lower g (true :: slots) (false :: mask) body b → Lower g slots mask term (.letData a b)
  | drop : CommonDataSource.nodeAt g term = .drop 0 owner body →
      CommonDataSource.nodeAt g owner = .core (.var k) → position slots k = some j →
      Lower g slots mask body b → Lower g slots mask term (.drop j b)
  | freeBuffer : CommonDataSource.nodeAt g term = .core (.free owner body) →
      CommonDataSource.nodeAt g owner = .core (.var k) → position slots k = some j →
      Lower g slots mask body b → Lower g slots mask term (.freeBuffer j b)
  | caseTree : CommonDataSource.nodeAt g term = .caseOf 0 motive [nil,node] scrutinee →
      motiveKind g motive = some kind → CommonDataSource.branchBody g node = some body →
      CommonDataSource.nodeAt g scrutinee = .core (.var k) → position slots k = some j →
      Lower g slots mask nil a → Lower g (true :: true :: slots) (false :: false :: mask) body b →
      Lower g slots mask term (.caseTree j a b)

/-- Target execution has no source graph, source environment, typing witness or
source execution premise. Heap operations and values remain the common model. -/
inductive Eval : List Value → Term → CommonData.State → Value → List Event → CommonData.State → Prop where
  | scalarLet : SizedErasure.Eval (coreEnv env) a s.buffers (.scalar n) before middle →
      Eval (.scalar n :: env) b ⟨middle,s.cells⟩ result after t →
      Eval env (.scalarLet a b) s result
        (before.map SizedBufferHeap.Event.project ++ after) t
  | ownerLet : SizedErasure.Eval (coreEnv env) a s.buffers (.owner x) before middle →
      Eval (.buffer x :: env) b ⟨middle,s.cells⟩ result after t →
      Eval env (.ownerLet a b) s result
        (before.map SizedBufferHeap.Event.project ++ after) t

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
theorem Lower.preserves (lower : Lower g slots mask term target)
    (agreement : Bridge slots mask source compacted)
    (run : CommonDataSourceExecution.Eval g source term s v es t) :
    Eval compacted target s v es t := by
  induction lower generalizing source compacted s v es t with
  | scalarLet shape fn ty arg body ih =>
    cases run <;> simp_all
    obtain ⟨v, equal, evaluated⟩ := arg.forward agreement.core (by assumption)
    cases v <;> simp_all [SizedErasure.Value.embed]
    exact .scalarLet evaluated (ih agreement.scalar (by assumption))
  | ownerLet shape fn ty arg body ih =>
    cases run <;> simp_all
    obtain ⟨v, equal, evaluated⟩ := arg.forward agreement.core (by assumption)
    cases v <;> simp_all [SizedErasure.Value.embed]
    exact .ownerLet evaluated (ih agreement.owner (by assumption))
  | literal shape =>
    cases run <;> simp_all
    exact .literal
  | empty shape =>
    cases run <;> simp_all
    exact .empty
  | var shape pos =>
    cases run <;> simp_all
    exact .var ((agreement.common.lookup pos).trans (by assumption))
  | construct shape left lp right rp =>
    cases run <;> simp_all
    exact .construct ((agreement.common.lookup lp).trans (by assumption))
      ((agreement.common.lookup rp).trans (by assumption))
  | letData shape fn ty arg body ia ib =>
    cases run <;> simp_all
    exact .letData (ia agreement (by assumption)) (ib agreement.data (by assumption))
  | drop shape owner pos body ih =>
    cases run <;> simp_all
    exact .drop ((agreement.common.lookup pos).trans (by assumption)) (by assumption)
      (ih agreement (by assumption))
  | freeBuffer shape owner pos body ih =>
    cases run <;> simp_all
    exact .freeBuffer ((agreement.common.lookup pos).trans (by assumption))
      (ih agreement (by assumption))
  | caseTree shape motive branch scrutinee pos nil node ia ib =>
    cases run <;> simp_all
    · exact .emptyCase ((agreement.common.lookup pos).trans (by assumption))
        (ia agreement (by assumption))
    · obtain ⟨opened, entered, related⟩ := agreement.enter pos (by assumption)
      exact .nodeCase entered (ib related (by assumption))


end Jihoo.CommonDataCoreErasure
