import Jihoo.CommonDataSourceExecution

/-! Ghost compaction for the Data-structural fragment of the existing CommonData
source judgment. Target terms contain runtime indices, not source variable IDs.
The lowering certificate is structural and contains no execution premises. -/
namespace Jihoo.CommonDataErasure
open RecursiveLexicalFields RecursiveFieldRuntime CommonDataSourceRules
open HeapLeases LinearHeapPrograms

abbrev Slots := List Bool

def position : Slots → Nat → Option Nat
  | [], _ => none
  | false :: _, 0 => none
  | true :: _, 0 => some 0
  | false :: rest, k+1 => position rest k
  | true :: rest, k+1 => (position rest k).map Nat.succ

/-- Only actual ghost values may be omitted; dead ownership aliases are retained. -/
inductive Env : Slots → List Value → List Value → Prop where
  | nil : Env [] [] []
  | keep : Env slots source target → Env (true :: slots) (v :: source) (v :: target)
  | erase : Env slots source target → Env (false :: slots) (.ghost :: source) target

theorem Env.lookup (h : Env slots source target) (p : position slots k = some j) :
    target[j]? = source[k]? := by
  induction h generalizing k j with
  | nil => simp [position] at p
  | keep h ih =>
    cases k with
    | zero => simp [position] at p; subst j; rfl
    | succ k =>
      obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp p
      exact ih hi
  | erase h ih =>
    cases k with
    | zero => simp [position] at p
    | succ k => exact ih p

theorem position_injective (a : position slots k = some j)
    (b : position slots l = some j) : k = l := by
  induction slots generalizing k l j with
  | nil => simp [position] at a
  | cons bit rest ih =>
    cases bit <;> cases k <;> cases l <;> simp_all [position]
    · exact ih a b
    · obtain ⟨i, _, eq⟩ := b; omega
    · obtain ⟨i, _, eq⟩ := a; omega
    · obtain ⟨i, hi, rfl⟩ := a
      obtain ⟨i', hi', eq⟩ := b
      have same : i' = i := Nat.succ.inj eq
      subst i'
      exact ih hi hi'

/-- Case introduces right then left; Drop introduces no binder. -/
theorem Env.bind (h : Env slots source target) :
    Env (true :: true :: slots) (bindValues 0 cell source) (bindValues 0 cell target) :=
  .keep (.keep h)

theorem Env.enter (h : Env slots source target) (p : position slots k = some j)
    (entered : enter s source k 0 = some (opened,parent)) :
    ∃ compacted, enter s target j 0 = some (compacted,parent) ∧
      Env (true :: true :: slots) opened compacted := by
  have lookup := h.lookup p
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
            exact ⟨bindValues 0 cell target,
              by simp [RecursiveLexicalFields.enter, lookup, found, live, cellFound], h.bind⟩
        · simp [RecursiveLexicalFields.enter, found, live] at entered

inductive Term where
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
applications and explicit Buffer release are supported. All SizedCoreExecution
islands (both Buffer producers and scalar lets) are deliberately not admitted. -/
inductive Lower (g : CommonDataSource.Graph) : Slots → Nat → Term → Prop where
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

end Jihoo.CommonDataErasure
