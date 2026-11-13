import Jihoo.CommonDataCaseEntryContext
import Jihoo.CommonDataCaseRelocation
import Jihoo.CommonDataSourceExecution
import Jihoo.TreeCreateContext

/-! Conditional interfaces only. No instance of EntryProvider
is postulated. All execution certificates refer to ONE installed Program. -/
namespace Jihoo.CommonCompositionContract
open CommonDataTargetContext CommonDataReference RecursiveLexicalFields
open RecursiveFieldRuntime RecursiveFieldOwnership

/-- A boundary names every resource, lexical value and complete machine state. -/
structure Boundary where
  images : List Image
  buffers : List (Nat × Nat)
  sizes : List Nat
  pending : List Pending
  sf : List Nat
  tf : List Nat
  ctx : List Entry
  env : List Value
  slots : List Nat
  source : CommonData.State
  target : ReferenceCalls.State

def Boundary.Valid (a : Boundary) : Prop :=
  CommonContext a.images a.buffers a.sizes a.pending a.sf a.tf
    a.ctx a.env a.slots a.source a.target.frame

/-- Transfer has exact ticks/events, preserves the suspended callers and both
ambient reservation lists. It cannot discharge a result/return ABI by itself. -/
structure Transfer (p : ReferenceCalls.Program) (limit ticks : Nat)
    (a b : Boundary) (events : List ReferenceCfg.Event) : Prop where
  run : CommonDataCaseRelocation.walk p ticks limit a.target = some (b.target, events)
  context : a.Valid → b.Valid
  callers : b.target.stack = a.target.stack
  sourceFrame : b.sf = a.sf
  targetFrame : b.tf = a.tf

theorem Transfer.then (ab : Transfer p limit n a b es)
    (bc : Transfer p limit m b c fs) : Transfer p limit (n+m) a c (es++fs) := by
  refine ⟨?_, fun h => bc.context (ab.context h),
    bc.callers.trans ab.callers, bc.sourceFrame.trans ab.sourceFrame,
    bc.targetFrame.trans ab.targetFrame⟩
  rw [CommonDataCaseRelocation.walk_add, ab.run]
  simp [bc.run]

theorem Transfer.steps (h : Transfer p limit n a b es) :
    ReferenceCalls.Steps p (.running a.target) es (.running b.target) :=
  (CommonDataCaseRelocation.walk_sound h.run).steps

/-- Exact Case input ABI. The copied-entry path is mandatory in this first
contract: src may be any slot, including zero if the reservation is satisfiable. -/
structure CaseInput where
  before : Boundary
  pre : Array ReferenceCfg.Block
  post : Array ReferenceCfg.Block
  nilBody : ReferenceCfg.Block
  nodeBody : ReferenceCfg.Block
  index : Nat
  src : Nat
  ghostSlots : List Nat
  selected : before.ctx[index]? = some (.data 0)
  slot : before.slots[index]? = some src
  pc : before.target = CommonDataCaseCfg.stateAt before.target.frame.heap
    before.target.frame.locals (pre.size+6) before.target.stack
  space : 7 ≤ before.target.frame.locals.size

def CaseInput.program (i : CaseInput) :=
  CommonDataCaseRelocation.linked i.pre i.post i.nilBody i.nodeBody i.src

def CaseInput.nodeOut (i : CaseInput) (x j : Nat) (l r : Image)
    (rest : List Image) : Boundary :=
  { i.before with
    images := l :: r :: rest
    pending := ⟨x,j,(Image.node x j l r).object⟩ :: i.before.pending
    ctx := bindContext i.ghostSlots.length i.before.ctx
    env := bindValues i.ghostSlots.length ⟨root l.source,root r.source⟩ i.before.env
    slots := 5 :: 4 :: (i.ghostSlots ++ i.before.slots)
    target := CommonDataCaseCfg.stateAt i.before.target.frame.heap
      (CommonDataCaseCfg.nodeLocals
        (i.before.target.frame.locals.set! 0 (some (.pointer j 0))) j l.target r.target)
      (i.pre.size+4) i.before.target.stack }

def CaseInput.nilOut (i : CaseInput) (j : Nat) (rest : List Image) : Boundary :=
  { i.before with
    images := rest
    ctx := CommonData.removeHead i.before.ctx
    target := CommonDataCaseCfg.stateAt
      (retired i.before.target.frame.heap j ReferenceHeap.nilObject)
      (CommonDataCaseCfg.nilLocals
        (i.before.target.frame.locals.set! 0 (some (.pointer j 0))))
      (i.pre.size+3) i.before.target.stack }

/-- A must provide these theorems, not merely an entry execution theorem.
The conservative reservation includes copied root slot zero. -/
structure EntryProvider : Prop where
  node : ∀ (i : CaseInput) x j l r rest limit,
    i.before.Valid → i.before.images = .node x j l r :: rest →
    CommonDataCaseEntryContext.Reserved i.before.ctx i.before.slots [0,1,2,3,4,5] →
    i.before.target.stack.length ≤ limit →
    CommonDataCaseCfg.sourceEnter i.before.source i.before.env i.index i.ghostSlots.length =
      some ((i.nodeOut x j l r rest).env, some x) ∧
    Transfer i.program limit 11 i.before (i.nodeOut x j l r rest) []
  nil : ∀ (i : CaseInput) j rest limit,
    i.before.Valid → i.before.images = .nil j :: rest →
    CommonDataCaseEntryContext.Reserved (CommonData.removeHead i.before.ctx)
      i.before.slots [0,1,6] → i.before.target.stack.length ≤ limit →
    CommonDataCaseCfg.sourceEnter i.before.source i.before.env i.index i.ghostSlots.length =
      some (i.before.env, none) ∧
    Transfer i.program limit 5 i.before (i.nilOut j rest) [.free j]

/-- B's body certificate includes genuine source Eval, result ownership and
an explicit result-local relation, not just execution of arbitrary blocks. -/
structure BodyResult (g : CommonDataSource.Graph) (term : Nat)
    (kind : CommonData.Result) (p : ReferenceCalls.Program) (limit ticks : Nat)
    (a b : Boundary) (v : Value) (sourceEvents : List HeapLeases.Event)
    (targetEvents : List ReferenceCfg.Event) (resultSlot : Nat) : Prop where
  typing : CommonDataSourceRules.Typing g a.ctx a.images.length a.sizes term kind
  sourceRun : CommonDataSourceExecution.Eval g a.env term a.source v sourceEvents b.source
  transfer : Transfer p limit ticks a b targetEvents
  post : CommonData.Post kind b.source v (b.pending.map Pending.source ++ b.sf)
  result : match v with
    | .scalar n => Local b.target.frame resultSlot (.i64 n)
    | .data ref => ∃ image ∈ b.images, root image.source = ref ∧
        Local b.target.frame resultSlot (.pointer image.target 0)
    | _ => False

/-- Finish removes exactly the pending head, changes source by finish, frees
exactly its target shell, and preserves result ownership. No source/target
trace equality is implied (boxed Nil and allocation bytes differ). -/
structure FinishResult (p : ReferenceCalls.Program) (limit ticks : Nat)
    (a b : Boundary) (shell : Pending) (tail : List Pending)
    (kind : CommonData.Result) (v : Value) (resultSlot : Nat) : Prop where
  resultLocal : b.target.frame.locals[resultSlot]? = a.target.frame.locals[resultSlot]?
  head : a.pending = shell :: tail
  pending : b.pending = tail
  source : b.source = CommonData.finish a.source shell.source
  images : b.images = a.images
  buffers : b.buffers = a.buffers
  sizes : b.sizes = a.sizes
  lexical : b.ctx = a.ctx ∧ b.env = a.env ∧ b.slots = a.slots
  transfer : Transfer p limit ticks a b [.free shell.target]
  post : CommonData.Post kind b.source v (tail.map Pending.source ++ b.sf)

/-- Integration is conditional on the actual body and finish certificates.
The seam b is definitionally identical in the two arguments. -/
theorem node_pipeline (entry : Transfer p limit 11 a b [])
    (body : BodyResult g term kind p limit n b c v se te slot)
    (finish : FinishResult p limit m c d shell tail kind v slot) :
    Transfer p limit (11+n+m) a d (te ++ [.free shell.target]) := by
  simpa using (entry.then body.transfer).then finish.transfer

/-- First source subset: signed literals, boxed Nil, head data variables,
Node of two variables, and constant-motive binary Case. No calls, drops,
Buffer effects, data-let, dependent motives or general Core expressions. -/
inductive Supported (g : CommonDataSource.Graph) : Nat → Prop where
  | literal : CommonDataSource.nodeAt g t = .core (.integer n) → n < 2^63 → Supported g t
  | empty : CommonDataSource.nodeAt g t = .con 0 0 [] → Supported g t
  | dataVar : CommonDataSource.nodeAt g t = .core (.var k) → Supported g t
  | construct : CommonDataSource.nodeAt g t = .con 0 1 [l,r] →
    CommonDataSource.nodeAt g l = .core (.var li) →
    CommonDataSource.nodeAt g r = .core (.var ri) → Supported g t
  | caseTree : CommonDataSource.nodeAt g t = .caseOf 0 motive [nil,node] scrutinee →
    CommonDataSourceRules.motiveKind g motive = some kind →
    CommonDataSource.branchBody g node = some body →
    CommonDataSource.nodeAt g scrutinee = .core (.var index) →
    nil < t → body < t → Supported g nil → Supported g body → Supported g t

/-- C's recursive calls are limited to strictly smaller graph IDs. P should be
an explicit placement-indexed body theorem; all leaf/Case laws remain arguments.
Typing must be supplied separately: Supported alone grants no ownership. -/
theorem supported_induction (g : CommonDataSource.Graph) (P : Nat → Prop)
    (step : ∀ t, Supported g t → (∀ child, child < t → Supported g child → P child) → P t)
    (supported : Supported g term) : P term := by
  induction term using Nat.strongRecOn with
  | ind t ih => exact step t supported (fun child smaller hs => ih child smaller hs)

end Jihoo.CommonCompositionContract
