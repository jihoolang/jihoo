import Jihoo.CommonDataSourceExecution
import Jihoo.SymbolicCoreClosing

/-! Value-independent mixed contexts. Data capability slots remain distinct
from Buffer slots; lexical positions are never compacted. Bound evidence is
introduced inside symbolic Buffer bodies, not fabricated by the projection. -/
namespace Jihoo.SymbolicCommonDataContext
open SymbolicCoreContext (ListRel Sizes SizesEval shiftSizes)
abbrev ClosedEntry := RecursiveLexicalFields.Entry
inductive Entry where
  | nat | scalar | buffer (slot : Nat) | data (slot : Nat) | ghost | dead
  deriving DecidableEq, Repr
abbrev Context := List Entry

def Entry.Closes : Entry → ClosedEntry → Prop
  | .nat, .nat n => n < 2^64
  | .scalar, .scalar | .ghost, .ghost | .dead, .dead => True
  | .buffer i, .buffer j | .data i, .data j => i = j
  | _, _ => False
abbrev Closes (ctx : Context) (closed : List ClosedEntry) := ListRel Entry.Closes ctx closed

def projectEntry (skip : Nat) : Entry → SymbolicCoreContext.Entry
  | .nat => .nat
  | .scalar => .scalar
  | .buffer k => if k < skip then .dead else .owner (k-skip)
  | _ => .dead

def project (skip : Nat) (ctx : Context) := ctx.map (projectEntry skip)
def naturalEnv (closed : List ClosedEntry) :=
  SizedBufferContext.naturalEnv (RecursiveBodyProjection.context 0 closed)

theorem project_entry (h : Entry.Closes e c) :
    SymbolicCoreContext.Entry.Closes env (projectEntry skip e) (RecursiveBodyProjection.entry skip c) := by
  cases e <;> cases c <;>
    simp_all [Entry.Closes, projectEntry, RecursiveBodyProjection.entry, SymbolicCoreContext.Entry.Closes]
  rename_i i j
  subst j
  by_cases h : i < skip <;> simp [h]

theorem projection (h : Closes ctx closed) :
    SymbolicCoreContext.Closes (project skip ctx) (RecursiveBodyProjection.context skip closed) := by
  unfold SymbolicCoreContext.Closes project RecursiveBodyProjection.context
  generalize SizedBufferContext.naturalEnv (closed.map (RecursiveBodyProjection.entry skip)) = env
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (project_entry hab) ih

theorem naturalEnv_skip (closed : List ClosedEntry) :
    SizedBufferContext.naturalEnv (RecursiveBodyProjection.context skip closed) = naturalEnv closed := by
  funext k
  simp only [naturalEnv, SizedBufferContext.naturalEnv, RecursiveBodyProjection.context, List.getElem?_map]
  cases h : closed[k]? with
  | none => rfl
  | some e =>
    cases e <;> simp [RecursiveBodyProjection.entry]
    rename_i slot
    by_cases h : slot < skip <;> simp [h]

theorem data_lookup {k : Nat} {ctx : Context} {closed : List ClosedEntry} (h : Closes ctx closed) (found : ctx[k]? = some (Entry.data slot)) :
    closed[k]? = some (RecursiveLexicalFields.Entry.data slot) := by
  obtain ⟨e, lookup, rel⟩ := h.lookup found
  cases e <;> simp_all [Entry.Closes]

theorem buffer_lookup {k : Nat} {ctx : Context} {closed : List ClosedEntry}
    (h : Closes ctx closed) (found : ctx[k]? = some (Entry.buffer slot)) :
    closed[k]? = some (RecursiveLexicalFields.Entry.buffer slot) := by
  obtain ⟨e, lookup, rel⟩ := h.lookup found
  cases e <;> simp_all [Entry.Closes]

def freshBufferEntry : Entry → Entry
  | .buffer k => .buffer (k+1)
  | e => e

def consumeBufferEntry (slot : Nat) : Entry → Entry
  | .buffer k => if k = slot then .dead else .buffer (if slot < k then k-1 else k)
  | e => e

def freshBuffer (count : Nat) (ctx : Context) := Entry.buffer count :: ctx.map freshBufferEntry
def consumeBuffer (slot : Nat) (ctx : Context) := ctx.map (consumeBufferEntry slot)

theorem freshBufferEntry_closes (h : Entry.Closes e c) :
    Entry.Closes (freshBufferEntry e) (CommonData.freshBufferEntry c) := by
  cases e <;> cases c <;> simp_all [Entry.Closes, freshBufferEntry, CommonData.freshBufferEntry]

theorem consumeBufferEntry_closes (h : Entry.Closes e c) :
    Entry.Closes (consumeBufferEntry slot e) (CommonData.consumeBufferEntry slot c) := by
  cases e <;> cases c <;> simp_all [Entry.Closes, consumeBufferEntry, CommonData.consumeBufferEntry]
  rename_i k
  by_cases eq : k = slot <;> simp [eq]

theorem freshBufferEntry_env (closed : List ClosedEntry) :
    naturalEnv (closed.map CommonData.freshBufferEntry) = naturalEnv closed := by
  funext k
  simp only [naturalEnv,SizedBufferContext.naturalEnv,RecursiveBodyProjection.context,
    List.getElem?_map,Option.map_map]
  cases h : closed[k]? with
  | none => rfl
  | some e => cases e <;> simp [CommonData.freshBufferEntry,RecursiveBodyProjection.entry]

theorem consumeBufferEntry_env (closed : List ClosedEntry) :
    naturalEnv (closed.map (CommonData.consumeBufferEntry slot)) = naturalEnv closed := by
  funext k
  simp only [naturalEnv,SizedBufferContext.naturalEnv,RecursiveBodyProjection.context,
    List.getElem?_map,Option.map_map]
  cases h : closed[k]? with
  | none => rfl
  | some e =>
    cases e <;> simp [CommonData.consumeBufferEntry,RecursiveBodyProjection.entry]
    rename_i k
    by_cases eq : k = slot <;> simp [eq]

theorem Closes.freshBuffer (h : Closes ctx closed) :
    Closes (freshBuffer count ctx) (CommonData.freshBuffer count closed) :=
  .cons rfl (ListRel.map h (by intro a b hab; exact freshBufferEntry_closes hab))

theorem Closes.consumeBuffer (h : Closes ctx closed) :
    Closes (consumeBuffer slot ctx) (CommonData.consumeBuffer slot closed) :=
  ListRel.map h (by intro a b hab; exact consumeBufferEntry_closes hab)

def bufferCallEntry (count p : Nat) : Entry → Entry
  | .buffer k => if count+p ≤ k then .buffer (k-p+1) else .dead
  | e => e

def bufferCall (count p : Nat) (ctx : Context) :=
  Entry.buffer count :: ctx.map (bufferCallEntry count p)

theorem bufferCallEntry_closes (h : Entry.Closes e c) :
    Entry.Closes (bufferCallEntry count p e) (CommonData.bufferCallEntry count p c) := by
  cases e <;> cases c <;> simp_all [Entry.Closes, bufferCallEntry, CommonData.bufferCallEntry]
  rename_i k
  by_cases bound : count+p ≤ k <;> simp [bound]

theorem bufferCallEntry_env (closed : List ClosedEntry) :
    naturalEnv (closed.map (CommonData.bufferCallEntry count p)) = naturalEnv closed := by
  funext k
  simp only [naturalEnv,SizedBufferContext.naturalEnv,RecursiveBodyProjection.context,
    List.getElem?_map,Option.map_map]
  cases h : closed[k]? with
  | none => rfl
  | some e =>
    cases e <;> simp [CommonData.bufferCallEntry,RecursiveBodyProjection.entry]
    rename_i k
    by_cases bound : count+p ≤ k <;> simp [bound]

theorem Closes.bufferCall (h : Closes ctx closed) :
    Closes (bufferCall count p ctx) (CommonData.bufferCall count p closed) :=
  .cons rfl (ListRel.map h (by intro a b hab; exact bufferCallEntry_closes hab))

def removeEntry : Entry → Entry
  | .data 0 | .buffer 0 => .dead
  | .data (k+1) => .data k
  | .buffer (k+1) => .buffer k
  | other => other

theorem removeEntry_closes (h : Entry.Closes e c) :
    Entry.Closes (removeEntry  e) (CommonData.removeEntry  c) := by
  cases e <;> cases c <;> simp_all [Entry.Closes, removeEntry, CommonData.removeEntry]
  all_goals rename_i slot; cases slot <;> trivial

theorem removeEntry_env (closed : List ClosedEntry) :
    naturalEnv (closed.map (CommonData.removeEntry )) = naturalEnv closed := by
  funext k
  simp only [naturalEnv, SizedBufferContext.naturalEnv, RecursiveBodyProjection.context,
    List.getElem?_map, Option.map_map]
  cases h : closed[k]? with
  | none => rfl
  | some e =>
    cases e <;> simp [CommonData.removeEntry, RecursiveBodyProjection.entry]
    all_goals rename_i slot; cases slot <;> trivial

def retireAll : Entry → Entry
  | .data _ | .buffer _ => .dead
  | other => other

theorem retireAll_closes (h : Entry.Closes e c) :
    Entry.Closes (retireAll  e) (CommonData.retireAll  c) := by
  cases e <;> cases c <;> simp_all [Entry.Closes, retireAll, CommonData.retireAll]
  all_goals rename_i slot; cases slot <;> trivial

theorem retireAll_env (closed : List ClosedEntry) :
    naturalEnv (closed.map (CommonData.retireAll )) = naturalEnv closed := by
  funext k
  simp only [naturalEnv, SizedBufferContext.naturalEnv, RecursiveBodyProjection.context,
    List.getElem?_map, Option.map_map]
  cases h : closed[k]? with
  | none => rfl
  | some e =>
    cases e <;> simp [CommonData.retireAll, RecursiveBodyProjection.entry]
    all_goals rename_i slot; cases slot <;> trivial

def argumentEntry (dataCount retainedCount bufferCount : Nat) : Entry → Entry
  | .data k => if k < dataCount then .data k else .dead
  | .buffer k => if dataCount + retainedCount ≤ k ∧ k < dataCount + retainedCount + bufferCount
      then .buffer (k - retainedCount) else .dead
  | e => e

theorem argumentEntry_closes (h : Entry.Closes e c) :
    Entry.Closes (argumentEntry a r b e) (CommonData.argumentEntry a r b c) := by
  cases e <;> cases c <;> simp_all [Entry.Closes, argumentEntry, CommonData.argumentEntry]
  · rename_i slot
    by_cases h : a+r ≤ slot ∧ slot < a+r+b <;> simp [h]
  · rename_i slot
    by_cases h : slot < a <;> simp [h]

theorem argumentEntry_env (closed : List ClosedEntry) :
    naturalEnv (closed.map (CommonData.argumentEntry a r b)) = naturalEnv closed := by
  funext k
  simp only [naturalEnv, SizedBufferContext.naturalEnv, RecursiveBodyProjection.context,
    List.getElem?_map, Option.map_map]
  cases h : closed[k]? with
  | none => rfl
  | some e =>
    cases e <;> simp [CommonData.argumentEntry, RecursiveBodyProjection.entry]
    · rename_i slot
      by_cases h : a+r ≤ slot ∧ slot < a+r+b <;> simp [h]
    · rename_i slot
      by_cases h : slot < a <;> simp [h]

def capturedEntry (dataCount retainedCount bufferCount : Nat) : Entry → Entry
  | .data k => if dataCount ≤ k ∧ k < dataCount + retainedCount
      then .data (1 + (k - dataCount)) else .dead
  | .buffer k => if dataCount + retainedCount + bufferCount ≤ k
      then .buffer (1 + retainedCount + (k - (dataCount + retainedCount + bufferCount))) else .dead
  | e => e

theorem capturedEntry_closes (h : Entry.Closes e c) :
    Entry.Closes (capturedEntry a r b e) (CommonData.capturedEntry a r b c) := by
  cases e <;> cases c <;> simp_all [Entry.Closes, capturedEntry, CommonData.capturedEntry]
  · rename_i slot
    by_cases h : a+r+b ≤ slot <;> simp [h]
  · rename_i slot
    by_cases h : a ≤ slot ∧ slot < a+r <;> simp [h]

theorem capturedEntry_env (closed : List ClosedEntry) :
    naturalEnv (closed.map (CommonData.capturedEntry a r b)) = naturalEnv closed := by
  funext k
  simp only [naturalEnv, SizedBufferContext.naturalEnv, RecursiveBodyProjection.context,
    List.getElem?_map, Option.map_map]
  cases h : closed[k]? with
  | none => rfl
  | some e =>
    cases e <;> simp [CommonData.capturedEntry, RecursiveBodyProjection.entry]
    · rename_i slot
      by_cases h : a+r+b ≤ slot <;> simp [h]
    · rename_i slot
      by_cases h : a ≤ slot ∧ slot < a+r <;> simp [h]

def retainedEntry (count : Nat) : Entry → Entry
  | .buffer _ => .dead
  | .data k => if k < count then .data k else .dead
  | other => other

theorem retainedEntry_closes (h : Entry.Closes e c) :
    Entry.Closes (retainedEntry count e) (RecursiveBodyProjection.retainedEntry count c) := by
  cases e <;> cases c <;> simp_all [Entry.Closes, retainedEntry, RecursiveBodyProjection.retainedEntry]
  · rename_i slot
    by_cases h : slot < count <;> simp [h]

theorem retainedEntry_env (closed : List ClosedEntry) :
    naturalEnv (closed.map (RecursiveBodyProjection.retainedEntry count)) = naturalEnv closed := by
  funext k
  simp only [naturalEnv, SizedBufferContext.naturalEnv, RecursiveBodyProjection.context,
    List.getElem?_map, Option.map_map]
  cases h : closed[k]? with
  | none => rfl
  | some e =>
    cases e <;> simp [RecursiveBodyProjection.retainedEntry, RecursiveBodyProjection.entry]
    · rename_i slot
      by_cases h : slot < count <;> simp [h]

def retireEntry : Entry → Entry
  | .buffer 0 | .data 0 => .dead
  | .buffer (k+1) => .buffer (k+2)
  | .data (k+1) => .data (k+2)
  | other => other

theorem retireEntry_closes (h : Entry.Closes e c) :
    Entry.Closes (retireEntry  e) (RecursiveLexicalFields.retireEntry  c) := by
  cases e <;> cases c <;> simp_all [Entry.Closes, retireEntry, RecursiveLexicalFields.retireEntry]
  all_goals rename_i slot; cases slot <;> trivial

theorem retireEntry_env (closed : List ClosedEntry) :
    naturalEnv (closed.map (RecursiveLexicalFields.retireEntry )) = naturalEnv closed := by
  funext k
  simp only [naturalEnv, SizedBufferContext.naturalEnv, RecursiveBodyProjection.context,
    List.getElem?_map, Option.map_map]
  cases h : closed[k]? with
  | none => rfl
  | some e =>
    cases e <;> simp [RecursiveLexicalFields.retireEntry, RecursiveBodyProjection.entry]
    all_goals rename_i slot; cases slot <;> trivial

def removeHead (ctx : Context) := ctx.map removeEntry
def dataContinuation (ctx : Context) := Entry.data 0 :: ctx.map retireAll
def argumentContext (a r b : Nat) (ctx : Context) := ctx.map (argumentEntry a r b)
def capturedContext (a r b : Nat) (ctx : Context) := Entry.data 0 :: ctx.map (capturedEntry a r b)
def continuation (count : Nat) (ctx : Context) := Entry.scalar :: ctx.map (retainedEntry count)
def bindContext (ctx : Context) := Entry.data 1 :: Entry.data 0 :: ctx.map retireEntry

theorem Closes.removeHead (h : Closes ctx closed) :
    Closes (removeHead  ctx) (CommonData.removeHead  closed) := by
  exact ListRel.map h (by intro a b hab; exact removeEntry_closes hab)

theorem Closes.dataContinuation (h : Closes ctx closed) :
    Closes (dataContinuation  ctx) (CommonData.dataContinuation  closed) := by
  exact .cons rfl (ListRel.map h (by intro a b hab; exact retireAll_closes hab))

theorem Closes.argumentContext (h : Closes ctx closed) :
    Closes (argumentContext a r b ctx) (CommonData.argumentContext a r b closed) := by
  exact ListRel.map h (by intro a b hab; exact argumentEntry_closes hab)

theorem Closes.capturedContext (h : Closes ctx closed) :
    Closes (capturedContext a r b ctx) (CommonData.capturedContext a r b closed) := by
  exact .cons rfl (ListRel.map h (by intro a b hab; exact capturedEntry_closes hab))

theorem Closes.continuation (h : Closes ctx closed) :
    Closes (continuation count ctx) (RecursiveBodyProjection.continuation count closed) := by
  exact .cons (by trivial) (ListRel.map h (by intro a b hab; exact retainedEntry_closes hab))

theorem Closes.bindContext (h : Closes ctx closed) :
    Closes (bindContext  ctx) (RecursiveLexicalFields.bindContext 0 closed) := by
  exact .cons rfl (.cons rfl (ListRel.map h (by intro a b hab; exact retireEntry_closes hab)))

end Jihoo.SymbolicCommonDataContext
