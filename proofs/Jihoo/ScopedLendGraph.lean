import Jihoo.ScopedLend

/-! Bounded constructor-graph recognition for the specified scalar Lend fragment.
The constructor view retains original node IDs. Unsupported nodes cannot be
projected; exporting/parsing this view is still a trusted implementation boundary.
Unlike a caller-built Reader, annotations, lexical roles, owner aliases and
one-cell index evidence are checked against the supplied original graph. -/
namespace Jihoo.ScopedLend.Graph
open HeapLeases

inductive Node where
  | opaque
  | var (index : Nat)
  | natural (value : Nat)
  | integer (value : Nat)
  | i64
  | buffer (length : Nat)
  | ref (type : Nat)
  | pi (erased : Bool) (type body : Nat)
  | lam (erased : Bool) (type body : Nat)
  | app (function argument : Nat)
  | index (array index proof : Nat)
  | decide (left right : Nat)
  | strict (first second : Nat)
  | borrow (owner : Nat)
  | lend (owner reader continuation : Nat)
  | free (owner rest : Nat)
  | store (owner index value proof : Nat)
  | ifLt (left right yes no : Nat)
  deriving DecidableEq, Repr

abbrev Graph := Array Node

def nodeAt (g : Graph) (id : Nat) : Node := g[id]?.getD .opaque

def Node.children : Node → List Nat
  | .opaque | .var _ | .natural _ | .integer _ | .i64 => []
  | .buffer a | .ref a | .borrow a => [a]
  | .pi _ a b | .lam _ a b | .app a b | .decide a b | .strict a b | .free a b => [a,b]
  | .index a b c | .lend a b c => [a,b,c]
  | .store a b c d | .ifLt a b c d => [a,b,c,d]

def valid (g : Graph) : Bool :=
  g.size ≤ 4096 && (List.range g.size).all fun id =>
    let n := nodeAt g id
    n.children.all (· < id) && match n with
      | .integer v => v < 2^63
      | .natural v => v < 2^64
      | .var k => k < 2^32
      | _ => true

def bufferOne (g : Graph) (ty : Nat) : Bool := match nodeAt g ty with
  | .buffer n => nodeAt g n == .natural 1
  | _ => false

def refOne (g : Graph) (ty : Nat) : Bool := match nodeAt g ty with
  | .ref t => bufferOne g t
  | _ => false

def boundZero (g : Graph) (i p : Nat) : Bool :=
  nodeAt g i == .natural 0 && match nodeAt g p with
    | .decide a b => nodeAt g a == .natural 0 && nodeAt g b == .natural 1
    | _ => false

inductive Role where
  | owner | borrow | scalar | ghost
  deriving DecidableEq, Repr

/-- Newest first. Entering an ignored scalar/erased branch binder shifts both
original owner and borrowed-reader slots; their roles do not change. -/
def borrowOperand (g : Graph) (ctx : List Role) (root : Nat) : Bool := match nodeAt g root with
  | .var k => ctx[k]? == some .borrow
  | .borrow x => match nodeAt g x with
      | .var k => ctx[k]? == some .owner
      | _ => false
  | _ => false

inductive Represents (g : Graph) : List Role → Nat → Reader → Prop where
  | scalar : nodeAt g root = .integer v → Represents g ctx root (.scalar v)
  | read : nodeAt g root = .index a i p → borrowOperand g ctx a = true → boundZero g i p = true →
      Represents g ctx root (.read 0)
  | strict : nodeAt g root = .strict a b → Represents g ctx a ra → Represents g ctx b rb →
      Represents g ctx root (.seq ra rb)
  | app : nodeAt g root = .app f a → nodeAt g f = .lam false ty body → nodeAt g ty = .i64 →
      Represents g ctx a ra → Represents g (.scalar :: ctx) body rb →
      Represents g ctx root (.seq ra rb)
  | branch (condition : Bool) : nodeAt g root = .ifLt a b yes no → nodeAt g a = .natural x → nodeAt g b = .natural y → condition = decide (x < y) →
      Represents g (.ghost :: ctx) yes ry → Represents g ctx no rn →
      Represents g ctx root (.branch condition ry rn)

/-- Fuel bounds nesting; the shared work budget bounds repeated DAG expansion.
There is no partial result after a failed child or unsupported annotation. -/
def project : Nat → Nat → Graph → List Role → Nat → Option (Reader × Nat)
  | 0, _, _, _, _ | _, 0, _, _, _ => none
  | fuel + 1, budget + 1, g, ctx, root => match nodeAt g root with
    | .integer v => some (.scalar v, budget)
    | .index a i p => if borrowOperand g ctx a && boundZero g i p then some (.read 0, budget) else none
    | .strict a b => do
        let (ra, remaining) ← project fuel budget g ctx a
        let (rb, remaining) ← project fuel remaining g ctx b
        pure (.seq ra rb, remaining)
    | .app f a => do
        let .lam false ty body := nodeAt g f | none
        if nodeAt g ty != .i64 then none else do
        let (ra, remaining) ← project fuel budget g ctx a
        let (rb, remaining) ← project fuel remaining g (.scalar :: ctx) body
        pure (.seq ra rb, remaining)
    | .ifLt a b yes no => do
        let .natural x := nodeAt g a | none
        let .natural y := nodeAt g b | none
        let (ry, remaining) ← project fuel budget g (.ghost :: ctx) yes
        let (rn, remaining) ← project fuel remaining g ctx no
        pure (.branch (x < y) ry rn, remaining)
    | _ => none

theorem project_sound (h : project fuel budget g ctx root = some (r, left)) :
    Represents g ctx root r := by
  induction fuel generalizing budget ctx root r left with
  | zero => simp [project] at h
  | succ fuel ih =>
    cases budget with
    | zero => simp [project] at h
    | succ budget =>
      cases node : nodeAt g root <;> simp only [project, node] at h
      all_goals try contradiction
      case integer v => cases h; exact .scalar node
      case index a i p =>
        split at h
        · next checks => cases h; exact .read node (Bool.and_eq_true_iff.mp checks).1 (Bool.and_eq_true_iff.mp checks).2
        · contradiction
      case strict a b =>
        cases ha : project fuel budget g ctx a <;> simp [ha] at h
        case some pair =>
          rcases pair with ⟨ra, remaining⟩
          cases hb : project fuel remaining g ctx b <;> simp [hb] at h
          case some pair =>
            rcases pair with ⟨rb, remaining'⟩
            rcases h with ⟨rfl, rfl⟩
            exact .strict node (ih ha) (ih hb)
      case app f a =>
        cases hf : nodeAt g f <;> simp [hf] at h
        case lam erased ty body =>
          cases erased <;> simp at h
          obtain ⟨ht', h⟩ := h
          cases ha : project fuel budget g ctx a <;> simp [ha] at h
          case some pair =>
            rcases pair with ⟨ra, remaining⟩
            cases hb : project fuel remaining g (.scalar :: ctx) body <;> simp [hb] at h
            case some pair =>
              rcases pair with ⟨rb, remaining'⟩
              rcases h with ⟨rfl, rfl⟩
              exact .app node hf ht' (ih ha) (ih hb)
      case ifLt a b yes no =>
        cases hx : nodeAt g a <;> simp [hx] at h
        case natural x =>
          cases hy : nodeAt g b <;> simp [hy] at h
          case natural y =>
            cases ha : project fuel budget g (.ghost :: ctx) yes <;> simp [ha] at h
            case some pair =>
              rcases pair with ⟨ra, remaining⟩
              cases hb : project fuel remaining g ctx no <;> simp [hb] at h
              case some pair =>
                rcases pair with ⟨rb, remaining'⟩
                rcases h with ⟨rfl, rfl⟩
                exact .branch _ node hx hy rfl (ih ha) (ih hb)

theorem Represents.scoped (h : Represents g ctx root r) : Scoped 1 r := by
  induction h with
  | scalar => exact .scalar
  | read => exact .read (by decide)
  | strict _ _ _ ia ib | app _ _ _ _ _ ia ib => exact .seq ia ib
  | branch _ _ _ _ _ _ _ ia ib => exact .branch ia ib

/-- Original constructor operational rules for this fragment. Slot roles are
lexical; runtime read observes the owner's payload through this active token. -/
inductive CoreReads (g : Graph) (s : State) (token owner : Nat) :
    List Role → Nat → Nat → List Event → Prop where
  | scalar : nodeAt g root = .integer v → CoreReads g s token owner ctx root v []
  | read : nodeAt g root = .index a i p → borrowOperand g ctx a = true → boundZero g i p = true →
      s.lease token = some owner →
      CoreReads g s token owner ctx root (s.payload owner) [.read token (s.payload owner)]
  | strict : nodeAt g root = .strict a b → CoreReads g s token owner ctx a v xs →
      CoreReads g s token owner ctx b w ys → CoreReads g s token owner ctx root w (xs ++ ys)
  | app : nodeAt g root = .app f a → nodeAt g f = .lam false ty body → nodeAt g ty = .i64 →
      CoreReads g s token owner ctx a v xs → CoreReads g s token owner (.scalar :: ctx) body w ys →
      CoreReads g s token owner ctx root w (xs ++ ys)
  | yes : nodeAt g root = .ifLt a b yes no → nodeAt g a = .natural x → nodeAt g b = .natural y → x < y →
      CoreReads g s token owner (.ghost :: ctx) yes v es → CoreReads g s token owner ctx root v es
  | no : nodeAt g root = .ifLt a b yes no → nodeAt g a = .natural x → nodeAt g b = .natural y → ¬ x < y →
      CoreReads g s token owner ctx no v es → CoreReads g s token owner ctx root v es

theorem Represents.execution (h : Represents g ctx root r)
    (active : s.lease token = some owner) (run : Reads s [token] r v es) :
    CoreReads g s token owner ctx root v es := by
  induction h generalizing v es with
  | scalar shape => cases run; exact .scalar shape
  | read shape role bound =>
    cases run with
    | read slot lease =>
      simp at slot
      subst_vars
      have eq := Option.some.inj (lease.symm.trans active)
      subst_vars
      exact .read shape role bound active
  | strict shape _ _ ia ib => cases run with
    | seq a b => exact .strict shape (ia a) (ib b)
  | app shape lam ty _ _ ia ib => cases run with
    | seq a b => exact .app shape lam ty (ia a) (ib b)
  | branch condition shape a b chosen _ _ ia ib =>
    cases run with
    | yes run => exact .yes shape a b (by simpa using chosen.symm) (ia run)
    | no run => exact .no shape a b (by simpa using chosen.symm) (ib run)

/-- Reflection ensures the new constructor semantics cannot choose an extra
unmodeled behavior for a graph that successfully projects. -/
theorem Represents.reflect (h : Represents g ctx root r)
    (run : CoreReads g s token owner ctx root v es) : Reads s [token] r v es := by
  induction h generalizing v es with
  | scalar shape =>
    cases run <;> simp_all
    exact .scalar
  | read shape role bound =>
    cases run <;> simp_all
    exact .read (k := 0) rfl (by assumption)
  | strict shape _ _ ia ib =>
    cases run <;> simp_all
    exact .seq (ia (by assumption)) (ib (by assumption))
  | app shape lam ty _ _ ia ib =>
    cases run <;> simp_all
    exact .seq (ia (by assumption)) (ib (by assumption))
  | branch condition shape a b chosen _ _ ia ib =>
    cases run <;> simp_all
    · exact .yes (ia (by assumption))
    · have cmp : condition = false := by
        rw [chosen]
        simp
        omega
      rw [← chosen, cmp]
      exact .no (ib (by assumption))

/-- Exact rooted lambda/Lend spine. No normalization or replacement of the
requested type is permitted. Reader and continuation roots come from these
edges, never unvalidated snapshot metadata. -/
def select (g : Graph) (root type : Nat) : Option (Nat × Nat) := do
  let .lam false input body := nodeAt g root | none
  if !bufferOne g input then none else do
  let .pi false domain result := nodeAt g type | none
  if !bufferOne g domain || nodeAt g result != .i64 then none else do
  let .lend owner reader continuation := nodeAt g body | none
  if nodeAt g owner != .var 0 then none else do
  let .lam false refType read := nodeAt g reader | none
  if !refOne g refType then none else do
  let .lam false resultType returned := nodeAt g continuation | none
  if nodeAt g resultType != .i64 then none else do
  let .lam false ownerType rest := nodeAt g returned | none
  if !bufferOne g ownerType then none else some (read, rest)

/-- Result is slot 1, returned owner slot 0, original owner slot 2. A store
must use the scalar result and literal index/evidence for the one-cell buffer. -/
def continuation (g : Graph) (root : Nat) : Option Continuation := do
  let .free owner result := nodeAt g root | none
  if nodeAt g result != .var 1 then none else
  match nodeAt g owner with
  | .var 0 => some .free
  | .var 2 => some .freeOriginal
  | .store owner i value proof =>
      if nodeAt g owner == .var 0 && nodeAt g value == .var 1 && boundZero g i proof
      then some .storeResult else none
  | _ => none

structure Accepted (g : Graph) (root type : Nat) where
  graph_valid : valid g = true
  root_bound : root < g.size
  type_bound : type < g.size
  readerRoot : Nat
  continuationRoot : Nat
  shape : select g root type = some (readerRoot, continuationRoot)
  reader : Reader
  selected : Represents g [.borrow, .owner] readerRoot reader
  next : Continuation
  continuation_shape : continuation g continuationRoot = some next

/-- A bounded proof-producing recognizer, not an executable-checker refinement.
All recursive reader expansion shares a 512-node work budget and depth 32. -/
def admit (g : Graph) (root type : Nat) : Option (Accepted g root type) :=
  if hv : valid g = true then
  if hr : root < g.size then
  if ht : type < g.size then
  match hs : select g root type with
  | none => none
  | some (read, rest) => match hp : project 32 512 g [.borrow, .owner] read with
    | none => none
    | some (r, _) => match hc : continuation g rest with
      | none => none
      | some k => some ⟨hv, hr, ht, read, rest, hs, r, project_sound hp, k, hc⟩
  else none else none else none

/-- Operational Lend rule over the retained constructor graph. Shape and
continuation checks select the original binders; the reader executes by
CoreReads, not by trusting a caller-provided heap event list. -/
inductive CoreRuns (g : Graph) (root type : Nat) (s : State) (owner : Nat) :
    Nat → List Event → State → Prop where
  | lend {readRoot rest : Nat} : select g root type = some (readRoot, rest) → continuation g rest = some k →
      CoreReads g (opened s owner) s.nextLease owner [.borrow, .owner] readRoot v events →
      CoreRuns g root type s owner v
        ([.beginLease s.nextLease owner] ++ events ++ [.close s.nextLease] ++ continuationEvents owner v k)
        (finalState s owner v k)

/-- The full specified-fragment endpoint: rooted original syntax supplies
scoping/aliases and a real constructor execution, primitive heap steps and
actual deallocation. Initial unique capabilities and native export fidelity
are not silently inferred from the no-preexisting-lease premise. -/
theorem accepted_execution (a : Accepted g root type) (valid : Valid s)
    (live : s.live owner = true) (unborrowed : Unborrowed s owner) :
    ∃ v events t, CoreRuns g root type s owner v events t ∧ Steps s events t ∧
      Valid t ∧ (released events).count owner = 1 ∧ t.live owner = false := by
  obtain ⟨v, events, t, source, steps⟩ := lend_total (k := a.next)
    valid live unborrowed a.selected.scoped
  cases source with
  | lend read =>
    have active : (opened s owner).lease s.nextLease = some owner := by simp [opened, put]
    refine ⟨v, _, _, .lend a.shape a.continuation_shape (a.selected.execution active read), steps, ?_⟩
    exact lend_owner_dead valid live unborrowed (.lend read)

/-- Every constructor execution of an accepted graph is reflected into the
previous scoped semantics, not only the witness constructed by totality. -/
theorem accepted_reflect (a : Accepted g root type)
    (run : CoreRuns g root type s owner v events t) :
    Executes s owner a.reader a.next v events t := by
  cases run with
  | lend shape cont reader =>
    have roots := Option.some.inj (a.shape.symm.trans shape)
    have r := Prod.mk.inj roots
    rcases r with ⟨hr, hc⟩
    subst_vars
    have k := Option.some.inj (a.continuation_shape.symm.trans cont)
    subst_vars
    exact .lend (a.selected.reflect reader)

theorem accepted_all_runs (a : Accepted g root type) (valid : Valid s)
    (live : s.live owner = true) (unborrowed : Unborrowed s owner)
    (run : CoreRuns g root type s owner v events t) :
    Steps s events t ∧ Valid t ∧ (released events).count owner = 1 ∧ t.live owner = false := by
  have source := accepted_reflect a run
  exact ⟨execution_steps valid live unborrowed source, lend_owner_dead valid live unborrowed source⟩

theorem accepted_token_expires (a : Accepted g root type) (valid : Valid s)
    (run : CoreRuns g root type s owner v events t) (later : Steps t tail u) :
    ¬ Step u (.read s.nextLease value) final :=
  execution_token_expires valid (accepted_reflect a run) later

end Jihoo.ScopedLend.Graph
