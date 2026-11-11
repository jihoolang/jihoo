import Jihoo.SizedErasureContext
import Jihoo.SizedOwnedLend

/-! Independent compact runtime for sized-buffer programs. Its syntax contains
only runtime operands, and its environments contain no proof placeholders.
Neither evaluation nor its determinism theorem refers to a source graph,
typing derivation, annotation, or proof witness. -/
namespace Jihoo.SizedErasure

/-- Natural operands retain lexical binding but have no source node identities. -/
inductive NatTerm where
  | literal (value : Nat)
  | var (slot : Nat)
  | letE (argument body : NatTerm)
  deriving DecidableEq, Repr

inductive NatEval : Env → NatTerm → Nat → Prop where
  | literal : NatEval env (.literal n) n
  | var : env[k]? = some (.nat n) → NatEval env (.var k) n
  | letE : NatEval env argument n → NatEval (.nat n :: env) body result →
      NatEval env (.letE argument body) result

inductive ScalarTerm where
  | literal (value : Nat)
  | var (slot : Nat)
  deriving DecidableEq, Repr

inductive ScalarEval : Env → ScalarTerm → Nat → Prop where
  | literal : ScalarEval env (.literal v) v
  | var : env[k]? = some (.scalar v) → ScalarEval env (.var k) v

/-- The true comparison arm has no extra binder. Application, natural lets,
and lender continuations retain only their computational binders. -/
inductive Term where
  | scalar (value : Nat)
  | natural (value : Nat)
  | var (slot : Nat)
  | app (argument body : Term)
  | allocate (length : NatTerm) (fill : ScalarTerm)
  | free (ownerSlot : Nat) (body : Term)
  | ifLt (left right : NatTerm) (yes no : Term)
  | lend (ownerSlot : Nat) (index : NatTerm) (body : Term)
  | ownedLend (ownerSlot : Nat) (length index : NatTerm) (body : Term)
  deriving DecidableEq, Repr

/-- Target execution is defined directly over the compact syntax. In
particular, comparison tests add no environment entry at runtime. -/
inductive Eval : Env → Term → SizedBufferHeap.State → Value →
    List SizedBufferHeap.Event → SizedBufferHeap.State → Prop where
  | scalar : Eval env (.scalar v) s (.scalar v) [] s
  | natural : Eval env (.natural n) s (.nat n) [] s
  | var : env[k]? = some value → Eval env (.var k) s value [] s
  | app : Eval env argument s computed before middle →
      Eval (computed :: env) body middle value after t →
      Eval env (.app argument body) s value (before ++ after) t
  | allocate : NatEval env length n → ScalarEval env fill v →
      Eval env (.allocate length fill) s (.owner s.heap.nextObject)
        [.alloc s.heap.nextObject n v] (SizedBufferHeap.allocate s n v)
  | free : env[k]? = some (.owner x) →
      Eval env body (SizedBufferHeap.release s x) value events t →
      Eval env (.free k body) s value (.free x :: events) t
  | yes : NatEval env left a → NatEval env right b → a < b →
      Eval env yes s value events t →
      Eval env (.ifLt left right yes no) s value events t
  | no : NatEval env left a → NatEval env right b → ¬ a < b →
      Eval env no s value events t →
      Eval env (.ifLt left right yes no) s value events t
  | lend : env[k]? = some (.owner x) →
      NatEval (.borrow x :: env) index i →
      Eval (.owner x :: .scalar (s.heap.payload x) :: env) body
        ⟨ScopedLend.restored s.heap, s.length⟩ value suffix t →
      Eval env (.lend k index body) s value
        ([.beginLease s.heap.nextLease x, .read s.heap.nextLease i (s.heap.payload x),
          .close s.heap.nextLease] ++ suffix) t
  | ownedLend : env[k]? = some (.owner x) →
      NatEval (.borrow x :: env) index i →
      NatEval (.borrow x :: env) length m →
      Eval (.owner x :: .owner s.heap.nextObject :: env) body
        (SizedOwnedLend.final s m (s.heap.payload x)) value suffix t →
      Eval env (.ownedLend k length index body) s value
        (SizedOwnedLend.events s x i m ++ suffix) t

theorem NatEval.deterministic (a : NatEval env term n) (b : NatEval env term m) : n = m := by
  induction a generalizing m with
  | literal => cases b; rfl
  | var lookup =>
      cases b with
      | var lookup' =>
          have eq := lookup.symm.trans lookup'
          cases eq
          rfl
  | letE first second ihf ihs =>
      cases b with
      | letE first' second' =>
          obtain rfl := ihf first'
          exact ihs second'

theorem ScalarEval.deterministic
    (a : ScalarEval env term v) (b : ScalarEval env term w) : v = w := by
  cases a with
  | literal => cases b; rfl
  | var lookup =>
      cases b with
      | var lookup' =>
          have eq := lookup.symm.trans lookup'
          cases eq
          rfl

/-- A fixed compact program, runtime environment, and initial heap determine
its value, complete event trace, and final heap. -/
theorem Eval.deterministic (a : Eval env term s v es t)
    (b : Eval env term s v' es' t') : v = v' ∧ es = es' ∧ t = t' := by
  induction a generalizing v' es' t' with
  | scalar => cases b; exact ⟨rfl, rfl, rfl⟩
  | natural => cases b; exact ⟨rfl, rfl, rfl⟩
  | var lookup =>
      cases b with
      | var lookup' =>
          have eq := lookup.symm.trans lookup'
          cases eq
          exact ⟨rfl, rfl, rfl⟩
  | app first second ihf ihs =>
      cases b with
      | app first' second' =>
          obtain ⟨rfl, rfl, rfl⟩ := ihf first'
          obtain ⟨rfl, rfl, rfl⟩ := ihs second'
          exact ⟨rfl, rfl, rfl⟩
  | allocate length fill =>
      cases b with
      | allocate length' fill' =>
          obtain rfl := length.deterministic length'
          obtain rfl := fill.deterministic fill'
          exact ⟨rfl, rfl, rfl⟩
  | free lookup suffix ih =>
      cases b with
      | free lookup' suffix' =>
          have eq := lookup.symm.trans lookup'
          cases eq
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩
  | yes left right bound suffix ih =>
      cases b with
      | yes left' right' bound' suffix' => exact ih suffix'
      | no left' right' bound' suffix' =>
          obtain rfl := left.deterministic left'
          obtain rfl := right.deterministic right'
          contradiction
  | no left right bound suffix ih =>
      cases b with
      | yes left' right' bound' suffix' =>
          obtain rfl := left.deterministic left'
          obtain rfl := right.deterministic right'
          contradiction
      | no left' right' bound' suffix' => exact ih suffix'
  | lend lookup index suffix ih =>
      cases b with
      | lend lookup' index' suffix' =>
          have eq := lookup.symm.trans lookup'
          cases eq
          obtain rfl := index.deterministic index'
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩
  | ownedLend lookup index length suffix ih =>
      cases b with
      | ownedLend lookup' index' length' suffix' =>
          have eq := lookup.symm.trans lookup'
          cases eq
          obtain rfl := index.deterministic index'
          obtain rfl := length.deterministic length'
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩

/-- Every target execution restores the incoming lease map, independently of
typing, bounds, or a safe-trace premise. -/
theorem Eval.lease_frame (run : Eval env term s value events t) :
    t.heap.lease = s.heap.lease := by
  induction run with
  | scalar | natural | var _ | allocate _ _ => rfl
  | app _ _ first last => exact last.trans first
  | free _ _ ih => exact ih
  | yes _ _ _ _ ih | no _ _ _ _ ih => exact ih
  | lend _ _ _ ih => exact ih
  | ownedLend _ _ _ _ ih => exact ih

end Jihoo.SizedErasure
