import Jihoo.SizedCoreTyping

/-! Static, slot-preserving contexts for symbolic buffer lengths. Every index
in an entry is expressed in the current lexical scope, as in Raw.Context.
Closing relates these contexts to the existing sized runtime judgment; it is
not itself a typing judgment. -/
namespace Jihoo.SymbolicCoreContext
open DependentBufferIndices
abbrev Index := Expr

inductive Entry where
  | nat
  | scalar
  | owner (slot : Nat)
  | bound (left right : Index)
  | dead
  deriving DecidableEq, Repr

abbrev Context := List Entry
abbrev Sizes := List Index

inductive Result where
  | scalar
  | owner (length : Index)
  deriving DecidableEq, Repr

def Entry.rename (ρ : Nat → Nat) : Entry → Entry
  | .bound a b => .bound (a.rename ρ) (b.rename ρ)
  | other => other

def Result.rename (ρ : Nat → Nat) : Result → Result
  | .scalar => .scalar
  | .owner n => .owner (n.rename ρ)

def Result.subst (σ : Nat → Index) : Result → Result
  | .scalar => .scalar
  | .owner n => .owner (n.subst σ)

def shift (e : Index) := e.rename Nat.succ
def shiftSizes (sizes : Sizes) := sizes.map shift
def shiftResult (kind : Result) := kind.rename Nat.succ

/-- The new entry is supplied before its binder, and is weakened too. -/
def push (entry : Entry) (ctx : Context) : Context :=
  entry.rename Nat.succ :: ctx.map (Entry.rename Nat.succ)

def Entry.mapOwner (f : Nat → Option Nat) : Entry → Entry
  | .owner k => match f k with | some j => .owner j | none => .dead
  | other => other

def mapOwners (f : Nat → Option Nat) (ctx : Context) : Context := ctx.map (Entry.mapOwner f)

def fresh (ctx : Context) : Context := push (.owner 0) (mapOwners (fun k => some (k+1)) ctx)
def transferred (ctx : Context) (slot : Nat) : Context :=
  push (.owner slot) (mapOwners (fun k => if k = slot then none else some k) ctx)
def consumed (slot : Nat) (ctx : Context) : Context :=
  mapOwners (fun k => if k = slot then none else some (if slot < k then k-1 else k)) ctx
def scalarReturned (ctx : Context) (slot : Nat) : Context := push (.owner slot) (push .scalar ctx)

def producer (ctx : Context) (p : Nat) : Context :=
  mapOwners (fun k => if k < p then some k else none) ctx

def callBody (ctx : Context) (p : Nat) : Context :=
  push (.owner 0) (mapOwners (fun k => if k < p then none else some (k-p+1)) ctx)

def ownedReturned (ctx : Context) (slot : Nat) : Context :=
  push (.owner (slot+1)) (fresh ctx)

def natSlots (ctx : Context) (k : Nat) : Prop := ctx[k]? = some .nat

def Entry.Closes (env : Env) : Entry → SizedBufferContext.Entry → Prop
  | .nat, .nat n => n < 2^64
  | .scalar, .scalar => True
  | .owner i, .owner j => i = j
  | .bound a b, .bound fact =>
      a.eval env = some fact.index ∧ b.eval env = some fact.length
  | .dead, .dead => True
  | _, _ => False

inductive ListRel (R : α → β → Prop) : List α → List β → Prop where
  | nil : ListRel R [] []
  | cons : R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

namespace ListRel

variable {α β : Type} {R S : α → β → Prop} {as : List α} {bs : List β} {k : Nat}

theorem lookup (h : ListRel R as bs) (ha : as[k]? = some a) :
    ∃ b, bs[k]? = some b ∧ R a b := by
  induction h generalizing k with
  | nil => simp at ha
  | cons hab _ ih =>
      cases k with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
                subst a; exact ⟨_, rfl, hab⟩
      | succ k => exact ih ha

theorem reverse (h : ListRel R as bs) : ListRel (fun b a => R a b) bs as := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons hab ih

theorem length (h : ListRel R as bs) : as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem map (h : ListRel R as bs) (step : ∀ a b, R a b → S (f a) (g b)) :
    ListRel S (as.map f) (bs.map g) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (step _ _ hab) ih

theorem transport (h : ListRel R as bs) (step : ∀ a b, R a b → S a b) :
    ListRel S as bs := by
  simpa using h.map (f := id) (g := id) step

end ListRel

def Closes (ctx : Context) (closed : SizedBufferContext.Context) : Prop :=
  ListRel (Entry.Closes (SizedBufferContext.naturalEnv closed)) ctx closed

def SizesEval (env : Env) (sizes : Sizes) (closed : List Nat) : Prop :=
  ListRel (fun e n => e.eval env = some n) sizes closed

def ResultEval (env : Env) : Result → SizedCoreTyping.Result → Prop
  | .scalar, .scalar => True
  | .owner e, .owner n => e.eval env = some n
  | _, _ => False

theorem Entry.Closes.rename (h : Entry.Closes source entry closed)
    (agree : ∀ k, target (ρ k) = source k) :
    Entry.Closes target (entry.rename ρ) closed := by
  cases entry <;> cases closed <;> simp_all [Entry.Closes, Entry.rename]
  case bound.bound a b fact =>
    exact ⟨(a.eval_rename agree).trans h.1, (b.eval_rename agree).trans h.2⟩

theorem Closes.lookup {k : Nat} (h : Closes ctx closed) (present : ctx[k]? = some entry) :
    ∃ value, closed[k]? = some value ∧ Entry.Closes (SizedBufferContext.naturalEnv closed) entry value :=
  ListRel.lookup h present

theorem Closes.nat_lookup (h : Closes ctx closed) (present : natSlots ctx k) :
    ∃ n, closed[k]? = some (.nat n) ∧ n < 2^64 := by
  obtain ⟨value, lookup, typed⟩ := h.lookup present
  cases value <;> simp_all [Entry.Closes]

theorem Closes.available (h : Closes ctx closed) (available : Available (natSlots ctx) e) :
    ∃ n, e.eval (SizedBufferContext.naturalEnv closed) = some n := by
  apply available.total
  intro k hk
  obtain ⟨n, hn, _⟩ := h.nat_lookup hk
  exact ⟨n, by simp [SizedBufferContext.naturalEnv, hn]⟩

theorem Closes.validNats (h : Closes ctx closed) : SizedBufferContext.ValidNats closed := by
  intro k n present
  cases lookup : closed[k]? with
  | none => simp [SizedBufferContext.naturalEnv, lookup] at present
  | some entry =>
      cases entry <;> simp [SizedBufferContext.naturalEnv, lookup] at present
      case nat m =>
        subst m
        obtain ⟨e, _, he⟩ := (ListRel.reverse h).lookup lookup
        cases e <;> simp_all [Entry.Closes]

theorem naturalEnv_cons_succ :
    SizedBufferContext.naturalEnv (value :: closed) (k+1) =
      SizedBufferContext.naturalEnv closed k := rfl

theorem Closes.extend (h : Closes ctx closed)
    (head : Entry.Closes (SizedBufferContext.naturalEnv (value :: closed))
      (entry.rename Nat.succ) value) :
    Closes (push entry ctx) (value :: closed) := by
  apply ListRel.cons head
  have mapped := ListRel.map h (f := Entry.rename Nat.succ) (g := id)
    (S := Entry.Closes (SizedBufferContext.naturalEnv (value :: closed)))
    (by intro a b hab; exact hab.rename (by intro k; rfl))
  simpa using mapped

theorem Closes.nat (h : Closes ctx closed) (bound : n < 2^64) :
    Closes (push .nat ctx) (.nat n :: closed) := h.extend bound

theorem Closes.scalar (h : Closes ctx closed) :
    Closes (push .scalar ctx) (.scalar :: closed) := h.extend trivial

theorem Closes.dead (h : Closes ctx closed) :
    Closes (push .dead ctx) (.dead :: closed) := h.extend trivial

theorem Closes.owner (h : Closes ctx closed) :
    Closes (push (.owner slot) ctx) (.owner slot :: closed) := h.extend rfl

theorem Closes.bound {a b : Expr} (h : Closes ctx closed)
    (left : a.eval (SizedBufferContext.naturalEnv closed) = some i)
    (right : b.eval (SizedBufferContext.naturalEnv closed) = some n) (lt : i < n) :
    Closes (push (.bound a b) ctx) (.bound ⟨i,n,lt⟩ :: closed) := by
  apply h.extend
  exact ⟨(a.eval_rename (by intro k; rfl)).trans left,
    (b.eval_rename (by intro k; rfl)).trans right⟩

theorem SizesEval.rename (h : SizesEval source sizes ns)
    (agree : ∀ k, target (ρ k) = source k) :
    SizesEval target (sizes.map (Expr.rename ρ)) ns := by
  have mapped := ListRel.map h (f := Expr.rename ρ) (g := id)
    (S := fun e n => e.eval target = some n)
    (by intro e n he; exact (e.eval_rename agree).trans he)
  simpa only [List.map_id_fun, id_eq, SizesEval] using mapped

theorem SizesEval.shift (h : SizesEval (SizedBufferContext.naturalEnv closed) sizes ns) :
    SizesEval (SizedBufferContext.naturalEnv (value :: closed)) (shiftSizes sizes) ns :=
  h.rename (by intro k; rfl)

theorem ResultEval.rename (h : ResultEval source result closed)
    (agree : ∀ k, target (ρ k) = source k) :
    ResultEval target (result.rename ρ) closed := by
  cases result <;> cases closed <;> simp_all [ResultEval, Result.rename]
  case owner.owner e n => exact (e.eval_rename agree).trans h

theorem ResultEval.shift (h : ResultEval (SizedBufferContext.naturalEnv ctx) result closed) :
    ResultEval (SizedBufferContext.naturalEnv (value :: ctx)) (shiftResult result) closed :=
  h.rename (by intro k; rfl)

theorem ResultEval.unshift
    (h : ResultEval (SizedBufferContext.naturalEnv (value :: ctx)) (shiftResult result) closed) :
    ResultEval (SizedBufferContext.naturalEnv ctx) result closed := by
  cases result <;> cases closed <;> simp_all [ResultEval, shiftResult, Result.rename]
  case owner.owner e n =>
    exact (e.eval_rename (source := SizedBufferContext.naturalEnv ctx)
      (target := SizedBufferContext.naturalEnv (value :: ctx)) (by intro k; rfl)).symm.trans h

theorem ResultEval.beta
    (argument : a.eval (SizedBufferContext.naturalEnv ctx) = some n)
    (body : ResultEval (SizedBufferContext.naturalEnv (.nat n :: ctx)) result closed) :
    ResultEval (SizedBufferContext.naturalEnv ctx) (result.subst (Expr.single a)) closed := by
  cases result <;> cases closed <;> simp_all [ResultEval, Result.subst]
  case owner.owner e m =>
    have envEq : SizedBufferContext.naturalEnv (SizedBufferContext.Entry.nat n :: ctx) =
        DependentBufferIndices.push n (SizedBufferContext.naturalEnv ctx) := by
      funext k; cases k <;> rfl
    rw [envEq] at body
    exact (Expr.eval_beta argument).trans body

theorem Closes.scalar_lookup {k : Nat} (h : Closes ctx closed)
    (present : ctx[k]? = some .scalar) : closed[k]? = some .scalar := by
  obtain ⟨value, lookup, typed⟩ := h.lookup present
  cases value <;> simp_all [Entry.Closes]

theorem Closes.owner_lookup {k : Nat} (h : Closes ctx closed)
    (present : ctx[k]? = some (.owner slot)) : closed[k]? = some (.owner slot) := by
  obtain ⟨value, lookup, typed⟩ := h.lookup present
  cases value <;> simp_all [Entry.Closes]

theorem Closes.bound_lookup {k : Nat} (h : Closes ctx closed)
    (present : ctx[k]? = some (.bound a b)) :
    ∃ fact, closed[k]? = some (.bound fact) ∧
      a.eval (SizedBufferContext.naturalEnv closed) = some fact.index ∧
      b.eval (SizedBufferContext.naturalEnv closed) = some fact.length := by
  obtain ⟨value, lookup, typed⟩ := h.lookup present
  cases value <;> simp_all [Entry.Closes]

def closedMapOwner (f : Nat → Option Nat) : SizedBufferContext.Entry → SizedBufferContext.Entry
  | .owner k => match f k with | some j => .owner j | none => .dead
  | other => other

theorem Entry.Closes.mapOwner (h : Entry.Closes env entry closed) :
    Entry.Closes env (entry.mapOwner f) (closedMapOwner f closed) := by
  cases entry <;> cases closed <;> simp_all [Entry.Closes, Entry.mapOwner, closedMapOwner]
  case owner.owner i j => subst j; cases f i <;> simp

theorem Closes.mapOwners (h : Closes ctx closed) :
    Closes (mapOwners f ctx) (SizedBufferContext.mapOwners f closed) := by
  unfold Closes
  rw [SizedBufferContext.mapOwners_naturalEnv]
  exact ListRel.map h (by intro a b hab; exact hab.mapOwner)

theorem Closes.fresh (h : Closes ctx closed) :
    Closes (fresh ctx) (SizedBufferContext.fresh closed) := by
  exact Closes.owner (h.mapOwners (f := fun k => some (k+1)))

theorem Closes.transferred (h : Closes ctx closed) :
    Closes (transferred ctx slot) (SizedBufferContext.transferred closed slot) := by
  exact Closes.owner (h.mapOwners (f := fun k => if k = slot then none else some k))

theorem Closes.consumed (h : Closes ctx closed) :
    Closes (consumed slot ctx) (SizedBufferContext.consumed slot closed) := by
  have mapped := h.mapOwners (f := fun k => if k = slot then none else some (if slot < k then k-1 else k))
  have eq : SizedBufferContext.mapOwners
      (fun k => if k = slot then none else some (if slot < k then k-1 else k)) closed =
      SizedBufferContext.consumed slot closed := by
    unfold SizedBufferContext.mapOwners SizedBufferContext.consumed
    congr 1
    funext e; cases e <;> simp
    case owner k => by_cases hk : k = slot <;> simp [hk]
  simpa only [eq, SymbolicCoreContext.consumed] using mapped

theorem Closes.scalarReturned (h : Closes ctx closed) :
    Closes (scalarReturned ctx slot) (SizedBufferContext.scalarReturned closed slot) :=
  h.scalar.owner

theorem SizesEval.lookup {k : Nat} (h : SizesEval env sizes ns) (present : sizes[k]? = some e) :
    ∃ n, ns[k]? = some n ∧ e.eval env = some n := ListRel.lookup h present

theorem SizesEval.length (h : SizesEval env sizes ns) : sizes.length = ns.length :=
  ListRel.length h

theorem SizesEval.eraseIdx (h : SizesEval env sizes ns) (k : Nat) :
    SizesEval env (sizes.eraseIdx k) (ns.eraseIdx k) := by
  induction h generalizing k with
  | nil => exact .nil
  | cons hab _ ih =>
      cases k with
      | zero => assumption
      | succ k => exact .cons hab (ih k)

theorem ResultEval.rename_inv
    (h : ResultEval target (result.rename ρ) closed)
    (agree : ∀ k, target (ρ k) = source k) : ResultEval source result closed := by
  cases result <;> cases closed <;> simp_all [ResultEval, Result.rename]
  case owner.owner e n => exact (e.eval_rename agree).symm.trans h

theorem ResultEval.beta_iff
    (argument : a.eval (SizedBufferContext.naturalEnv ctx) = some n) :
    ResultEval (SizedBufferContext.naturalEnv ctx) (result.subst (Expr.single a)) closed ↔
    ResultEval (SizedBufferContext.naturalEnv (.nat n :: ctx)) result closed := by
  have envEq : SizedBufferContext.naturalEnv (SizedBufferContext.Entry.nat n :: ctx) =
      DependentBufferIndices.push n (SizedBufferContext.naturalEnv ctx) := by
    funext k; cases k <;> rfl
  cases result <;> cases closed <;> simp only [ResultEval, Result.subst]
  all_goals try rfl
  rw [envEq, Expr.eval_beta argument]

theorem ResultEval.unbeta
    (argument : a.eval (SizedBufferContext.naturalEnv ctx) = some n)
    (outer : ResultEval (SizedBufferContext.naturalEnv ctx)
      (result.subst (Expr.single a)) closed) :
    ResultEval (SizedBufferContext.naturalEnv (.nat n :: ctx)) result closed :=
  (ResultEval.beta_iff argument).mp outer

/-- Only scalar, natural and erased propositions enter the pure projection.
Owner authority never becomes unrestricted Raw lookup. -/
def rawContext (ctx : Context) : CoreBridge.Raw.Context := fun k =>
  match ctx[k]? with
  | some .nat => some .u64
  | some .scalar => some .i64
  | some (.bound a b) => some (.lt a.encode b.encode)
  | _ => none

theorem rawTypes (present : natSlots ctx k) : rawContext ctx k = some .u64 := by
  simp only [rawContext, natSlots] at *
  rw [present]

theorem SizesEval.nil : SizesEval env [] [] := ListRel.nil

theorem SizesEval.cons (head : e.eval env = some n) (tail : SizesEval env es ns) :
    SizesEval env (e :: es) (n :: ns) := ListRel.cons head tail

theorem SizesEval.congr (h : SizesEval env sizes ns) (eq : env = target) :
    SizesEval target sizes ns := eq ▸ h

theorem ResultEval.congr (h : ResultEval env result kind) (eq : env = target) :
    ResultEval target result kind := eq ▸ h

theorem naturalEnv_fresh (ctx : SizedBufferContext.Context) :
    SizedBufferContext.naturalEnv (SizedBufferContext.fresh ctx) =
    SizedBufferContext.naturalEnv (.dead :: ctx) := by
  have eq := SizedBufferContext.mapOwners_naturalEnv (f := fun k => some (k+1)) (ctx := ctx)
  funext k
  cases k with
  | zero => rfl
  | succ k => exact congrFun eq k

theorem naturalEnv_transferred (ctx : SizedBufferContext.Context) (slot : Nat) :
    SizedBufferContext.naturalEnv (SizedBufferContext.transferred ctx slot) =
    SizedBufferContext.naturalEnv (.dead :: ctx) := by
  have eq := SizedBufferContext.mapOwners_naturalEnv
    (f := fun k => if k = slot then none else some k) (ctx := ctx)
  funext k
  cases k with
  | zero => rfl
  | succ k => exact congrFun eq k

theorem naturalEnv_consumed (ctx : SizedBufferContext.Context) (slot : Nat) :
    SizedBufferContext.naturalEnv (SizedBufferContext.consumed slot ctx) =
    SizedBufferContext.naturalEnv ctx := by
  funext k
  simp only [SizedBufferContext.naturalEnv, SizedBufferContext.consumed, List.getElem?_map]
  cases lookup : ctx[k]? with
  | none => rfl
  | some e =>
      cases e <;> simp
      case owner j => by_cases h : j = slot <;> simp [h]

theorem naturalEnv_scalarReturned (ctx : SizedBufferContext.Context) (slot : Nat) :
    SizedBufferContext.naturalEnv (SizedBufferContext.scalarReturned ctx slot) =
    SizedBufferContext.naturalEnv (.dead :: .dead :: ctx) := by
  funext k
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl

theorem Closes.producer (h : Closes ctx closed) :
    Closes (producer ctx p) (SizedBufferContext.producer closed p) := h.mapOwners

theorem Closes.callBody (h : Closes ctx closed) :
    Closes (callBody ctx p) (SizedBufferContext.callBody closed p) := h.mapOwners.owner

theorem Closes.ownedReturned (h : Closes ctx closed) :
    Closes (ownedReturned ctx slot) (SizedBufferContext.ownedReturned closed slot) := h.fresh.owner

theorem SizesEval.take (h : SizesEval env sizes ns) (p : Nat) :
    SizesEval env (sizes.take p) (ns.take p) := by
  induction h generalizing p with
  | nil => simpa using (SizesEval.nil (env := env))
  | cons hab _ ih => cases p with
    | zero => exact .nil
    | succ p => exact .cons hab (ih p)

theorem SizesEval.drop (h : SizesEval env sizes ns) (p : Nat) :
    SizesEval env (sizes.drop p) (ns.drop p) := by
  induction h generalizing p with
  | nil => simpa using (SizesEval.nil (env := env))
  | cons hab tail ih => cases p with
    | zero => exact .cons hab tail
    | succ p => exact ih p

theorem naturalEnv_producer (ctx : SizedBufferContext.Context) :
    SizedBufferContext.naturalEnv (SizedBufferContext.producer ctx p) =
    SizedBufferContext.naturalEnv ctx := SizedBufferContext.mapOwners_naturalEnv

theorem naturalEnv_callBody (ctx : SizedBufferContext.Context) :
    SizedBufferContext.naturalEnv (SizedBufferContext.callBody ctx p) =
    SizedBufferContext.naturalEnv (.dead :: ctx) := by
  funext k
  cases k with
  | zero => rfl
  | succ k => exact congrFun SizedBufferContext.mapOwners_naturalEnv k

theorem naturalEnv_ownedReturned (ctx : SizedBufferContext.Context) :
    SizedBufferContext.naturalEnv (SizedBufferContext.ownedReturned ctx slot) =
    SizedBufferContext.naturalEnv (.dead :: .dead :: ctx) := by
  funext k
  cases k with
  | zero => rfl
  | succ k => exact congrFun (naturalEnv_fresh ctx) k

end Jihoo.SymbolicCoreContext
