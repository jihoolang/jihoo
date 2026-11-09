import Jihoo.QuantityLendProjection

/-! Capture-avoiding substitution at the quantity-annotated source boundary.
Borrow replacement erases an ownership-use event; it is not an arbitrary
expression substitution. Descriptor/mode stability and the native graph view
remain typing/implementation obligations. -/
namespace Jihoo.Quantity.Substitution

abbrev PartialMap := Nat → Option Nat

def liftPartial (ρ : PartialMap) : PartialMap
  | 0 => some 0
  | n + 1 => (ρ n).map Nat.succ

def _root_.Jihoo.Quantity.Control.relabel (c : Control) (ρ : PartialMap) : Control := match c with
  | .pure => .pure
  | .trap => .trap
  | .use k => match ρ k with | some j => .use j | none => .pure
  | .seq a b => .seq (a.relabel ρ) (b.relabel ρ)
  | .branch a b => .branch (a.relabel ρ) (b.relabel ρ)
  | .repeat b => .repeat (b.relabel ρ)
  | .once b => .once (b.relabel ρ)
  | .closure b => .closure (b.relabel ρ)
  | .erased b => .erased (b.relabel ρ)
  | .scope mode b => .scope mode (b.relabel (liftPartial ρ))

theorem discharge_filterMap (xs : List Nat) :
    discharge (xs.filterMap (liftPartial ρ)) = (discharge xs).filterMap ρ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | zero => simp [discharge, liftPartial, ih]
    | succ x => cases hx : ρ x <;> simp [discharge, liftPartial, hx, ih]

theorem _root_.Jihoo.Quantity.Finishes.relabel (run : Finishes c xs) (ρ : PartialMap) :
    Finishes (c.relabel ρ) (xs.filterMap ρ) := by
  induction run generalizing ρ with
  | pure => exact .pure
  | @use k => cases hk : ρ k <;> simp [Control.relabel, hk] <;> constructor
  | seq ha hb iha ihb => simpa only [Control.relabel, List.filterMap_append] using Finishes.seq (iha ρ) (ihb ρ)
  | left _ ih => exact .left (ih ρ)
  | right _ ih => exact .right (ih ρ)
  | repeatZero => exact .repeatZero
  | repeatNext ha hb iha ihb => simpa only [Control.relabel, List.filterMap_append] using Finishes.repeatNext (iha ρ) (ihb ρ)
  | once _ ih => exact .once (ih ρ)
  | closure => exact .closure
  | erased => exact .erased
  | bind _ ih => simpa only [Control.relabel, discharge_filterMap] using Finishes.bind (ih (liftPartial ρ))

theorem _root_.Jihoo.Quantity.Prefix.relabel (run : Prefix c xs) (ρ : PartialMap) :
    Prefix (c.relabel ρ) (xs.filterMap ρ) := by
  induction run generalizing ρ with
  | start => exact .start
  | @use k => cases hk : ρ k <;> simp [Control.relabel, hk]; exact .start; exact .use
  | seqLeft _ ih => exact .seqLeft (ih ρ)
  | seqRight ha hb ih => simpa only [Control.relabel, List.filterMap_append] using Prefix.seqRight (ha.relabel ρ) (ih ρ)
  | left _ ih => exact .left (ih ρ)
  | right _ ih => exact .right (ih ρ)
  | repeatNext ha hb ih => simpa only [Control.relabel, List.filterMap_append] using Prefix.repeatNext (ha.relabel ρ) (ih ρ)
  | repeatBody _ ih => exact .repeatBody (ih ρ)
  | once _ ih => exact .once (ih ρ)
  | bind _ ih => simpa only [Control.relabel, discharge_filterMap] using Prefix.bind (ih (liftPartial ρ))

private theorem lift_zero : ∀ x, liftPartial ρ x = some 0 ↔ x = 0 := by
  intro x; cases x with
  | zero => simp [liftPartial]
  | succ x => cases h : ρ x <;> simp [liftPartial, h]

private theorem lift_fiber (h : ∀ x, ρ x = some r ↔ x = s) :
    ∀ x, liftPartial ρ x = some (r + 1) ↔ x = s + 1 := by
  intro x; cases x with
  | zero => simp [liftPartial]
  | succ x => simpa [liftPartial] using h x

/-- A unique preimage of the queried resource preserves the complete checker
result, including rejection from local linear/erased scopes and capture checks. -/
theorem relabel_demand (c : Control) {ρ : PartialMap} {r s : Nat} (h : ∀ x, ρ x = some r ↔ x = s) :
    (c.relabel ρ).demand r = c.demand s := by
  induction c generalizing ρ r s with
  | pure | trap => rfl
  | use k =>
    have hk := h k
    cases hr : ρ k <;> simp_all [Control.relabel, Control.demand]
  | seq a b iha ihb => simp only [Control.relabel, Control.demand, iha h, ihb h]
  | branch a b iha ihb => simp only [Control.relabel, Control.demand, iha h, ihb h]
  | «repeat» b ih | closure b ih => simp only [Control.relabel, Control.demand, ih h]
  | once b ih => exact ih h
  | erased b ih => rfl
  | scope mode b ih =>
    have localEq := ih (ρ := liftPartial ρ) (r := 0) (s := 0) lift_zero
    have outerEq := ih (lift_fiber h)
    cases mode <;> simp only [Control.relabel, Control.demand, localEq, outerEq]

private theorem lift_precompose : liftPartial (fun n => ρ (f n)) = fun n => liftPartial ρ (lift f n) := by
  funext n; cases n <;> rfl
private theorem lift_postcompose : liftPartial (fun n => (ρ n).map f) = fun n => (liftPartial ρ n).map (lift f) := by
  funext n; cases n with
  | zero => rfl
  | succ n => cases h : ρ n <;> simp [liftPartial, lift, h]

theorem rename_relabel (c : Control) :
    (c.rename f).relabel ρ = c.relabel (fun n => ρ (f n)) := by
  induction c generalizing f ρ <;> simp_all [Control.rename, Control.relabel, lift_precompose]

theorem relabel_rename (c : Control) :
    (c.relabel ρ).rename f = c.relabel (fun n => (ρ n).map f) := by
  induction c generalizing ρ f with
  | use k => cases h : ρ k <;> simp [Control.relabel, Control.rename, h]
  | _ => simp_all [Control.rename, Control.relabel, lift_postcompose]

def dropBorrow : PartialMap
  | 0 => none | n + 1 => some n

theorem drop_borrow_demand (c : Control) :
    (c.relabel dropBorrow).demand r = (Control.scope .borrowed c).demand r := by
  apply relabel_demand
  intro x; cases x <;> simp [dropBorrow]

theorem drop_borrow_trace (xs : List Nat) : xs.filterMap dropBorrow = discharge xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [List.filterMap_cons, dropBorrow, discharge, ih]

/-- Only value replacements used by dependent Lend: a variable or its borrow.
No effectful expression, allocation or duplication law is assumed. -/
inductive Atom where
  | var (k : Nat)
  | borrow (k : Nat)
  deriving DecidableEq, Repr

def Atom.shift : Atom → Atom
  | .var k => .var (k + 1) | .borrow k => .borrow (k + 1)
def Atom.event : Atom → Option Nat
  | .var k => some k | .borrow _ => none

def liftAtoms (σ : Nat → Atom) : Nat → Atom
  | 0 => .var 0 | n + 1 => (σ n).shift

/-- Quantity-annotated structural source. A scope is an invoked binder, not a
reusable lambda. Mode annotations must already be justified and stable. -/
inductive Expr where
  | literal
  | var (k : Nat)
  | borrow (owner : Nat)
  | seq (a b : Expr)
  | scope (mode : BinderMode) (body : Expr)
  | lend (owner : Nat) (resultMode : BinderMode) (reader continuation : Expr)
  deriving DecidableEq, Repr

def Atom.expr : Atom → Expr
  | .var k => .var k | .borrow k => .borrow k

def Expr.project : Expr → Control
  | .literal | .borrow _ => .pure
  | .var k => .use k
  | .seq a b => .seq a.project b.project
  | .scope m b => .scope m b.project
  | .lend k m read rest => LendProjection.scopedLend k m read.project rest.project

/-- Retain source identity when reifying a successful graph projection. Borrow
owner indices are preserved here, even though their event projection is pure. -/
inductive Represents (graph : LendProjection.Syntax) (observe : ContextProjection.Observe) :
    List ContextProjection.Entry → Nat → Expr → Prop where
  | literal : graph root = .literal → Represents graph observe ctx root .literal
  | var : graph root = .var k → ContextProjection.lookup ctx k = some entry →
      entry.raw.erased = false → Represents graph observe ctx root (.var k)
  | borrow : graph root = .borrow owner → graph owner = .var k →
      ContextProjection.lookup ctx k = some entry → entry.raw.erased = false →
      Represents graph observe ctx root (.borrow k)
  | seq : graph root = .seq first second → Represents graph observe ctx first a →
      Represents graph observe ctx second b → Represents graph observe ctx root (.seq a b)
  | lend {read rest : Expr} : LendProjection.prepare graph observe ctx root = some shape →
      Represents graph observe shape.readerContext shape.reader read →
      Represents graph observe shape.continuationContext shape.continuation rest →
      Represents graph observe ctx root (.lend shape.owner shape.resultMode read rest)

theorem projects_represents (h : LendProjection.Projects graph observe ctx root c) :
    ∃ e, Represents graph observe ctx root e ∧ e.project = c := by
  induction h with
  | literal hv => exact ⟨.literal, .literal hv, rfl⟩
  | var hv hl he => exact ⟨.var _, .var hv hl he, rfl⟩
  | borrow hv ho hl he => exact ⟨.borrow _, .borrow hv ho hl he, rfl⟩
  | seq hv _ _ iha ihb =>
    obtain ⟨a, ha, rfl⟩ := iha
    obtain ⟨b, hb, rfl⟩ := ihb
    exact ⟨.seq a b, .seq hv ha hb, rfl⟩
  | lend hs _ _ checked ihr ihc =>
    obtain ⟨read, hr, rfl⟩ := ihr
    obtain ⟨rest, hc, rfl⟩ := ihc
    exact ⟨.lend _ _ read rest, .lend hs hr hc, (LendProjection.checked_lend_origin checked).1.symm⟩

/-- Substitution traverses under every binder. Borrow/Lend owner positions
must remain variables; replacing those positions by borrows fails explicitly. -/
def Expr.subst (σ : Nat → Atom) : Expr → Option Expr
  | .literal => some .literal
  | .var k => some (σ k).expr
  | .borrow k => match σ k with | .var j => some (.borrow j) | _ => none
  | .seq a b => do return .seq (← a.subst σ) (← b.subst σ)
  | .scope m b => do return .scope m (← b.subst (liftAtoms σ))
  | .lend k m read rest => match σ k with
    | .var j => do return .lend j m (← read.subst (liftAtoms σ)) (← rest.subst (liftAtoms (liftAtoms σ)))
    | _ => none

private theorem event_lift : (fun n => (liftAtoms σ n).event) = liftPartial (fun n => (σ n).event) := by
  funext n; cases n with
  | zero => rfl
  | succ n => cases h : σ n <;> simp [liftAtoms, liftPartial, Atom.event, Atom.shift, h]

private theorem alias_lift {σ : Nat → Atom} (h : σ k = .var j) :
    (fun n => liftPartial (fun n => (σ n).event) (openOwner (k + 1) n)) =
    (fun n => (liftPartial (liftPartial (fun n => (σ n).event)) n).map (openOwner (j + 1))) := by
  funext n
  cases n with
  | zero => simp [openOwner, liftPartial, h, Atom.event]
  | succ n => cases n with
    | zero => rfl
    | succ n => cases hn : σ n <;> simp [liftPartial, openOwner, Atom.event, hn]

theorem substitution_projection {e out : Expr} {σ : Nat → Atom} (h : e.subst σ = some out) :
    out.project = e.project.relabel (fun n => (σ n).event) := by
  induction e generalizing σ out with
  | literal => simp [Expr.subst] at h; subst out; rfl
  | var k => simp [Expr.subst] at h; subst out; cases hs : σ k <;> simp [Atom.expr, Expr.project, Control.relabel, Atom.event, hs]
  | borrow k =>
    cases hs : σ k <;> simp_all [Expr.subst]
    subst out
    rfl
  | seq a b iha ihb =>
    simp only [Expr.subst] at h
    cases ha : a.subst σ <;> simp_all
    case some a' =>
      cases hb : b.subst σ <;> simp_all
      case some b' =>
        subst out
        simp [Expr.project, Control.relabel, iha ha, ihb hb]
  | scope m b ih =>
    simp only [Expr.subst] at h
    cases hb : b.subst (liftAtoms σ) <;> simp_all
    case some b' =>
      subst out
      simp [Expr.project, Control.relabel, ih hb, event_lift]
  | lend k m read rest ihr ihc =>
    cases hs : σ k <;> simp only [Expr.subst, hs] at h
    case borrow _ => contradiction
    case var j =>
      cases hr : read.subst (liftAtoms σ) <;> simp_all
      case some read' =>
        cases hc : rest.subst (liftAtoms (liftAtoms σ)) <;> simp_all
        case some rest' =>
          subst out
          simp only [Expr.project, LendProjection.scopedLend, Control.relabel, ihr hr, ihc hc, event_lift]
          simp only [Control.alias]
          rw [relabel_rename, rename_relabel, alias_lift hs]

/-- These are exactly the value shapes used by dependent_lend. The continuation
replacement is used with owner+1 because the result binder remains in scope. -/
def openBorrow (owner : Nat) : Nat → Atom
  | 0 => .borrow owner | n + 1 => .var n

def openVariable (owner : Nat) : Nat → Atom
  | 0 => .var owner | n + 1 => .var n

private theorem lift_some : liftPartial (fun n => some (f n)) = fun n => some (lift f n) := by
  funext n; cases n <;> rfl

theorem relabel_some (c : Control) : c.relabel (fun n => some (f n)) = c.rename f := by
  induction c generalizing f <;> simp_all [Control.relabel, Control.rename, lift_some]

theorem reader_projection {read after : Expr} (h : read.subst (openBorrow owner) = some after) :
    after.project = read.project.relabel dropBorrow := by
  have mapEq : (fun n => (openBorrow owner n).event) = dropBorrow := by
    funext n; cases n <;> rfl
  simpa only [mapEq] using substitution_projection h

theorem continuation_projection {rest after : Expr}
    (h : rest.subst (openVariable (owner + 1)) = some after) :
    after.project = .alias (owner + 1) rest.project := by
  have mapEq : (fun n => (openVariable (owner + 1) n).event) =
      (fun n => some (openOwner (owner + 1) n)) := by
    funext n; cases n <;> rfl
  simpa only [mapEq, relabel_some] using substitution_projection h

theorem reader_demand {read after : Expr} (h : read.subst (openBorrow owner) = some after) :
    after.project.demand r = (Control.scope .borrowed read.project).demand r := by
  rw [reader_projection h, drop_borrow_demand]

theorem reader_finishes {read after : Expr} (h : read.subst (openBorrow owner) = some after)
    (run : Finishes read.project xs) : Finishes after.project (discharge xs) := by
  rw [reader_projection h]
  simpa only [drop_borrow_trace] using run.relabel dropBorrow

theorem reader_prefix {read after : Expr} (h : read.subst (openBorrow owner) = some after)
    (run : Prefix read.project xs) : Prefix after.project (discharge xs) := by
  rw [reader_projection h]
  simpa only [drop_borrow_trace] using run.relabel dropBorrow

/-- The two substituted bodies have exactly the original scoped Lend checker
result for every outer resource, including failures from nested obligations. -/
theorem lend_demand_correspondence {read rest readAfter restAfter : Expr}
    (hr : read.subst (openBorrow owner) = some readAfter)
    (hc : rest.subst (openVariable (owner + 1)) = some restAfter) :
    (Control.seq readAfter.project (.scope mode restAfter.project)).demand r =
      (LendProjection.scopedLend owner mode read.project rest.project).demand r := by
  rw [continuation_projection hc]
  simp only [LendProjection.scopedLend, Control.demand, reader_demand hr]

theorem lend_substituted_finished {read rest readAfter restAfter : Expr}
    (hr : read.subst (openBorrow owner) = some readAfter)
    (hc : rest.subst (openVariable (owner + 1)) = some restAfter)
    (checked : LendProjection.checkedLend owner mode read.project rest.project = some c)
    (run : Finishes (.seq readAfter.project (.scope mode restAfter.project)) xs) :
    xs.count owner = 1 := by
  apply run.count_eq
  rw [lend_demand_correspondence hr hc, ← (LendProjection.checked_lend_origin checked).1]
  exact LendProjection.checked_lend_demand checked

theorem lend_substituted_prefix {read rest readAfter restAfter : Expr}
    (hr : read.subst (openBorrow owner) = some readAfter)
    (hc : rest.subst (openVariable (owner + 1)) = some restAfter)
    (checked : LendProjection.checkedLend owner mode read.project rest.project = some c)
    (run : Prefix (.seq readAfter.project (.scope mode restAfter.project)) xs) :
    xs.count owner ≤ 1 := by
  apply run.count_le
  rw [lend_demand_correspondence hr hc, ← (LendProjection.checked_lend_origin checked).1]
  exact LendProjection.checked_lend_demand checked

/-- The source used by commutation is obtained from the existing successful
rooted graph projection, not an independently supplied control/expression. -/
theorem rooted_substitution_source
    (h : LendProjection.rootedProject graph observe depth budget root = some (ctx, c, remaining)) :
    ∃ leaf e, ContextProjection.Path (LendProjection.head graph) observe [] root ctx leaf ∧
      ContextProjection.Authentic observe ctx ∧ Represents graph observe ctx leaf e ∧ e.project = c ∧
      ∀ σ out, e.subst σ = some out → out.project = c.relabel (fun n => (σ n).event) := by
  obtain ⟨leaf, path, authentic, projected, _⟩ := LendProjection.rooted_project_sound h
  obtain ⟨e, represented, he⟩ := projects_represents projected
  refine ⟨leaf, e, path, authentic, represented, he, ?_⟩
  intro σ out hs
  rw [← he]
  exact substitution_projection hs

end Jihoo.Quantity.Substitution
