import Jihoo.NativeTyping
import Jihoo.NativeQuantity

/-! Context-derived resource inputs and a closed declaration gate. Callers do
not supply ownership or erasure lists. Classification is intentionally partial:
neutral/type-family domains require separate checked environment metadata.
The resulting theorems describe the projected control tree, not a native heap. -/
namespace Jihoo.NativeKernel.NativeOwnership

open Jihoo.Quantity

/-- Capture-avoiding weakening changes indices, never a resolved resource
head or its arity. Thus context lookup and stored annotations agree on mode. -/
theorem binderMode_rename (e : Bool) (domain : Term) (ρ : Nat → Nat) :
    NativeQuantity.binderMode e (domain.rename ρ) = NativeQuantity.binderMode e domain := by
  cases e with
  | true => simp [NativeQuantity.binderMode]
  | false =>
      cases domain with
      | var x => simp [NativeQuantity.binderMode, Term.rename]
      | node op args =>
          cases op <;> cases args with
          | nil => simp [NativeQuantity.binderMode, Term.rename, renameArgs]
          | cons a args =>
              cases args with
              | nil => simp [NativeQuantity.binderMode, Term.rename, renameArgs]
              | cons b args =>
                  cases args <;> simp [NativeQuantity.binderMode, Term.rename, renameArgs]

/-- Any binding actually returned by typed context lookup has the same mode
as its unweakened stored declaration at that slot. -/
theorem lookup_mode (found : lookup ctx r = some b) :
    ∃ declared : Binding, ctx[r]? = some declared ∧
      NativeQuantity.binderMode b.erased b.ty =
        NativeQuantity.binderMode declared.erased declared.ty := by
  induction ctx generalizing r b with
  | nil => simp [lookup] at found
  | cons head ctx ih =>
      cases r with
      | zero =>
          simp only [lookup, Option.some.injEq] at found
          subst b
          exact ⟨head, rfl, binderMode_rename _ _ _⟩
      | succ r =>
          cases hr : lookup ctx r with
          | none => simp [lookup, hr] at found
          | some old =>
              simp only [lookup, hr, Option.map_some, Option.some.injEq] at found
              subst b
              obtain ⟨declared, selected, mode⟩ := ih hr
              exact ⟨declared, selected, (binderMode_rename _ _ _).trans mode⟩

/-- Classify the actual declared bindings, in newest-first de Bruijn order. -/
def classify : Context → Option (List BinderMode)
  | [] => some []
  | b :: ctx => do
      let mode ← NativeQuantity.binderMode b.erased b.ty
      let modes ← classify ctx
      pure (mode :: modes)

inductive Classified : Context → List BinderMode → Prop where
  | nil : Classified [] []
  | cons : NativeQuantity.binderMode b.erased b.ty = some mode →
      Classified ctx modes → Classified (b :: ctx) (mode :: modes)

theorem classify_sound (h : classify ctx = some modes) : Classified ctx modes := by
  induction ctx generalizing modes with
  | nil => simp [classify] at h; subst modes; exact .nil
  | cons b ctx ih =>
      cases hb : NativeQuantity.binderMode b.erased b.ty with
      | none => simp [classify, hb] at h
      | some mode =>
          cases hc : classify ctx with
          | none => simp [classify, hb, hc] at h
          | some rest =>
              simp only [classify, hb, hc, Bind.bind, Option.bind, pure, Option.some.injEq] at h
              subst modes
              exact .cons hb (ih hc)

theorem Classified.length (h : Classified ctx modes) : modes.length = ctx.length := by
  induction h <;> simp_all

/-- Every selected mode comes from that exact context slot. -/
theorem Classified.at {r : Nat} {b : Binding} (h : Classified ctx modes) (found : ctx[r]? = some b) :
    modes[r]? = NativeQuantity.binderMode b.erased b.ty := by
  induction h generalizing r with
  | nil => simp at found
  | cons hb rest ih =>
      cases r with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst b; exact hb.symm
      | succ r => simpa only [List.getElem?_cons_succ] using ih found

/-- Slot selection carries no external list of owner indices. -/
def slots (target : BinderMode) : List BinderMode → List Nat
  | [] => []
  | mode :: modes => (if mode = target then [0] else []) ++ (slots target modes).map Nat.succ

theorem mem_slots (target : BinderMode) (modes : List BinderMode) (r : Nat) :
    r ∈ slots target modes ↔ modes[r]? = some target := by
  induction modes generalizing r with
  | nil => simp [slots]
  | cons mode modes ih =>
      cases r with
      | zero => simp [slots, List.mem_map]
      | succ r => simp [slots, List.mem_map, ih]

def owners (modes : List BinderMode) : List Nat := slots .linear modes

def erased (modes : List BinderMode) : List Nat := slots .erased modes

/-- The fresh sentinel is the actual context depth. All owner and erased slots
are computed from that same context. Unresolved domains reject explicitly. -/
def check (fuel : Nat) (ctx : Context) (t : Term) : Bool :=
  match classify ctx with
  | none => false
  | some modes => NativeQuantity.check fuel ctx.length (owners modes) (erased modes) t

theorem checked_origin (h : check fuel ctx t = true) :
    ∃ modes, Classified ctx modes ∧
      NativeQuantity.check fuel ctx.length (owners modes) (erased modes) t = true := by
  cases hc : classify ctx with
  | none => simp [check, hc] at h
  | some modes => exact ⟨modes, classify_sound hc, by simpa only [check, hc] using h⟩

theorem checked_owner_finished (h : check fuel ctx t = true)
    (found : ctx[r]? = some b) (owned : NativeQuantity.binderMode b.erased b.ty = some .linear)
    (run : NativeQuantity.Finishes fuel t events) : events.count r = 1 := by
  obtain ⟨modes, classified, checked⟩ := checked_origin h
  exact NativeQuantity.checked_finished checked run r
    ((mem_slots _ _ _).mpr ((classified.at found).trans owned))

theorem checked_owner_prefix (h : check fuel ctx t = true)
    (found : ctx[r]? = some b) (owned : NativeQuantity.binderMode b.erased b.ty = some .linear)
    (run : NativeQuantity.Prefix fuel t events) : events.count r ≤ 1 := by
  obtain ⟨modes, classified, checked⟩ := checked_origin h
  exact NativeQuantity.checked_prefix checked run r
    ((mem_slots _ _ _).mpr ((classified.at found).trans owned))

theorem checked_erased_prefix (h : check fuel ctx t = true)
    (found : ctx[r]? = some b) (removed : b.erased = true)
    (run : NativeQuantity.Prefix fuel t events) : r ∉ events := by
  obtain ⟨modes, classified, checked⟩ := checked_origin h
  have mode : modes[r]? = some .erased := by
    rw [classified.at found]
    simp [NativeQuantity.binderMode, removed]
  exact NativeQuantity.checked_erased checked run r ((mem_slots _ _ _).mpr mode)

theorem checked_sentinel (h : check fuel ctx t = true)
    (run : NativeQuantity.Prefix fuel t events) : ctx.length ∉ events := by
  obtain ⟨_, _, checked⟩ := checked_origin h
  exact NativeQuantity.checked_sentinel checked run

/-- The resource certificate applies directly to the binding used by the
typing rule, including all type weakening performed by `lookup`. -/
theorem checked_lookup_owner_finished (h : check fuel ctx t = true)
    (found : lookup ctx r = some b) (owned : NativeQuantity.binderMode b.erased b.ty = some .linear)
    (run : NativeQuantity.Finishes fuel t events) : events.count r = 1 := by
  obtain ⟨declared, selected, mode⟩ := lookup_mode found
  exact checked_owner_finished h selected (mode.symm.trans owned) run

theorem checked_lookup_owner_prefix (h : check fuel ctx t = true)
    (found : lookup ctx r = some b) (owned : NativeQuantity.binderMode b.erased b.ty = some .linear)
    (run : NativeQuantity.Prefix fuel t events) : events.count r ≤ 1 := by
  obtain ⟨declared, selected, mode⟩ := lookup_mode found
  exact checked_owner_prefix h selected (mode.symm.trans owned) run

theorem checked_lookup_erased_prefix (h : check fuel ctx t = true)
    (found : lookup ctx r = some b) (removed : b.erased = true)
    (run : NativeQuantity.Prefix fuel t events) : r ∉ events := by
  obtain ⟨declared, selected, mode⟩ := lookup_mode found
  obtain ⟨modes, classified, checked⟩ := checked_origin h
  have slot : modes[r]? = some .erased := by
    rw [classified.at selected, ← mode]
    simp [NativeQuantity.binderMode, removed]
  exact NativeQuantity.checked_erased checked run r ((mem_slots _ _ _).mpr slot)

/-- Closed code declarations have authentic depth zero and empty outer lists.
The sentinel still enforces every analyzed local ownership/capture condition. -/
def checkClosed (fuel : Nat) (t : Term) : Bool := NativeQuantity.check fuel 0 [] [] t

@[simp] theorem check_empty : check fuel [] t = checkClosed fuel t := rfl

def ClosedSafe (t : Term) : Prop := ∃ fuel, checkClosed fuel t = true

/-- Declaration mode is supplied by independently checking its declared sort.
Ghost declarations have no runtime projection obligations. -/
def declarationGate (fuel : Nat) (ghost : Bool) (t : Term) : Bool := ghost || checkClosed fuel t

theorem declarationGate_code (h : declarationGate fuel false t = true) : ClosedSafe t := by
  exact ⟨fuel, by simpa only [declarationGate, Bool.false_or] using h⟩

theorem closed_localScopes (h : checkClosed fuel t = true) :
    ∃ c, NativeQuantity.project fuel t = some c ∧ NativeQuantity.LocalScopes c :=
  NativeQuantity.checked_localScopes h

theorem closed_no_sentinel (h : checkClosed fuel t = true)
    (run : NativeQuantity.Prefix fuel t events) : 0 ∉ events :=
  NativeQuantity.checked_sentinel h run

end Jihoo.NativeKernel.NativeOwnership
