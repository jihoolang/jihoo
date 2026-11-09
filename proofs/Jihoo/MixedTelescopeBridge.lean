import Jihoo.MixedTelescope
import Jihoo.CoreBridgeTyping

/-! Representable mixed telescopes, with a constructed unified Raw context.
The target is the existing ghost declarative judgment, not Core.infer. -/
namespace Jihoo.CoreBridge.MixedBridge
open Indexed (liftRenaming)

inductive Telescope where
  | empty
  | natural : Telescope → Telescope
  | proof : Telescope → Ty → Telescope

def Telescope.erase : Telescope → Indexed.Mixed.Telescope
  | .empty => .empty
  | .natural Γ => .natural Γ.erase
  | .proof Γ A => .proof Γ.erase A.erase

def Telescope.naturals : Telescope → Nat
  | .empty => 0
  | .natural Γ => Γ.naturals + 1
  | .proof Γ _ => Γ.naturals

def Telescope.proofs : Telescope → List Ty
  | .empty => []
  | .natural Γ => Γ.proofs.map (fun A => A.subst Index.shift)
  | .proof Γ A => A :: Γ.proofs

def Telescope.indices : Telescope → Nat → Nat
  | .empty => fun _ => 0
  | .natural Γ => liftRenaming Γ.indices
  | .proof Γ _ => fun x => Γ.indices x + 1

def Telescope.values : Telescope → Nat → Nat
  | .empty => fun _ => 0
  | .natural Γ => fun x => Γ.values x + 1
  | .proof Γ _ => liftRenaming Γ.values

def Telescope.context : Telescope → Raw.Context
  | .empty => fun _ => none
  | .natural Γ => Γ.context.extend .u64
  | .proof Γ A => Γ.context.extend (A.encode Γ.indices)

def Telescope.layout : Telescope → Layout
  | .empty => []
  | .natural Γ => .index :: Γ.layout
  | .proof Γ _ => .value :: Γ.layout

theorem Telescope.context_match (Γ : Telescope) :
    ContextMatch Γ.naturals Γ.proofs Γ.context Γ.indices Γ.values := by
  induction Γ with
  | empty => constructor <;> simp [naturals, proofs]
  | natural Γ ih => exact ih.index
  | proof Γ A ih => exact ih.value A

theorem Telescope.indices_slot (Γ : Telescope) (x : Nat) :
    Γ.indices x = slot .index x Γ.layout := by
  induction Γ generalizing x with
  | empty => rfl
  | natural Γ ih => cases x <;> simp [indices, layout, liftRenaming, slot, ih]
  | proof Γ A ih => simp [indices, layout, slot, ih]

theorem Telescope.values_slot (Γ : Telescope) (x : Nat) :
    Γ.values x = slot .value x Γ.layout := by
  induction Γ generalizing x with
  | empty => rfl
  | natural Γ ih => simp [values, layout, slot, ih]
  | proof Γ A ih => cases x <;> simp [values, layout, liftRenaming, slot, ih]

theorem Telescope.count_indices (Γ : Telescope) : count .index Γ.layout = Γ.naturals := by
  induction Γ <;> simp_all [layout, naturals, count, Nat.add_comm]

theorem Telescope.count_values (Γ : Telescope) : count .value Γ.layout = Γ.proofs.length := by
  induction Γ <;> simp_all [layout, proofs, count, Nat.add_comm]

theorem Telescope.namespaces_disjoint (Γ : Telescope) (hi : i < Γ.naturals)
    (hv : v < Γ.proofs.length) : Γ.indices i ≠ Γ.values v := by
  rw [Γ.indices_slot, Γ.values_slot]
  exact slots_disjoint (by simpa [Γ.count_indices] using hi)
    (by simpa [Γ.count_values] using hv)

@[simp] theorem Telescope.erase_naturals (Γ : Telescope) : Γ.erase.naturals = Γ.naturals := by
  induction Γ <;> simp_all [erase, naturals, Indexed.Mixed.Telescope.naturals]

theorem Telescope.erase_proofs (Γ : Telescope) : Γ.erase.proofs = Γ.proofs.map Ty.erase := by
  induction Γ with
  | empty => rfl
  | natural Γ ih =>
      simp only [erase, Indexed.Mixed.Telescope.proofs, proofs, ih, List.map_map]
      congr 1
      funext A
      exact (Ty.erase_subst A Index.shift).symm
  | proof Γ A ih => simp [erase, Indexed.Mixed.Telescope.proofs, proofs, ih]

inductive WellFormed : Telescope → Prop where
  | empty : WellFormed .empty
  | natural : WellFormed Γ → WellFormed (.natural Γ)
  | proof : WellFormed Γ → Indexed.Mixed.Proposition A.erase → A.Scoped Γ.naturals →
      WellFormed (.proof Γ A)

theorem WellFormed.erase (h : WellFormed Γ) : Indexed.Mixed.WellFormed Γ.erase := by
  induction h with
  | empty => exact .empty
  | natural _ ih => exact .natural ih
  | proof _ hp hs ih =>
      exact .proof ih hp (by simpa using Ty.erase_scoped hs)

/-- A source derivation produces an independently typed Raw expression in the
actual mixed-order context; ContextMatch is proved, not supplied by the caller. -/
theorem translate {Γ : Telescope} (h : SourceTyping Γ.naturals Γ.proofs t A) :
    Raw.HasType Γ.context (t.encode Γ.indices Γ.values) (A.encode Γ.indices) :=
  h.translate Γ.context_match

/-- The same derivation enters the semantic telescope judgment. No validity of
the conclusion, Raw typing, or source/target context match is assumed. -/
theorem erase_derivation (wf : WellFormed Γ)
    (hp : Indexed.Mixed.Proposition A.erase)
    (h : SourceTyping Γ.naturals Γ.proofs t A) :
    Indexed.Mixed.Derives Γ.erase t.erase A.erase := by
  refine ⟨wf.erase, hp, wf.erase.scoped, ?_, ?_, ?_⟩
  · rw [Γ.erase_naturals, Γ.erase_proofs, List.length_map]
    exact Term.erase_scoped h.scoped.1
  · rw [Γ.erase_naturals]
    exact Ty.erase_scoped h.scoped.2
  · rw [Γ.erase_proofs]
    exact h.erases

theorem semantic_sound (wf : WellFormed Γ)
    (hp : Indexed.Mixed.Proposition A.erase)
    (h : SourceTyping Γ.naturals Γ.proofs t A)
    (hv : Indexed.Mixed.Valid Γ.erase ρ) : Indexed.Mixed.Holds A.erase ρ :=
  (erase_derivation wf hp h).sound hv

/-- Closing a telescope wraps each binder in its ORIGINAL scope, not the final
scope where intervening binders would capture annotation variables. -/
def Telescope.closeTerm : Telescope → Raw → Raw
  | .empty, t => t
  | .natural Γ, t => Γ.closeTerm (.lam false .u64 t)
  | .proof Γ A, t => Γ.closeTerm (.lam A.proposition (A.encode Γ.indices) t)

def Telescope.closeType : Telescope → Raw → Raw
  | .empty, A => A
  | .natural Γ, A => Γ.closeType (.pi false .u64 A)
  | .proof Γ P, A => Γ.closeType (.pi P.proposition (P.encode Γ.indices) A)

theorem close_typed (wf : WellFormed Γ) (h : Raw.HasType Γ.context t A) :
    Raw.HasType (fun _ => none) (Γ.closeTerm t) (Γ.closeType A) := by
  induction wf generalizing t A with
  | empty => exact h
  | natural _ ih => exact ih (.lam .u64 rfl h)
  | @proof Γ P _ _ hs ih =>
      apply ih
      exact .lam (Ty.encode_isType hs Γ.context_match.1) (Ty.encode_proposition P Γ.indices).symm h

/-- A closed, unified, typed term and semantic validity share the same source
witness. This is a forward translation theorem, not acceptance reflection. -/
theorem closed_translation (wf : WellFormed Γ)
    (h : SourceTyping Γ.naturals Γ.proofs t A) :
    Raw.HasType (fun _ => none)
      (Γ.closeTerm (t.encode Γ.indices Γ.values))
      (Γ.closeType (A.encode Γ.indices)) := close_typed wf (translate h)

end Jihoo.CoreBridge.MixedBridge
