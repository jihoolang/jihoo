import Jihoo.NativeArena
import Jihoo.NativePartialRenaming

/-! Tree-mediated append-only arena adapters for signed partial shifts and
native no-removal rewrites. Exact tree meaning and old-prefix preservation are
proved; native allocation order, index truncation and work budgets are separate. -/
namespace Jihoo.NativeKernel.NativeArenaPartial

open NativeArena

def transform (fuel : Nat) (g : Arena) (root : Nat) (f : Term → Option Term) :
    Option (Arena × Nat) := do
  let t ← decode fuel g root
  let u ← f t
  some (emit u g)

def shift (fuel : Nat) (g : Arena) (root : Nat) (delta : Int) (cutoff : Nat) :
    Option (Arena × Nat) := transform fuel g root (PartialRenaming.shift delta cutoff)

def lower (fuel : Nat) (g : Arena) (root cutoff amount : Nat) : Option (Arena × Nat) :=
  transform fuel g root (PartialRenaming.lower cutoff amount)

def rewrite (fuel : Nat) (g : Arena) (root target value : Nat) : Option (Arena × Nat) := do
  let a ← decode fuel g value
  transform fuel g root (fun t => some (PartialRenaming.rewrite target a t))

theorem transform_sound {fuel root out : Nat} {g after : Arena} {f : Term → Option Term}
    (h : transform fuel g root f = some (after, out))
    (wf : ∀ t u, t.WellFormed → f t = some u → u.WellFormed) :
    ∃ t u, decode fuel g root = some t ∧ f t = some u ∧
      Prefix g after ∧ Represents after out u := by
  cases ht : decode fuel g root with
  | none => simp [transform, ht] at h
  | some t =>
      cases hu : f t with
      | none => simp [transform, ht, hu] at h
      | some u =>
          have he : emit u g = (after, out) := by simpa [transform, ht, hu] using h
          have hp := emit_prefix u g
          have hr := emit_sound (wf t u (decode_wellFormed ht) hu) g
          rw [he] at hp hr
          exact ⟨t, u, rfl, hu, hp, hr⟩

theorem shift_sound {fuel root out cutoff : Nat} {delta : Int} {g after : Arena}
    (h : shift fuel g root delta cutoff = some (after, out)) :
    ∃ t u, decode fuel g root = some t ∧ PartialRenaming.shift delta cutoff t = some u ∧
      Prefix g after ∧ Represents after out u :=
  transform_sound h (fun _ _ wf success => PartialRenaming.shift_wellFormed wf success)

theorem lower_sound {fuel root out cutoff amount : Nat} {g after : Arena}
    (h : lower fuel g root cutoff amount = some (after, out)) :
    ∃ t u, decode fuel g root = some t ∧ PartialRenaming.lower cutoff amount t = some u ∧
      Prefix g after ∧ Represents after out u :=
  transform_sound h (fun _ _ wf success => PartialRenaming.lower_wellFormed wf success)

theorem lower_reweakens {fuel root out cutoff amount : Nat} {g after : Arena}
    (h : lower fuel g root cutoff amount = some (after, out)) :
    ∃ t u, decode fuel g root = some t ∧ Represents after out u ∧
      u.rename (PartialRenaming.raiseIndex cutoff amount) = t := by
  obtain ⟨t, u, ht, hu, _, hr⟩ := lower_sound h
  exact ⟨t, u, ht, hr, PartialRenaming.lower_reweakens hu⟩

theorem lower_scoped {fuel root out cutoff amount depth : Nat} {g after : Arena} {t : Term}
    (h : lower fuel g root cutoff amount = some (after, out))
    (ht : decode fuel g root = some t) (hs : t.Scoped (depth + amount)) (hc : cutoff ≤ depth) :
    ∃ u, Represents after out u ∧ u.Scoped depth := by
  obtain ⟨t', u, ht', hu, _, hr⟩ := lower_sound h
  have et : t' = t := Option.some.inj (ht'.symm.trans ht)
  subst t'
  exact ⟨u, hr, PartialRenaming.lower_scoped hs hc hu⟩

theorem rewrite_sound {fuel root out target value : Nat} {g after : Arena}
    (h : rewrite fuel g root target value = some (after, out)) :
    ∃ t a, decode fuel g root = some t ∧ decode fuel g value = some a ∧
      Prefix g after ∧ Represents after out (t.subst (PartialRenaming.replaceIndex target a)) := by
  cases ha : decode fuel g value with
  | none => simp [rewrite, ha] at h
  | some a =>
      have ht : transform fuel g root (fun t => some (PartialRenaming.rewrite target a t)) =
          some (after, out) := by simpa [rewrite, ha] using h
      obtain ⟨t, u, ht, hu, hp, hr⟩ := transform_sound ht
        (fun _ _ wf success => by cases success; exact PartialRenaming.rewrite_wellFormed wf (decode_wellFormed ha))
      cases hu
      rw [PartialRenaming.rewrite_eq_subst] at hr
      exact ⟨t, a, ht, rfl, hp, hr⟩

theorem rewrite_scoped {fuel root out target value depth : Nat} {g after : Arena} {t a : Term}
    (h : rewrite fuel g root target value = some (after, out))
    (ht : decode fuel g root = some t) (ha : decode fuel g value = some a)
    (hs : t.Scoped depth) (hv : a.Scoped depth) :
    ∃ u, Represents after out u ∧ u.Scoped depth := by
  obtain ⟨t', a', ht', ha', _, hr⟩ := rewrite_sound h
  have et : t' = t := Option.some.inj (ht'.symm.trans ht)
  have ea : a' = a := Option.some.inj (ha'.symm.trans ha)
  subst t'; subst a'
  refine ⟨_, hr, ?_⟩
  simpa only [PartialRenaming.rewrite_eq_subst] using PartialRenaming.rewrite_scoped hs hv (target := target)

theorem lower_frame {fuel root out cutoff amount oldFuel old : Nat} {g after : Arena} {t : Term}
    (h : lower fuel g root cutoff amount = some (after, out))
    (hold : decode oldFuel g old = some t) : decode oldFuel after old = some t := by
  obtain ⟨_, _, _, _, hp, _⟩ := lower_sound h
  exact decode_frame_exact hold hp

theorem shift_frame {fuel root out cutoff oldFuel old : Nat} {delta : Int}
    {g after : Arena} {t : Term}
    (h : shift fuel g root delta cutoff = some (after, out))
    (hold : decode oldFuel g old = some t) : decode oldFuel after old = some t := by
  obtain ⟨_, _, _, _, hp, _⟩ := shift_sound h
  exact decode_frame_exact hold hp

theorem rewrite_frame {fuel root out target value oldFuel old : Nat}
    {g after : Arena} {t : Term}
    (h : rewrite fuel g root target value = some (after, out))
    (hold : decode oldFuel g old = some t) : decode oldFuel after old = some t := by
  obtain ⟨_, _, _, _, hp, _⟩ := rewrite_sound h
  exact decode_frame_exact hold hp

theorem transform_backward {fuel root out : Nat} {g after : Arena} {f : Term → Option Term}
    (h : transform fuel g root f = some (after, out)) (hg : Backward g) : Backward after := by
  cases ht : decode fuel g root with
  | none => simp [transform, ht] at h
  | some t =>
      cases hu : f t with
      | none => simp [transform, ht, hu] at h
      | some u =>
          have he : emit u g = (after, out) := by simpa [transform, ht, hu] using h
          have hb := emit_backward u hg
          rwa [he] at hb

theorem lower_backward {fuel root out cutoff amount : Nat} {g after : Arena}
    (h : lower fuel g root cutoff amount = some (after, out)) (hg : Backward g) :
    Backward after := transform_backward h hg

theorem shift_backward {fuel root out cutoff : Nat} {delta : Int} {g after : Arena}
    (h : shift fuel g root delta cutoff = some (after, out)) (hg : Backward g) :
    Backward after := transform_backward h hg

theorem rewrite_backward {fuel root out target value : Nat} {g after : Arena}
    (h : rewrite fuel g root target value = some (after, out)) (hg : Backward g) :
    Backward after := by
  cases ha : decode fuel g value with
  | none => simp [rewrite, ha] at h
  | some a =>
      apply transform_backward (fuel := fuel) (root := root) (out := out)
        (f := fun t => some (PartialRenaming.rewrite target a t)) _ hg
      simpa [rewrite, ha] using h

end Jihoo.NativeKernel.NativeArenaPartial
