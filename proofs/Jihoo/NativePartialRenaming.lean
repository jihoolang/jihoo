import Jihoo.NativeSubstitution

/-! Partial scope removal and no-removal rewriting for the entire native term
syntax. Failure is explicit: a reference into a removed variable block cannot
be silently clamped to zero. Machine integer limits and mutable native execution
are separate from these binding-aware tree definitions. -/
namespace Jihoo.NativeKernel.PartialRenaming

def liftOne (ρ : Nat → Option Nat) : Nat → Option Nat
  | 0 => some 0
  | x + 1 => (ρ x).map Nat.succ

def lift : Nat → (Nat → Option Nat) → Nat → Option Nat
  | 0, ρ => ρ
  | n + 1, ρ => liftOne (lift n ρ)

mutual
  def rename? (ρ : Nat → Option Nat) : Term → Option Term
    | .var x => (ρ x).map Term.var
    | .node op args => (renameArgs? op ρ 0 args).map (Term.node op)
  termination_by t => sizeOf t
  decreasing_by all_goals simp_wf; all_goals omega

  def renameArgs? (op : Op) (ρ : Nat → Option Nat) (offset : Nat) :
      List Term → Option (List Term)
    | [] => some []
    | t :: ts => do
        let t' ← rename? (lift (op.binders offset) ρ) t
        let ts' ← renameArgs? op ρ (offset + 1) ts
        some (t' :: ts')
  termination_by ts => sizeOf ts
  decreasing_by all_goals simp_wf; all_goals omega
end

def Inverse (ρ : Nat → Option Nat) (restore : Nat → Nat) : Prop :=
  ∀ x y, ρ x = some y → restore y = x

theorem Inverse.underBinders (h : Inverse ρ restore) (n : Nat) :
    Inverse (lift n ρ) (liftRenaming n restore) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro x y success
      cases x with
      | zero =>
          simp only [lift, liftOne, Option.some.injEq] at success
          subst y
          rfl
      | succ x =>
          cases hr : lift n ρ x with
          | none => simp [lift, liftOne, hr] at success
          | some z =>
              simp only [lift, liftOne, hr, Option.map_some, Option.some.injEq] at success
              subst y
              simpa only [liftRenaming, Indexed.liftRenaming] using congrArg Nat.succ (ih x z hr)

/-- A successful partial renaming is undone by any pointwise inverse. This
follows every binding edge, including both branch evidence binders. -/
theorem rename?_restores (t : Term) {ρ : Nat → Option Nat} {restore : Nat → Nat}
    (inverse : Inverse ρ restore) (success : rename? ρ t = some u) :
    u.rename restore = t := by
  induction t using Term.rec
    (motive_2 := fun ts => ∀ op offset ρ restore us,
      Inverse ρ restore → renameArgs? op ρ offset ts = some us →
      renameArgs op restore offset us = ts) generalizing ρ restore u with
  | var x =>
      cases hr : ρ x with
      | none => simp [rename?, hr] at success
      | some y =>
          simp [rename?, hr] at success
          subst u
          simp only [Term.rename, inverse x y hr]
  | node op args ih =>
      cases ha : renameArgs? op ρ 0 args with
      | none => simp [rename?, ha] at success
      | some us =>
          simp [rename?, ha] at success
          subst u
          simp only [Term.rename, ih op 0 ρ restore us inverse ha]
  | nil =>
      rename_i op offset ρ restore us inverse success
      simp only [renameArgs?, Option.some.injEq] at success
      subst us
      simp [renameArgs]
  | cons t ts iht ihts =>
      rename_i op offset ρ restore us inverse success
      cases ht : rename? (lift (op.binders offset) ρ) t with
      | none => simp [renameArgs?, ht] at success
      | some u =>
          cases hs : renameArgs? op ρ (offset + 1) ts with
          | none => simp [renameArgs?, ht, hs] at success
          | some rest =>
              simp only [renameArgs?, ht, hs, bind, Option.bind,
                Option.some.injEq] at success
              subst us
              simp only [renameArgs, iht (inverse.underBinders _) ht,
                ihts op (offset + 1) ρ restore rest inverse hs]

def Within (source target : Nat) (ρ : Nat → Option Nat) : Prop :=
  ∀ x y, x < source → ρ x = some y → y < target

theorem Within.underBinders (h : Within source target ρ) (n : Nat) :
    Within (source + n) (target + n) (lift n ρ) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro x y hx success
      cases x with
      | zero =>
          simp only [lift, liftOne, Option.some.injEq] at success
          subst y
          omega
      | succ x =>
          cases hr : lift n ρ x with
          | none => simp [lift, liftOne, hr] at success
          | some z =>
              simp only [lift, liftOne, hr, Option.map_some, Option.some.injEq] at success
              subst y
              have bound := ih x z (by omega) hr
              omega

theorem renameArgs?_length (h : renameArgs? op ρ offset ts = some us) :
    us.length = ts.length := by
  induction ts generalizing offset us with
  | nil => simp [renameArgs?] at h; subst us; rfl
  | cons t ts ih =>
      cases ht : rename? (lift (op.binders offset) ρ) t with
      | none => simp [renameArgs?, ht] at h
      | some u =>
          cases hs : renameArgs? op ρ (offset + 1) ts with
          | none => simp [renameArgs?, ht, hs] at h
          | some rest =>
              simp [renameArgs?, ht, hs] at h
              subst us
              simpa only [List.length_cons] using congrArg Nat.succ (ih hs)

/-- A selected output child comes from the same input child position and its
own correctly lifted partial renaming. -/
theorem renameArgs?_get (h : renameArgs? op ρ offset ts = some us)
    (selected : us[i]? = some u) :
    ∃ t, ts[i]? = some t ∧ rename? (lift (op.binders (offset + i)) ρ) t = some u := by
  induction ts generalizing offset us i with
  | nil => simp [renameArgs?] at h; subst us; simp at selected
  | cons t ts ih =>
      cases ht : rename? (lift (op.binders offset) ρ) t with
      | none => simp [renameArgs?, ht] at h
      | some v =>
          cases hs : renameArgs? op ρ (offset + 1) ts with
          | none => simp [renameArgs?, ht, hs] at h
          | some rest =>
              simp [renameArgs?, ht, hs] at h
              subst us
              cases i with
              | zero =>
                  simp at selected
                  subst u
                  exact ⟨t, rfl, ht⟩
              | succ i =>
                  have tail := ih hs (by simpa using selected)
                  simpa only [List.getElem?_cons_succ, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using tail

theorem rename?_scoped (ht : t.Scoped source) (hρ : Within source target ρ)
    (success : rename? ρ t = some u) : u.Scoped target := by
  induction ht generalizing target ρ u with
  | @var x depth hx =>
      cases hr : ρ x with
      | none => simp [rename?, hr] at success
      | some y =>
          simp [rename?, hr] at success
          subst u
          exact .var (hρ _ _ hx hr)
  | @node args source op hs ih =>
      cases ha : renameArgs? op ρ 0 args with
      | none => simp [rename?, ha] at success
      | some us =>
          simp [rename?, ha] at success
          subst u
          apply Term.Scoped.node
          intro i u selected
          obtain ⟨t, lookup, renamed⟩ := renameArgs?_get ha selected
          exact ih i t lookup (hρ.underBinders (op.binders i)) (by simpa only [Nat.zero_add] using renamed)

theorem rename?_wellFormed (ht : t.WellFormed) (success : rename? ρ t = some u) :
    u.WellFormed := by
  induction t using Term.rec
    (motive_2 := fun ts => ∀ op offset ρ us, (∀ t ∈ ts, t.WellFormed) →
      renameArgs? op ρ offset ts = some us → ∀ u ∈ us, u.WellFormed) generalizing ρ u with
  | var x =>
      cases hr : ρ x with
      | none => simp [rename?, hr] at success
      | some y => simp [rename?, hr] at success; subst u; simp [Term.WellFormed]
  | node op args ih =>
      simp only [Term.WellFormed] at ht
      cases ha : renameArgs? op ρ 0 args with
      | none => simp [rename?, ha] at success
      | some us =>
          simp [rename?, ha] at success
          subst u
          simp only [Term.WellFormed]
          exact ⟨(renameArgs?_length ha).trans ht.1, ih op 0 ρ us ht.2 ha⟩
  | nil =>
      rename_i op offset ρ us wf h u member
      simp [renameArgs?] at h
      subst us
      simp at member
  | cons t ts iht ihts =>
      rename_i op offset ρ us wf h x hx
      cases ht : rename? (lift (op.binders offset) ρ) t with
      | none => simp [renameArgs?, ht] at h
      | some v =>
          cases hs : renameArgs? op ρ (offset + 1) ts with
          | none => simp [renameArgs?, ht, hs] at h
          | some rest =>
              simp [renameArgs?, ht, hs] at h
              subst us
              rcases List.mem_cons.mp hx with rfl | hx
              · exact iht (wf t (by simp)) ht
              · exact ihts op (offset + 1) ρ rest (fun y hy => wf y (by simp [hy])) hs x hx

def raiseIndex (cutoff amount x : Nat) : Nat :=
  if x < cutoff then x else x + amount

def lowerIndex (cutoff amount x : Nat) : Option Nat :=
  if x < cutoff then some x
  else if cutoff + amount ≤ x then some (x - amount) else none

/-- Remove an arbitrary block of variables, failing when a term refers to it. -/
def lower (cutoff amount : Nat) (t : Term) : Option Term :=
  rename? (lowerIndex cutoff amount) t

theorem lowerIndex_inverse (cutoff amount : Nat) :
    Inverse (lowerIndex cutoff amount) (raiseIndex cutoff amount) := by
  intro x y h
  unfold lowerIndex at h
  split at h
  · cases h; simp [raiseIndex, ‹x < cutoff›]
  · split at h
    · cases h
      have bound : cutoff ≤ x - amount := by omega
      simp [raiseIndex, show ¬x - amount < cutoff from by omega]
      omega
    · contradiction

theorem lowerIndex_within (cutoff amount depth : Nat) (hc : cutoff ≤ depth) :
    Within (depth + amount) depth (lowerIndex cutoff amount) := by
  intro x y hx h
  unfold lowerIndex at h
  split at h
  · cases h; omega
  · split at h
    · cases h; omega
    · contradiction

theorem lower_reweakens (success : lower cutoff amount t = some u) :
    u.rename (raiseIndex cutoff amount) = t :=
  rename?_restores t (lowerIndex_inverse cutoff amount) success

theorem lower_scoped (ht : t.Scoped (depth + amount)) (hc : cutoff ≤ depth)
    (success : lower cutoff amount t = some u) : u.Scoped depth :=
  rename?_scoped ht (lowerIndex_within cutoff amount depth hc) success

theorem lower_wellFormed (ht : t.WellFormed) (success : lower cutoff amount t = some u) :
    u.WellFormed := rename?_wellFormed ht success

/-- A reference to the removed slot is rejected, even at zero. -/
theorem lower_removed_var (inside : cutoff ≤ x ∧ x < cutoff + amount) :
    lower cutoff amount (.var x) = none := by
  simp [lower, rename?, lowerIndex, show ¬x < cutoff from by omega,
    show ¬cutoff + amount ≤ x from by omega]

/-- Lifting scope removal is exactly the native cutoff increment. -/
theorem lift_lowerIndex (cutoff amount n : Nat) :
    lift n (lowerIndex cutoff amount) = lowerIndex (cutoff + n) amount := by
  induction n with
  | zero => simp [lift]
  | succ n ih =>
      funext x
      cases x with
      | zero =>
          simp [lift, liftOne, lowerIndex, show 0 < cutoff + (n + 1) from by omega]
      | succ x =>
          simp only [lift, liftOne, ih]
          by_cases hs : x < cutoff + n
          · simp [lowerIndex, hs, show x + 1 < cutoff + (n + 1) from by omega]
          · by_cases hl : cutoff + n + amount ≤ x
            · simp [lowerIndex, hs, hl,
                show ¬x + 1 < cutoff + (n + 1) from by omega,
                show cutoff + (n + 1) + amount ≤ x + 1 from by omega]
              omega
            · simp [lowerIndex, hs, hl,
                show ¬x + 1 < cutoff + (n + 1) from by omega,
                show ¬cutoff + (n + 1) + amount ≤ x + 1 from by omega]

/-- Signed shifts use partial scope removal for every negative amount. -/
def shift (delta : Int) (cutoff : Nat) (t : Term) : Option Term :=
  if 0 ≤ delta then some (t.rename (raiseIndex cutoff delta.toNat))
  else lower cutoff (-delta).toNat t

theorem shift_negative (negative : delta < 0) :
    shift delta cutoff t = lower cutoff (-delta).toNat t := by
  simp [shift, show ¬0 ≤ delta from by omega]

theorem shift_nonnegative (positive : 0 ≤ delta) :
    shift delta cutoff t = some (t.rename (raiseIndex cutoff delta.toNat)) := by
  simp [shift, positive]

theorem shift_wellFormed (ht : t.WellFormed) (success : shift delta cutoff t = some u) :
    u.WellFormed := by
  unfold shift at success
  split at success
  · cases success; exact ht.rename _
  · exact lower_wellFormed ht success

theorem shift_negative_reweakens (negative : delta < 0)
    (success : shift delta cutoff t = some u) :
    u.rename (raiseIndex cutoff (-delta).toNat) = t := by
  rw [shift_negative negative] at success
  exact lower_reweakens success

theorem shift_negative_scoped (negative : delta < 0)
    (ht : t.Scoped (depth + (-delta).toNat)) (hc : cutoff ≤ depth)
    (success : shift delta cutoff t = some u) : u.Scoped depth := by
  rw [shift_negative negative] at success
  exact lower_scoped ht hc success

def replaceIndex (target : Nat) (value : Term) (x : Nat) : Term :=
  if x = target then value else .var x

theorem liftSub_add (first second : Nat) (σ : Nat → Term) :
    liftSub second (liftSub first σ) = liftSub (first + second) σ := by
  induction second with
  | zero => simp [liftSub]
  | succ n ih =>
      change liftSubOne (liftSub n (liftSub first σ)) = liftSubOne (liftSub (first + n) σ)
      exact congrArg liftSubOne ih

/-- Rewrite keeps all binders. Under n local binders its replacement shifts
by n, while every non-target variable retains its exact index. -/
theorem liftSub_replaceIndex (target n : Nat) (value : Term) :
    liftSub n (replaceIndex target value) =
      replaceIndex (target + n) (value.rename (fun x => x + n)) := by
  induction n with
  | zero =>
      simp only [liftSub, Nat.add_zero]
      exact congrArg (replaceIndex target) (Term.rename_id value).symm
  | succ n ih =>
      funext x
      cases x with
      | zero => simp [liftSub, liftSubOne, replaceIndex]
      | succ x =>
          simp only [liftSub, liftSubOne, ih]
          by_cases he : x = target + n
          · subst x
            simp [replaceIndex, Term.rename_comp, Nat.add_assoc]
          · simp [replaceIndex, he, show x + 1 ≠ target + (n + 1) from by omega,
              Term.rename]

mutual
  /-- Direct native-style rewrite: only the selected free variable is replaced.
  Higher indices are not decremented, unlike binder-instantiating substitution. -/
  def rewriteAt (target : Nat) (value : Term) (depth : Nat) : Term → Term
    | .var x => if x = target + depth then value.rename (fun x => x + depth) else .var x
    | .node op args => .node op (rewriteArgsAt op target value depth 0 args)
  termination_by t => sizeOf t
  decreasing_by all_goals simp_wf; all_goals omega

  def rewriteArgsAt (op : Op) (target : Nat) (value : Term) (depth offset : Nat) :
      List Term → List Term
    | [] => []
    | t :: ts => rewriteAt target value (depth + op.binders offset) t ::
        rewriteArgsAt op target value depth (offset + 1) ts
  termination_by ts => sizeOf ts
  decreasing_by all_goals simp_wf; all_goals omega
end

def rewrite (target : Nat) (value t : Term) : Term := rewriteAt target value 0 t

/-- The direct native traversal agrees with simultaneous substitution that
retains all variable slots. The theorem holds for every constructor and depth. -/
theorem rewriteAt_eq_subst (t : Term) (target : Nat) (value : Term) (depth : Nat) :
    rewriteAt target value depth t = t.subst (liftSub depth (replaceIndex target value)) := by
  induction t using Term.rec
    (motive_2 := fun ts => ∀ op target value depth offset,
      rewriteArgsAt op target value depth offset ts =
        substArgs op (liftSub depth (replaceIndex target value)) offset ts)
    generalizing target value depth with
  | var x => simp only [rewriteAt, Term.subst, liftSub_replaceIndex, replaceIndex]
  | node op args ih => simp only [rewriteAt, Term.subst, ih]
  | nil => simp [rewriteArgsAt, substArgs]
  | cons t ts iht ihts =>
      rename_i op target value depth offset
      simp only [rewriteArgsAt, substArgs, iht, ihts, liftSub_add]

theorem rewrite_eq_subst (t : Term) (target : Nat) (value : Term) :
    rewrite target value t = t.subst (replaceIndex target value) := by
  simpa only [rewrite, liftSub] using rewriteAt_eq_subst t target value 0

theorem rewrite_wellFormed (ht : t.WellFormed) (hv : value.WellFormed) :
    (rewrite target value t).WellFormed := by
  rw [rewrite_eq_subst]
  apply ht.subst
  intro x
  unfold replaceIndex
  split
  · exact hv
  · simp [Term.WellFormed]

theorem rewrite_scoped (ht : t.Scoped depth) (hv : value.Scoped depth) :
    (rewrite target value t).Scoped depth := by
  rw [rewrite_eq_subst]
  apply ht.subst
  intro x hx
  unfold replaceIndex
  split
  · exact hv
  · exact .var hx

theorem rewrite_other_var (different : x ≠ target) : rewrite target value (.var x) = .var x := by
  simp [rewrite, rewriteAt, different]

theorem rewrite_target_var : rewrite target value (.var target) = value := by
  simp only [rewrite, rewriteAt, Nat.add_zero, ↓reduceIte]
  exact Term.rename_id value

end Jihoo.NativeKernel.PartialRenaming
