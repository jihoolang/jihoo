import Jihoo.NativeArena
import Jihoo.NativePartialRenaming

/-! Direct reference-by-reference arena transformation over every native
constructor. This implementation does not decode a graph into a tree or call
the tree emitter. Depth, total visited-node work and allocation are separate
budgets. Semantic theorems refer to independent tree partial renaming; native
source execution, spans, allocation-order equality and machine code refinement
are not assumed or asserted. -/
namespace Jihoo.NativeKernel.NativeTransform

open NativeArena

def indexLimit : Nat := 2^32

structure Result where
  arena : Arena
  root : Nat
  remaining : Nat
  deriving Repr

structure ChildrenResult where
  arena : Arena
  roots : List Nat
  remaining : Nat
  deriving Repr

def allocateChecked (limit : Nat) (g : Arena) (n : Node) (remaining : Nat) : Option Result :=
  if g.size < limit then some ⟨g.push n, g.size, remaining⟩ else none

theorem allocateChecked_sound (h : allocateChecked limit g n remaining = some result) :
    Prefix g result.arena ∧ result.arena.size ≤ limit ∧
      result.arena[result.root]? = some n ∧ result.remaining = remaining := by
  unfold allocateChecked at h
  split at h
  · cases h
    exact ⟨Prefix.push _ _, by simp; omega, Array.getElem?_push_size, rfl⟩
  · contradiction

/-- Local binders are unchanged variables. Free-variable reuse follows the
caller policy, and an equality check still verifies every reused variable. -/
def liftReuse : Nat → (Nat → Bool) → Nat → Bool
  | 0, reuse => reuse
  | n + 1, reuse => fun
      | 0 => true
      | x + 1 => liftReuse n reuse x

def traverse (f : Nat → Arena → Nat → Nat → Option Result)
    (offset : Nat) (g : Arena) (work : Nat) : List Nat → Option ChildrenResult
  | [] => some ⟨g, [], work⟩
  | root :: refs => do
      let head ← f offset g work root
      let tail ← traverse f (offset + 1) head.arena head.remaining refs
      some ⟨tail.arena, head.root :: tail.roots, tail.remaining⟩

/-- Traverse original references directly and in declaration order. Successful
variable outputs fit u32. Eligible unchanged variables reuse their original
node; every other output is appended with a checked allocation limit. -/
def rename : Nat → Nat → Nat → Arena → Nat → (Nat → Option Nat) →
    (Nat → Bool) → Option Result
  | 0, _, _, _, _, _, _ => none
  | _ + 1, 0, _, _, _, _, _ => none
  | depth + 1, work + 1, limit, g, root, ρ, reuse => do
      if g.size ≤ limit then
        let n ← g[root]?
        match n with
        | .var k =>
            if k < indexLimit then do
              let y ← ρ k
              if y < indexLimit then
                if reuse k = true ∧ y = k then some ⟨g, root, work⟩
                else allocateChecked limit g (.var y) work
              else none
            else none
        | .node op refs =>
            if refs.length = op.arity then do
              let children ← traverse (fun i arena remaining child =>
                rename depth remaining limit arena child
                  (PartialRenaming.lift (op.binders i) ρ)
                  (liftReuse (op.binders i) reuse)) 0 g work refs
              allocateChecked limit children.arena (.node op children.roots) children.remaining
            else none
      else none

def VariablesBounded : Term → Prop
  | .var k => k < indexLimit
  | .node _ args => ∀ t ∈ args, VariablesBounded t

def Correct (ρ : Nat → Option Nat) (g : Arena) (work limit : Nat)
    (t : Term) (result : Result) : Prop :=
  ∃ u, PartialRenaming.rename? ρ t = some u ∧ Prefix g result.arena ∧
    Represents result.arena result.root u ∧ VariablesBounded u ∧
    result.remaining < work ∧ result.arena.size ≤ limit

private theorem traverse_sound {f : Nat → Arena → Nat → Nat → Option Result}
    (step : ∀ offset g work root t result, Represents g root t →
      f offset g work root = some result →
      Correct (PartialRenaming.lift (op.binders offset) ρ) g work limit t result)
    (representation : RepresentsList g refs ts) (cap : g.size ≤ limit)
    (success : traverse f offset g work refs = some result) :
    ∃ us, PartialRenaming.renameArgs? op ρ offset ts = some us ∧
      Prefix g result.arena ∧ RepresentsList result.arena result.roots us ∧
      (∀ u ∈ us, VariablesBounded u) ∧ result.remaining ≤ work ∧ result.arena.size ≤ limit := by
  induction refs generalizing g ts offset work result with
  | nil =>
      cases representation
      simp [traverse] at success
      subst result
      exact ⟨[], by simp [PartialRenaming.renameArgs?], Prefix.refl _, .nil,
        by simp, Nat.le_refl _, cap⟩
  | cons root refs ih =>
      cases representation with
      | cons hr hrs =>
          cases hh : f offset g work root with
          | none => simp [traverse, hh] at success
          | some head =>
              cases ht : traverse f (offset + 1) head.arena head.remaining refs with
              | none => simp [traverse, hh, ht] at success
              | some tail =>
                  simp [traverse, hh, ht] at success
                  subst result
                  obtain ⟨u, hu, hp, rep, bounded, remaining, limit'⟩ := step offset g work root _ head hr hh
                  have tailRep := hrs.frame hp
                  obtain ⟨us, hus, hpt, reps, bounds, rem, lim⟩ := ih tailRep limit' ht
                  refine ⟨u :: us, ?_, hp.trans hpt, .cons (rep.frame hpt) reps, ?_, ?_, lim⟩
                  · simp [PartialRenaming.renameArgs?, hu, hus]
                  · intro x hx
                    rcases List.mem_cons.mp hx with rfl | hx
                    · exact bounded
                    · exact bounds x hx
                  · exact Nat.le_trans rem (Nat.le_of_lt remaining)

private theorem representsList_length (h : RepresentsList g ids ts) : ids.length = ts.length := by
  induction h using RepresentsList.rec (motive_1 := fun _ _ _ => True) with
  | var => trivial
  | node => trivial
  | nil => rfl
  | cons h hs ih ihs => exact congrArg Nat.succ ihs

/-- Direct graph execution implements the independently defined partial tree
renaming on every represented input. Success also certifies no u32 variable
truncation, strict consumption of total work, and the final allocation cap. -/
theorem rename_sound (representation : Represents g root t)
    (success : rename depth work limit g root ρ reuse = some result) :
    Correct ρ g work limit t result := by
  induction depth generalizing work g root t ρ reuse result with
  | zero => simp [rename] at success
  | succ depth ih =>
      cases work with
      | zero => simp [rename] at success
      | succ work =>
          by_cases cap : g.size ≤ limit
          · cases hn : g[root]? with
            | none => simp [rename, cap, hn] at success
            | some n =>
                cases n with
                | var k =>
                    have et : t = .var k := representation.unique (.var hn)
                    subst t
                    by_cases kb : k < indexLimit
                    · cases hy : ρ k with
                      | none => simp [rename, cap, hn, kb, hy] at success
                      | some y =>
                          by_cases yb : y < indexLimit
                          · by_cases keep : reuse k = true ∧ y = k
                            · simp [rename, cap, hn, kb, hy, keep] at success
                              subst result
                              have hyk := keep.2
                              subst y
                              exact ⟨.var k, by simp [PartialRenaming.rename?, hy], Prefix.refl _,
                                .var hn, by simpa [VariablesBounded] using kb, Nat.lt_succ_self _, cap⟩
                            · have allocated : allocateChecked limit g (.var y) work = some result := by
                                simpa [rename, cap, hn, kb, hy, yb, keep] using success
                              obtain ⟨hp, limit', lookup, remaining⟩ := allocateChecked_sound allocated
                              exact ⟨.var y, by simp [PartialRenaming.rename?, hy], hp, .var lookup,
                                by simpa [VariablesBounded] using yb,
                                by rw [remaining]; exact Nat.lt_succ_self _, limit'⟩
                          · simp [rename, cap, hn, kb, hy, yb] at success
                    · simp [rename, cap, hn, kb] at success
                | node op refs =>
                    cases representation with
                    | var lookup => rw [hn] at lookup; cases lookup
                    | node lookup arity represented =>
                        have same := Option.some.inj (hn.symm.trans lookup)
                        cases same
                        let f := fun i arena remaining child => rename depth remaining limit arena child
                          (PartialRenaming.lift (op.binders i) ρ) (liftReuse (op.binders i) reuse)
                        cases hc : traverse f 0 g work refs with
                        | none =>
                            dsimp only [f] at hc
                            simp [rename, cap, hn, arity, hc] at success
                        | some children =>
                            dsimp only [f] at hc
                            have allocated : allocateChecked limit children.arena
                                (.node op children.roots) children.remaining = some result := by
                              simpa [rename, cap, hn, arity, hc] using success
                            have step : ∀ offset arena remaining child v output,
                                Represents arena child v → f offset arena remaining child = some output →
                                Correct (PartialRenaming.lift (op.binders offset) ρ)
                                  arena remaining limit v output := by
                              intro offset arena remaining child v output rep checked
                              exact ih rep checked
                            obtain ⟨us, hu, hp, reps, bounded, remaining, _⟩ :=
                              traverse_sound step represented cap hc
                            obtain ⟨hp', limit', lookup', remaining'⟩ := allocateChecked_sound allocated
                            have outArity : children.roots.length = op.arity :=
                              (representsList_length reps).trans
                                ((PartialRenaming.renameArgs?_length hu).trans
                                  ((representsList_length represented).symm.trans arity))
                            exact ⟨.node op us, by simp [PartialRenaming.rename?, hu], hp.trans hp',
                              .node lookup' outArity (reps.frame hp'),
                              by simpa only [VariablesBounded] using bounded,
                              by rw [remaining']; exact Nat.lt_succ_of_le remaining, limit'⟩
          · simp [rename, cap] at success

theorem rename_frame (representation : Represents g root t)
    (success : rename depth work limit g root ρ reuse = some result)
    (old : decode oldFuel g oldRoot = some oldTerm) :
    decode oldFuel result.arena oldRoot = some oldTerm := by
  obtain ⟨_, _, hp, _⟩ := rename_sound representation success
  exact decode_frame_exact old hp

theorem rename_decodes (input : decode inputFuel g root = some t)
    (success : rename depth work limit g root ρ reuse = some result) :
    ∃ u bound, PartialRenaming.rename? ρ t = some u ∧
      (∀ fuel, bound ≤ fuel → decode fuel result.arena result.root = some u) ∧
      Prefix g result.arena ∧ VariablesBounded u ∧
      result.remaining < work ∧ result.arena.size ≤ limit := by
  obtain ⟨u, hu, hp, rep, bounded, remaining, cap⟩ := rename_sound (decode_sound input) success
  obtain ⟨bound, complete⟩ := rep.decode_complete
  exact ⟨u, bound, hu, complete, hp, bounded, remaining, cap⟩

theorem lift_total (n : Nat) (ρ : Nat → Nat) :
    PartialRenaming.lift n (fun x => some (ρ x)) = fun x => some (liftRenaming n ρ x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext x
      cases x <;> simp [PartialRenaming.lift, PartialRenaming.liftOne,
        liftRenaming, Indexed.liftRenaming, ih]

theorem rename?_total (t : Term) (ρ : Nat → Nat) :
    PartialRenaming.rename? (fun x => some (ρ x)) t = some (t.rename ρ) := by
  induction t using Term.rec
    (motive_2 := fun args => ∀ op ρ offset,
      PartialRenaming.renameArgs? op (fun x => some (ρ x)) offset args =
        some (renameArgs op ρ offset args)) generalizing ρ with
  | var => simp [PartialRenaming.rename?, Term.rename]
  | node op args ih => simp [PartialRenaming.rename?, Term.rename, ih]
  | nil => simp [PartialRenaming.renameArgs?, renameArgs]
  | cons t ts iht ihts =>
      rename_i op ρ offset
      simp [PartialRenaming.renameArgs?, renameArgs, lift_total, iht, ihts]

def shiftIndex (delta : Int) (cutoff : Nat) : Nat → Option Nat :=
  if 0 ≤ delta then fun x => some (PartialRenaming.raiseIndex cutoff delta.toNat x)
  else PartialRenaming.lowerIndex cutoff (-delta).toNat

theorem shiftIndex_semantics (delta : Int) (cutoff : Nat) (t : Term) :
    PartialRenaming.rename? (shiftIndex delta cutoff) t = PartialRenaming.shift delta cutoff t := by
  by_cases positive : 0 ≤ delta
  · simp [shiftIndex, PartialRenaming.shift, positive, rename?_total]
  · simp [shiftIndex, PartialRenaming.shift, positive, PartialRenaming.lower]

/-- Sufficient guards for native cutoff increments and signed addition to avoid
machine overflow. Variable outputs are separately checked against u32 before
allocation. The guards intentionally reject some mathematically valid inputs. -/
def MachineSafe (depth cutoff : Nat) (delta : Int) : Prop :=
  cutoff + depth < indexLimit ∧ -(2^63 : Int) ≤ delta ∧
    delta + (indexLimit : Int) ≤ 2^63

instance : Decidable (MachineSafe depth cutoff delta) := by unfold MachineSafe; infer_instance

theorem MachineSafe.addition (safe : MachineSafe depth cutoff delta) (bound : k < indexLimit) :
    -(2^63 : Int) ≤ (k : Int) + delta ∧ (k : Int) + delta < 2^63 := by
  obtain ⟨_, lower, upper⟩ := safe
  constructor <;> omega

theorem MachineSafe.cutoff_bound (safe : MachineSafe depth cutoff delta) (visited : binders ≤ depth) :
    cutoff + binders < indexLimit := by
  have limit := safe.1
  omega

def shift (depth work limit : Nat) (g : Arena) (root : Nat) (delta : Int) (cutoff : Nat) :
    Option Result :=
  if MachineSafe depth cutoff delta then
    rename depth work limit g root (shiftIndex delta cutoff) (fun x => decide (x < cutoff))
  else none

theorem shift_correct (representation : Represents g root t)
    (success : shift depth work limit g root delta cutoff = some result) :
    MachineSafe depth cutoff delta ∧ Correct (shiftIndex delta cutoff) g work limit t result := by
  unfold shift at success
  split at success
  · exact ⟨‹_›, rename_sound representation success⟩
  · contradiction

theorem shift_sound (representation : Represents g root t)
    (success : shift depth work limit g root delta cutoff = some result) :
    ∃ u, PartialRenaming.shift delta cutoff t = some u ∧ Prefix g result.arena ∧
      Represents result.arena result.root u ∧ VariablesBounded u ∧
      result.remaining < work ∧ result.arena.size ≤ limit := by
  obtain ⟨_, u, hu, hp, hr, bounded, remaining, cap⟩ := shift_correct representation success
  rw [shiftIndex_semantics] at hu
  exact ⟨u, hu, hp, hr, bounded, remaining, cap⟩

theorem shift_frame (representation : Represents g root t)
    (success : shift depth work limit g root delta cutoff = some result)
    (old : decode oldFuel g oldRoot = some oldTerm) :
    decode oldFuel result.arena oldRoot = some oldTerm := by
  obtain ⟨_, _, hp, _⟩ := shift_sound representation success
  exact decode_frame_exact old hp

theorem shift_negative_reweakens (representation : Represents g root t) (negative : delta < 0)
    (success : shift depth work limit g root delta cutoff = some result) :
    ∃ u, Represents result.arena result.root u ∧
      u.rename (PartialRenaming.raiseIndex cutoff (-delta).toNat) = t := by
  obtain ⟨u, hu, _, hr, _⟩ := shift_sound representation success
  exact ⟨u, hr, PartialRenaming.shift_negative_reweakens negative hu⟩

theorem shift_negative_scoped (representation : Represents g root t) (negative : delta < 0)
    (scope : t.Scoped (scopeDepth + (-delta).toNat)) (cutoff_bound : cutoff ≤ scopeDepth)
    (success : shift depth work limit g root delta cutoff = some result) :
    ∃ u, Represents result.arena result.root u ∧ u.Scoped scopeDepth := by
  obtain ⟨u, hu, _, hr, _⟩ := shift_sound representation success
  exact ⟨u, hr, PartialRenaming.shift_negative_scoped negative scope cutoff_bound hu⟩

@[simp] theorem rename_zero_depth : rename 0 work limit g root ρ reuse = none := rfl

@[simp] theorem rename_zero_work : rename depth 0 limit g root ρ reuse = none := by
  cases depth <;> rfl

end Jihoo.NativeKernel.NativeTransform
