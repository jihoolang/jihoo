import Jihoo.CommonDataErasure
import Jihoo.SizedErasureContext
import Jihoo.SymbolicCommonDataContext
import Jihoo.SymbolicCoreCompaction

/-! Independent environment-only bridge. Data survives CommonData erasure but
becomes ghost under the existing Core projection. The two Core masks therefore
have different domains; neither is the CommonData mask. No heap, ownership,
target execution, or typing rule is changed by this module. -/
namespace Jihoo.CommonDataEnvironmentCompaction
open RecursiveLexicalFields
open CommonDataErasure (Env position)
open SizedErasure (EnvRel rank compactEnv)

/-- The Core mask is derived from values, never from liveness or dead entries. -/
def coreMask (env : List Value) : SizedErasure.Mask :=
  (compactEnv (RecursiveBodyProjection.environment env)).1

def coreEnv (env : List Value) : SizedErasure.Env :=
  (compactEnv (RecursiveBodyProjection.environment env)).2

theorem core_related (env : List Value) :
    EnvRel (coreMask env) (RecursiveBodyProjection.environment env) (coreEnv env) :=
  SizedErasure.compactEnv_related _

/-- Project then compact commutes with CommonData ghost erasure followed by
projection and a second, value-sensitive compaction. -/
theorem project_compact (h : Env slots source target) : coreEnv source = coreEnv target := by
  induction h with
  | nil => rfl
  | @keep slots source target v h ih =>
    cases v <;> simp_all [coreEnv, RecursiveBodyProjection.environment,
      RecursiveBodyProjection.value, compactEnv]
  | erase h ih => exact ih

/-- Relational callers need not use the executable compactor themselves. -/
theorem envRel_canonical (h : EnvRel mask env compacted) :
    compactEnv env = (mask, compacted) := by
  induction h with
  | nil => rfl
  | consKeep v tail ih => cases v <;> simp [compactEnv, SizedErasure.Value.embed, ih]
  | consGhost tail ih => simp [compactEnv, ih]

theorem relational_square (h : Env slots source target)
    (left : EnvRel sourceMask (RecursiveBodyProjection.environment source) leftEnv)
    (right : EnvRel targetMask (RecursiveBodyProjection.environment target) rightEnv) :
    leftEnv = rightEnv := by
  have l := congrArg Prod.snd (envRel_canonical left)
  have r := congrArg Prod.snd (envRel_canonical right)
  exact l.symm.trans ((project_compact h).trans r)

/-- An observable source value necessarily survives CommonData compaction. -/
theorem position_exists (h : Env slots source target)
    (found : source[k]? = some v) (observable : v ≠ .ghost) :
    ∃ j, position slots k = some j := by
  induction h generalizing k with
  | nil => simp at found
  | keep h ih =>
    cases k with
    | zero => exact ⟨0, rfl⟩
    | succ k =>
      obtain ⟨j, hj⟩ := ih found
      exact ⟨j+1, by simp [position, hj]⟩
  | erase h ih =>
    cases k with
    | zero => exact False.elim (observable (Option.some.inj found).symm)
    | succ k => exact ih found

/-- Position in the CommonData runtime followed by residual Core rank equals
Core rank directly in the lexical source. This includes retained Data positions,
although only observable lookups may use the resulting Core index. -/
theorem position_rank (h : Env slots source target) (p : position slots k = some j) :
    rank (coreMask source) k = rank (coreMask target) j := by
  induction h generalizing k j with
  | nil => simp [position] at p
  | @keep slots source target v h ih =>
    cases k with
    | zero => simp [position] at p; subst j; simp
    | succ k =>
      obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp p
      have eq := ih hi
      cases v <;> simpa [coreMask, RecursiveBodyProjection.environment,
        RecursiveBodyProjection.value, compactEnv, rank] using eq
  | erase h ih =>
    cases k with
    | zero => simp [position] at p
    | succ k => exact ih p

/-- The corresponding retained positions have the same Core bit, even when
both bits are false because the CommonData value is Data. -/
theorem position_mask (h : Env slots source target) (p : position slots k = some j) :
    (coreMask target)[j]? = (coreMask source)[k]? := by
  induction h generalizing k j with
  | nil => simp [position] at p
  | @keep slots source target v h ih =>
    cases k with
    | zero =>
      simp [position] at p
      subst j
      cases v <;> rfl
    | succ k =>
      obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp p
      cases v <;> exact ih hi
  | erase h ih =>
    cases k with
    | zero => simp [position] at p
    | succ k => exact ih p

theorem relational_position_rank (h : Env slots source target)
    (left : EnvRel sourceMask (RecursiveBodyProjection.environment source) leftEnv)
    (right : EnvRel targetMask (RecursiveBodyProjection.environment target) rightEnv)
    (p : position slots k = some j) : rank sourceMask k = rank targetMask j := by
  have l := congrArg Prod.fst (envRel_canonical left)
  have r := congrArg Prod.fst (envRel_canonical right)
  change coreMask source = sourceMask at l
  change coreMask target = targetMask at r
  rw [← l, ← r]
  exact position_rank h p

/-- Select lexical entries using the CommonData mask, without changing values
or claiming that selection alone renames dependent index expressions. -/
def select (slots : List Bool) (xs : List α) : List α :=
  match slots, xs with
  | [], _ | _, [] => []
  | true :: rest, x :: xs => x :: select rest xs
  | false :: rest, _ :: xs => select rest xs

theorem select_lookup {xs : List α} {j : Nat} (found : (select slots xs)[j]? = some v) :
    ∃ k, position slots k = some j ∧ xs[k]? = some v := by
  induction slots generalizing xs j with
  | nil => simp [select] at found
  | cons bit slots ih =>
    cases xs with
    | nil => simp [select] at found
    | cons x xs =>
      cases bit with
      | false =>
        obtain ⟨k, hk, hv⟩ := ih found
        exact ⟨k+1, hk, hv⟩
      | true =>
        cases j with
        | zero => exact ⟨0, rfl, found⟩
        | succ j =>
          obtain ⟨k, hk, hv⟩ := ih found
          exact ⟨k+1, by simp [position, hk], hv⟩

/-- The residual Core mask is selected from the lexical Core mask, not reused. -/
theorem select_mask (h : Env slots source target) :
    select slots (coreMask source) = coreMask target := by
  induction h with
  | nil => rfl
  | @keep slots source target v h ih =>
    cases v <;> simp_all [coreMask, RecursiveBodyProjection.environment,
      RecursiveBodyProjection.value, compactEnv, select]
  | erase h ih => exact ih

theorem support_select (h : Env slots source target)
    (supported : SymbolicCoreCompaction.MaskSupports ctx (coreMask source)) :
    SymbolicCoreCompaction.MaskSupports (select slots ctx) (coreMask target) := by
  intro j entry found
  obtain ⟨k, p, original⟩ := select_lookup found
  rw [position_mask h p]
  exact supported k entry original

/-- Generic observable lookup; Data has no inhabitant of this embedding premise. -/
theorem lookup (h : Env slots source target) (p : position slots k = some j)
    {v : SizedErasure.Value}
    (found : (RecursiveBodyProjection.environment source)[k]? = some v.embed) :
    (coreEnv target)[rank (coreMask target) j]? = some v := by
  have result := (core_related source).lookup found
  rw [project_compact h, position_rank h p] at result
  exact result

theorem nat_lookup (h : Env slots source target) (p : position slots k = some j)
    (found : source[k]? = some (.nat n)) :
    (coreEnv target)[rank (coreMask target) j]? = some (.nat n) :=
  lookup h p (by simp [RecursiveBodyProjection.environment, List.getElem?_map,
    found, RecursiveBodyProjection.value, SizedErasure.Value.embed])

theorem scalar_lookup (h : Env slots source target) (p : position slots k = some j)
    (found : source[k]? = some (.scalar n)) :
    (coreEnv target)[rank (coreMask target) j]? = some (.scalar n) :=
  lookup h p (by simp [RecursiveBodyProjection.environment, List.getElem?_map,
    found, RecursiveBodyProjection.value, SizedErasure.Value.embed])

/-- No live-heap premise: even a stale owner alias retains its runtime slot. -/
theorem buffer_lookup (h : Env slots source target) (p : position slots k = some j)
    (found : source[k]? = some (.buffer x)) :
    (coreEnv target)[rank (coreMask target) j]? = some (.owner x) :=
  lookup h p (by simp [RecursiveBodyProjection.environment, List.getElem?_map,
    found, RecursiveBodyProjection.value, SizedErasure.Value.embed])

theorem data_erased {env : List Value} {k : Nat} (found : env[k]? = some (.data ref)) :
    (coreMask env)[k]? = some false := by
  apply (core_related env).ghost_iff.mp
  simp [RecursiveBodyProjection.environment, List.getElem?_map, found,
    RecursiveBodyProjection.value]

theorem ghost_erased {env : List Value} {k : Nat} (found : env[k]? = some .ghost) :
    (coreMask env)[k]? = some false := by
  apply (core_related env).ghost_iff.mp
  simp [RecursiveBodyProjection.environment, List.getElem?_map, found,
    RecursiveBodyProjection.value]

theorem buffer_retained {env : List Value} {k : Nat} (found : env[k]? = some (.buffer x)) :
    (coreMask env)[k]? = some true := by
  apply (core_related env).retained_of_lookup (v := .owner x)
  simp [RecursiveBodyProjection.environment, List.getElem?_map, found,
    RecursiveBodyProjection.value, SizedErasure.Value.embed]

/-- Binder laws expose both the source and residual masks. -/
theorem nat_binder (h : Env slots source target) :
    Env (true :: slots) (.nat n :: source) (.nat n :: target) ∧
    coreMask (.nat n :: source) = true :: coreMask source ∧
    coreEnv (.nat n :: target) = .nat n :: coreEnv target := ⟨.keep h, rfl, rfl⟩

theorem scalar_binder (h : Env slots source target) :
    Env (true :: slots) (.scalar n :: source) (.scalar n :: target) ∧
    coreMask (.scalar n :: source) = true :: coreMask source ∧
    coreEnv (.scalar n :: target) = .scalar n :: coreEnv target := ⟨.keep h, rfl, rfl⟩

theorem owner_binder (h : Env slots source target) :
    Env (true :: slots) (.buffer x :: source) (.buffer x :: target) ∧
    coreMask (.buffer x :: source) = true :: coreMask source ∧
    coreEnv (.buffer x :: target) = .owner x :: coreEnv target := ⟨.keep h, rfl, rfl⟩

theorem data_binder (h : Env slots source target) :
    Env (true :: slots) (.data ref :: source) (.data ref :: target) ∧
    coreMask (.data ref :: source) = false :: coreMask source ∧
    coreEnv (.data ref :: target) = coreEnv target := ⟨.keep h, rfl, rfl⟩

/-- Case's right and left fields survive CommonData and both disappear in Core. -/
theorem case_binders (h : Env slots source target) :
    Env (true :: true :: slots) (bindValues 0 cell source) (bindValues 0 cell target) ∧
    coreMask (bindValues 0 cell source) = false :: false :: coreMask source ∧
    coreEnv (bindValues 0 cell target) = coreEnv target := ⟨h.bind, rfl, rfl⟩

theorem case_position_rank (h : Env slots source target) (p : position slots k = some j) :
    rank (coreMask (bindValues 0 cell source)) (k+2) =
      rank (coreMask (bindValues 0 cell target)) (j+2) := by
  change rank (coreMask source) k = rank (coreMask target) j
  exact position_rank h p

/-- Symbolic support uses existing closing and ownership-sensitive agreement;
Data and dead context entries never justify inventing scalar values. -/
theorem projected_support {owners : List Nat} {retained : List Capability}
    (closing : SymbolicCommonDataContext.Closes ctx closed)
    (agreement : Agrees (retained ++ owners.map Capability.buffer) closed source) :
    SymbolicCoreCompaction.MaskSupports
      (SymbolicCommonDataContext.project retained.length ctx) (coreMask source) :=
  SymbolicCoreCompaction.MaskSupports.of_closing_agrees
    (SymbolicCommonDataContext.projection closing)
    (RecursiveBodyProjection.project_agrees agreement)

theorem projected_support_compacted {owners : List Nat} {retained : List Capability}
    (closing : SymbolicCommonDataContext.Closes ctx closed)
    (agreement : Agrees (retained ++ owners.map Capability.buffer) closed source)
    (h : Env slots source target) :
    SymbolicCoreCompaction.MaskSupports
      (select slots (SymbolicCommonDataContext.project retained.length ctx)) (coreMask target) :=
  support_select h (projected_support closing agreement)

/-- Minimal counterexample to reusing the CommonData runtime mask. -/
theorem common_mask_not_core :
    Env [true] [.data none] [.data none] ∧ coreMask [.data none] ≠ [true] := by
  exact ⟨.keep .nil, by decide⟩

/-- A removed Data slot shifts an actual Buffer index. -/
theorem data_buffer_counterexample :
    position [true, true] 1 = some 1 ∧
    rank (coreMask [.data none, .buffer 7]) 1 = 0 ∧
    coreEnv [.data none, .buffer 7] = [.owner 7] := by decide

end Jihoo.CommonDataEnvironmentCompaction
