import Jihoo.NativeTyping

/-! Mode facts for the universe-aware native judgment. These are prerequisites
for a mode-sensitive substitution theorem, not an assumption that unrestricted
substitution preserves runtime representation or linear ownership. -/
namespace Jihoo.NativeKernel

/-- Every term checked for code may also be checked for types/evidence. The
converse fails because erased variables are unavailable in code. -/
theorem HasType.ghost (h : HasType ctx mode t T) : HasType ctx true t T := by
  induction h using HasType.rec
    (motive_1 := fun ctx e A s _ => Binder ctx e A s) with
  | intro hA allowed ih => exact .intro ih allowed
  | var lookup readable => exact .var lookup (Or.inl rfl)
  | univ bound => exact .univ bound
  | prop => exact .prop
  | u64 => exact .u64
  | i64 => exact .i64
  | natural bound => exact .natural bound
  | integer lo hi => exact .integer lo hi
  | array hn ih => exact .array ih
  | lt ha hb iha ihb => exact .lt iha ihb
  | eq ha hb iha ihb => exact .eq iha ihb
  | pi hA hB ihA ihB => exact .pi ihA ihB
  | lam hA hb ihA ihb => exact .lam ihA ihb
  | app hf ha allowed ihf iha => exact .app ihf iha (Or.inl rfl)
  | uadd ha hb iha ihb => exact .uadd iha ihb
  | usub ha hb hp iha ihb ihp => exact .usub iha ihb ihp
  | refl ha ih => exact .refl ih
  | zeroLe ha ih => exact .zeroLe ih
  | decide ha hb hab => exact .decide ha hb hab
  | decideConverted ha hb ca cb hma hnb hmn iha ihb =>
      exact .decideConverted iha ihb ca cb hma hnb hmn
  | elements size bound hs ih => exact .elements size bound ih
  | index ha hi hp iha ihi ihp => exact .index iha ihi ihp
  | arith ha hb iha ihb => exact .arith iha ihb
  | strict ha hb iha ihb => exact .strict iha ihb
  | ltAdd ha hb hc hp iha ihb ihc ihp => exact .ltAdd iha ihb ihc ihp
  | ltCancel ha hb hc hp iha ihb ihc ihp => exact .ltCancel iha ihb ihc ihp
  | ltLe ha hb hc hp hq iha ihb ihc ihp ihq => exact .ltLe iha ihb ihc ihp ihq
  | transport hf he hp ihf ihe ihp => exact .transport ihf ihe ihp
  | refine hp ih => exact .refine ih
  | pack hp ha hq ihp iha ihq => exact .pack ihp iha ihq
  | witness hs ih => exact .witness ih
  | proof hs ih => exact .proof ih
  | ifLt ha hb hy hn iha ihb ihy ihn => exact .ifLt iha ihb ihy ihn
  | ifEq ha hb hy hn iha ihb ihy ihn => exact .ifEq iha ihb ihy ihn
  | absurd hT hp allowed ihT ihp => exact .absurd ihT ihp (Or.inl rfl)
  | foldI64 hn hi hb allowed ihn ihi ihb => exact .foldI64 ihn ihi ihb (Or.inl rfl)
  | loop hm motivePolicy hn hi hb bodyPolicy ihm ihn ihi ihb =>
      exact .loop ihm (Or.inl rfl) (by simpa using ihn) (by simpa using ihi) (by simpa using ihb) (Or.inl rfl)
  | convert ht conv ih => exact .convert ih conv

/-- Variable inversion retains readability through arbitrary type conversion. -/
theorem HasType.variable_readable (h : HasType ctx mode t T) :
    ∀ x, t = .var x → ∃ b, lookup ctx x = some b ∧ (mode = true ∨ b.erased = false) := by
  induction h using HasType.rec (motive_1 := fun _ _ _ _ _ => True) with
  | var hx readable =>
      intro x ht
      cases ht
      exact ⟨_, hx, readable⟩
  | convert ht conv ih => exact ih
  | _ => first | trivial | (intro x ht; cases ht)

/-- Type conversion cannot bypass an erased variable's code-mode exclusion. -/
theorem erased_variable_unavailable {ctx : Context} {x : Nat} {b : Binding}
    (hx : lookup ctx x = some b) (erased : b.erased = true) :
    ∀ T, ¬ HasType ctx false (.var x) T := by
  intro T typed
  obtain ⟨b', hx', readable⟩ := typed.variable_readable x rfl
  have same : b' = b := Option.some.inj (hx'.symm.trans hx)
  subst b'
  simp [erased] at readable

/-- Constructor arities are enforced for the actual term, even under type
conversion. No well-formedness of a caller-supplied result type is presumed. -/
theorem HasType.term_wellFormed (h : HasType ctx mode t T) : t.WellFormed := by
  induction h using HasType.rec (motive_1 := fun _ _ A _ _ => A.WellFormed) <;>
    simp_all [Term.WellFormed, Op.arity]

theorem lookup_bound {ctx : Context} {x : Nat} {b : Binding}
    (h : lookup ctx x = some b) : x < ctx.length := by
  induction ctx generalizing x b with
  | nil => simp [lookup] at h
  | cons head ctx ih =>
      cases x with
      | zero => simp
      | succ x =>
          obtain ⟨old, hx, _⟩ := Option.map_eq_some_iff.mp h
          have inside := ih hx
          simp only [List.length_cons]
          omega

private theorem scoped_node {depth : Nat} {op : Op} {args : List Term}
    (h0 : ∀ i, op.binders i = 0) (hs : ∀ t ∈ args, t.Scoped depth) :
    (Term.node op args).Scoped depth := by
  apply Term.Scoped.node
  intro i t ht
  rw [h0 i, Nat.add_zero]
  exact hs t (List.mem_of_getElem? ht)

private theorem scoped_binder {depth : Nat} {op : Op} {A B : Term}
    (h0 : op.binders 0 = 0) (h1 : op.binders 1 = 1)
    (hA : A.Scoped depth) (hB : B.Scoped (depth + 1)) :
    (Term.node op [A, B]).Scoped depth := by
  apply Term.Scoped.node
  intro i t ht
  cases i with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
      subst t
      simpa only [h0, Nat.add_zero] using hA
  | succ i =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at ht
          subst t
          simpa only [h1] using hB
      | succ i => simp at ht


private theorem scoped_branch {depth : Nat} {op : Op} {a b yes no : Term}
    (h0 : op.binders 0 = 0) (h1 : op.binders 1 = 0)
    (h2 : op.binders 2 = 1) (h3 : op.binders 3 = 0)
    (ha : a.Scoped depth) (hb : b.Scoped depth)
    (hy : yes.Scoped (depth+1)) (hn : no.Scoped depth) :
    (Term.node op [a,b,yes,no]).Scoped depth := by
  apply Term.Scoped.node
  intro i t ht
  cases i with
  | zero => simpa [h0] using (Option.some.inj ht ▸ ha)
  | succ i =>
      cases i with
      | zero => simpa [h1] using (Option.some.inj ht ▸ hb)
      | succ i =>
          cases i with
          | zero => simpa [h2] using (Option.some.inj ht ▸ hy)
          | succ i =>
              cases i with
              | zero => simpa [h3] using (Option.some.inj ht ▸ hn)
              | succ i => simp at ht

@[simp] theorem natural_scoped (depth n : Nat) : (Term.natural n).Scoped depth :=
  scoped_node (by intro i; rfl) (by simp)

/-- Every variable occurrence in the actual term has a finite in-context index.
Only annotations present in the term are included; arbitrary conversion targets
are deliberately not asserted to have the same scope. -/
theorem HasType.term_scoped (h : HasType ctx mode t T) : t.Scoped ctx.length := by
  induction h using HasType.rec
    (motive_1 := fun ctx _ A _ _ => A.Scoped ctx.length) with
  | intro hA allowed ih => exact ih
  | var hx readable => exact .var (lookup_bound hx)
  | pi hA hB ihA ihB => exact scoped_binder rfl rfl ihA ihB
  | lam hA hb ihA ihb => exact scoped_binder rfl rfl ihA ihb
  | ifLt ha hb hy hn iha ihb ihy ihn => exact scoped_branch rfl rfl rfl rfl iha ihb ihy ihn
  | ifEq ha hb hy hn iha ihb ihy ihn => exact scoped_branch rfl rfl rfl rfl iha ihb ihy ihn
  | elements size bound hs ih => exact scoped_node (by intro i; rfl) ih
  | convert ht conv ih => exact ih
  | _ =>
      apply scoped_node (by intro i; simp [Op.binders])
      simp_all

end Jihoo.NativeKernel
