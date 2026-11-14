import Jihoo.NativeEnvironmentInversion
import Jihoo.NativeEnvironmentUniquenessAlgebra

/-! Type uniqueness for the same unified environment, across code and ghost
modes, using proved full-ACU rigid injectivity and deterministic telescopes. -/
namespace Jihoo.NativeKernel.Environment
open Jihoo.NativeKernel.Environment.Conversion
private theorem related_drop (related : ListRel Conv xs ys) (n : Nat) :
    ListRel Conv (xs.drop n) (ys.drop n) := by
  induction n generalizing xs ys with
  | zero => exact related
  | succ n ih =>
    cases related with
    | nil => exact .nil
    | cons first rest => exact ih rest

theorem eliminationResult_congr (entry : CheckedFamily) (motive scrutinee : Term)
    (indices : ListRel Conv xs ys) :
    Conv (eliminationResult entry motive xs scrutinee) (eliminationResult entry motive ys scrutinee) := by
  unfold eliminationResult
  split
  · exact .node .app (.cons (applications_congr (.refl _) (related_drop indices _)) (.cons (.refl _) .nil))
  · exact applications_congr (.refl _) indices

 theorem HasType.unique (ht : HasType env Γ mode t A) (hu : HasType env Γ mode' t B) : Conv A B := by
  have aux : ∀ t, ∀ Γ mode mode' A B, HasType env Γ mode t A → HasType env Γ mode' t B → Conv A B := by
    have wf : WellFounded (fun a b : Term => sizeOf a < sizeOf b) := (measure sizeOf).wf
    intro t
    induction t using wf.induction with
    | h t ih =>
        intro Γ mode mode' A B ht hu
        have hv := ht.principalView
        have hw := hu.principalView
        fun_cases PrincipalView env Γ mode t A <;> simp only [PrincipalView] at hv hw
        all_goals first | exact False.elim hv | exact .trans (.symm hv) hw | skip
        case case1 =>
          obtain ⟨b, hb, hc⟩ := hv
          obtain ⟨b', hb', hd⟩ := hw
          have same : b = b' := Option.some.inj (hb.symm.trans hb')
          subst b'
          exact .trans (.symm hc) hd
        case case25 =>
          rename_i e X Y
          obtain ⟨s,r,hX,hY,hc⟩ := hv
          obtain ⟨s',r',hX',hY',hd⟩ := hw
          have ds := ih X (by simp; omega) Γ true true _ _ hX hX'
          have dr := ih Y (by simp; omega) (⟨X,e⟩ :: Γ) true true _ _ hY hY'
          have ss := ds.sort_injective
          have rr := dr.sort_injective
          subst s'; subst r'
          exact .trans (.symm hc) hd
        case case26 =>
          rename_i e X body
          obtain ⟨Y,hY,hc⟩ := hv
          obtain ⟨Z,hZ,hd⟩ := hw
          have bodies := ih body (by simp; omega) (⟨X,e⟩ :: Γ) mode mode' Y Z hY hZ
          exact .trans (.symm hc)
            (.trans (.node (.pi e) (.cons (.refl X) (.cons bodies .nil))) hd)
        case case27 =>
          rename_i f a
          obtain ⟨e,X,Y,hf,hc⟩ := hv
          obtain ⟨e',X',Y',hf',hd⟩ := hw
          have functions := ih f (by simp; omega) Γ mode mode' _ _ hf hf'
          exact .trans (.symm hc) (.trans
            (functions.pi_injective.2.2.substitution (single a)) hd)
        case case28 =>
          rename_i a b
          obtain ⟨X,hX,hc⟩ := hv
          obtain ⟨Y,hY,hd⟩ := hw
          have bodies := ih b (by simp; omega) Γ mode mode' X Y hX hY
          exact .trans (.symm hc) (.trans bodies hd)
        case case29 =>
          rename_i f evidence p
          obtain ⟨a,b,he,hc⟩ := hv
          obtain ⟨a',b',he',hd⟩ := hw
          have equality := ih evidence (by simp; omega) Γ true true _ _ he he'
          exact .trans (.symm hc)
            (.trans (.node .app (.cons (.refl f) (.cons equality.eq_injective.2 .nil))) hd)
        case case30 =>
          rename_i s
          obtain ⟨p,hp,hc⟩ := hv
          obtain ⟨q,hq,hd⟩ := hw
          have predicates := ih s (by simp; omega) Γ true true _ _ hp hq
          exact .trans (.symm hc)
            (.trans (.node .app (.cons predicates.refine_injective (.cons (.refl _) .nil))) hd)
        case case31 =>
          rename_i a b yes no
          obtain ⟨X,hX,hc⟩ := hv
          obtain ⟨Y,hY,hd⟩ := hw
          have branches := ih no (by simp; omega) Γ mode mode' X Y hX hY
          exact .trans (.symm hc) (.trans branches hd)
        case case32 =>
          rename_i a b yes no
          obtain ⟨X,hX,hc⟩ := hv
          obtain ⟨Y,hY,hd⟩ := hw
          have branches := ih no (by simp; omega) Γ mode mode' X Y hX hY
          exact .trans (.symm hc) (.trans branches hd)
        case case34 =>
          rename_i n init body
          obtain ⟨X,hX,hc⟩ := hv
          obtain ⟨Y,hY,hd⟩ := hw
          exact .trans (.symm hc) (.trans (ih init (by simp; omega) Γ mode mode' X Y hX hY) hd)
        case case36 =>
          obtain ⟨declaration,found,hc⟩ := hv
          obtain ⟨declaration',found',hd⟩ := hw
          have same := Option.some.inj (found.symm.trans found')
          subst declaration'
          exact .trans (.symm hc) hd
        case case37 =>
          obtain ⟨entry,found,hc⟩ := hv
          obtain ⟨entry',found',hd⟩ := hw
          have same := Option.some.inj (found.symm.trans found')
          subst entry'
          exact .trans (.symm hc) hd
        case case38 =>
          obtain ⟨entry,signature,arity,indices,found,sigFound,args,hc⟩ := hv
          obtain ⟨entry',signature',arity',indices',found',sigFound',args',hd⟩ := hw
          have same := Option.some.inj (found.symm.trans found')
          subst entry'
          have same := Option.some.inj (sigFound.symm.trans sigFound')
          subst signature'
          exact .trans (.symm hc) (.trans (args.result_unique _ _ _ _ _ args' (.refl _)) hd)
        case case39 =>
          rename_i f count fields
          obtain ⟨entry,motive,branches,scrutinee,indices,scrutineeMode,found,countEq,layout,scrut,hc⟩ := hv
          obtain ⟨entry',motive',branches',scrutinee',indices',scrutineeMode',found',countEq',layout',scrut',hd⟩ := hw
          have entries := Option.some.inj (found.symm.trans found')
          subst entry'
          have layouts := List.cons.inj (layout.symm.trans layout')
          have motives := layouts.1
          subst motive'
          have ends := List.append_inj_right layouts.2 (countEq.symm.trans countEq')
          have scruts := (List.cons.inj ends).1
          subst scrutinee'
          have smaller : sizeOf scrutinee < sizeOf (Term.node (.elim f count) fields) := by
            have member : scrutinee ∈ fields := by rw [layout]; simp
            have bound := List.sizeOf_lt_of_mem member
            simp only [Term.node.sizeOf_spec]
            omega
          have indicesConv := ind_injective (ih scrutinee smaller Γ scrutineeMode scrutineeMode' _ _ scrut scrut')
          exact .trans (.symm hc) (.trans (eliminationResult_congr _ _ _ indicesConv.2.2) hd)
        case case44 =>
          rename_i buffer index value proof
          obtain ⟨n,hn,hc⟩ := hv
          obtain ⟨m,hm,hd⟩ := hw
          have lengths := buffer_injective (ih buffer (by simp; omega) Γ mode mode' _ _ hn hm)
          exact .trans (.symm hc) (.trans (.node .buffer (.cons lengths .nil)) hd)
        case case45 =>
          rename_i buffer rest
          obtain ⟨X,hX,hc⟩ := hv
          obtain ⟨Y,hY,hd⟩ := hw
          exact .trans (.symm hc) (.trans (ih rest (by simp; omega) Γ mode mode' X Y hX hY) hd)
        case case46 =>
          rename_i buffer
          obtain ⟨X,hX,hc⟩ := hv
          obtain ⟨Y,hY,hd⟩ := hw
          have owners := ih buffer (by simp; omega) Γ true true X Y hX hY
          exact .trans (.symm hc) (.trans (.node .ref (.cons owners .nil)) hd)
        case case47 =>
          rename_i reference
          obtain ⟨X,hX,hc⟩ := hv
          obtain ⟨Y,hY,hd⟩ := hw
          have owners := ref_injective (ih reference (by simp; omega) Γ true true _ _ hX hY)
          exact .trans (.symm hc) (.trans owners hd)
        case case48 =>
          rename_i erased motive owner result
          obtain ⟨X,hX,hc⟩ := hv
          obtain ⟨Y,hY,hd⟩ := hw
          have owners := ih owner (by simp; omega) Γ mode mode' X Y hX hY
          exact .trans (.symm hc) (.trans (.node (.back erased) (.cons owners (.cons (.refl _) .nil))) hd)
        case case49 =>
          rename_i buffer index proof continuation
          obtain ⟨X,e,Y,C,normal,outside,hκ,cn,lowered,hc⟩ := hv
          obtain ⟨X',e',Y',C',normal',outside',hκ',cn',lowered',hd⟩ := hw
          have results := (ih continuation (by simp; omega) Γ mode mode' _ _ hκ hκ').pi_injective.2.2.pi_injective.2.2
          have outsideConv := lowered_conversion lowered lowered' (.trans (.symm cn) (.trans results cn'))
          exact .trans (.symm hc) (.trans outsideConv hd)
        case case50 =>
          rename_i value continuation
          obtain ⟨X,e,Y,C,normal,outside,hκ,cn,lowered,hc⟩ := hv
          obtain ⟨X',e',Y',C',normal',outside',hκ',cn',lowered',hd⟩ := hw
          have results := (ih continuation (by simp; omega) Γ mode mode' _ _ hκ hκ').pi_injective.2.2.pi_injective.2.2
          have outsideConv := lowered_conversion lowered lowered' (.trans (.symm cn) (.trans results cn'))
          exact .trans (.symm hc) (.trans outsideConv hd)
        case case51 =>
          rename_i f count fields
          obtain ⟨entry,motive,branches,scrutinee,indices,scrutineeMode,found,countEq,layout,scrut,hc⟩ := hv
          obtain ⟨entry',motive',branches',scrutinee',indices',scrutineeMode',found',countEq',layout',scrut',hd⟩ := hw
          have entries := Option.some.inj (found.symm.trans found')
          subst entry'
          have layouts := List.cons.inj (layout.symm.trans layout')
          have motives := layouts.1
          subst motive'
          have ends := List.append_inj_right layouts.2 (countEq.symm.trans countEq')
          have scruts := (List.cons.inj ends).1
          subst scrutinee'
          have smaller : sizeOf scrutinee < sizeOf (Term.node (.elim f count) fields) := by
            have member : scrutinee ∈ fields := by rw [layout]; simp
            have bound := List.sizeOf_lt_of_mem member
            simp only [Term.node.sizeOf_spec]
            omega
          have indicesConv := ind_injective (ih scrutinee smaller Γ scrutineeMode scrutineeMode' _ _ scrut scrut')
          exact .trans (.symm hc) (.trans (eliminationResult_congr _ _ _ indicesConv.2.2) hd)
        case case52 =>
          rename_i family owner rest
          obtain ⟨X,hX,hc⟩ := hv
          obtain ⟨Y,hY,hd⟩ := hw
          exact .trans (.symm hc) (.trans (ih rest (by simp; omega) Γ mode mode' X Y hX hY) hd)
  exact aux t Γ mode mode' A B ht hu


/-- The sort assigned to a binder domain is unique. -/
theorem Binder.unique (h : Binder env Γ e A s) (h' : Binder env Γ e A r) : s = r := by
  cases h with
  | intro ht allowed =>
      cases h' with
      | intro ht' allowed' => exact (ht.unique ht').sort_injective

theorem HasType.sort_unique {s r : SortTag} (ht : HasType env Γ mode t s.term)
    (hu : HasType env Γ mode' t r.term) : s = r := (ht.unique hu).sort_injective

theorem HasType.no_scalar_confusion (hu : HasType env Γ mode t .u64)
    (hi : HasType env Γ mode' t .i64) : False := ACU.Conv.full_u64_i64_separate (hu.unique hi)

theorem HasType.array_index_unique (ht : HasType env Γ mode t (.array m))
    (hu : HasType env Γ mode' t (.array n)) : Conv m n := (ht.unique hu).array_injective

theorem HasType.array_length_unique (ht : HasType env Γ mode t (.array (.natural m)))
    (hu : HasType env Γ mode' t (.array (.natural n))) : m = n :=
  (ht.array_index_unique hu).natural_injective

theorem HasType.function_unique (ht : HasType env Γ mode t (.pi e A B))
    (hu : HasType env Γ mode' t (.pi e' A' B')) :
    e = e' ∧ Conv A A' ∧ Conv B B' := (ht.unique hu).pi_injective

theorem HasType.equality_indices_unique (ht : HasType env Γ mode t (.eq a b))
    (hu : HasType env Γ mode' t (.eq c d)) : Conv a c ∧ Conv b d := (ht.unique hu).eq_injective

theorem HasType.bound_indices_unique (ht : HasType env Γ mode t (.lt a b))
    (hu : HasType env Γ mode' t (.lt c d)) : Conv a c ∧ Conv b d := (ht.unique hu).lt_injective

theorem HasType.refinement_predicate_unique (ht : HasType env Γ mode t (.refine p))
    (hu : HasType env Γ mode' t (.refine q)) : Conv p q := (ht.unique hu).refine_injective

theorem HasType.excludes (ht : HasType env Γ mode t A) (apart : ¬ Conv A B) :
    ¬ HasType env Γ mode' t B := fun hu => apart (ht.unique hu)

theorem HasType.universe_level_unique (ht : HasType env Γ mode t (.univ m))
    (hu : HasType env Γ mode' t (.univ n)) : m = n := (ht.unique hu).full_universe_injective

/-- A universe literal's type is its exact successor, even after any number
of result-type conversions. Administrative Universe32 can classify Universe31. -/
theorem HasType.universe_successor (h : HasType env Γ mode (.univ n) (.univ m)) : m = n+1 :=
  (show Conv (.univ (n+1)) (.univ m) from h.principalView).full_universe_injective.symm

theorem HasType.no_type_in_type : ¬ HasType env Γ mode (.univ n) (.univ n) := by
  intro h
  have same := h.universe_successor
  omega

theorem HasType.universe_not_proposition : ¬ HasType env Γ mode (.univ n) .prop :=
  fun h => ACU.Conv.full_rigid_disjoint (op := .universe (n+1)) (op' := .prop) rfl rfl (by intro same; cases same) h.principalView

theorem HasType.sorts_do_not_collapse (hp : HasType env Γ mode t .prop)
    (hu : HasType env Γ mode' t (.univ n)) : False :=
  ACU.Conv.full_rigid_disjoint (op := .universe n) (op' := .prop) rfl rfl (by intro same; cases same) (.symm (hp.unique hu))


/-- Every accepted inferred type determines all declarative types, including
independent derivations in another mode. -/
theorem Checker.infer_unique (hi : Checker.infer fuel env Γ mode t = some A)
    (ht : HasType env Γ mode' t B) : Conv A B := (Checker.infer_sound hi).unique ht

theorem Checker.check_unique (hc : Checker.check fuel env Γ mode t A = true)
    (ht : HasType env Γ mode' t B) : Conv A B := (Checker.check_sound hc).unique ht

theorem HasType.constructor_indices_unique
    (ht : HasType env Γ mode t (.node (.ind f n) xs))
    (hu : HasType env Γ mode' t (.node (.ind g m) ys)) :
    f = g ∧ n = m ∧ ListRel Conv xs ys := ind_injective (ht.unique hu)

theorem HasType.buffer_index_unique (ht : HasType env Γ mode t (.buffer n))
    (hu : HasType env Γ mode' t (.buffer m)) : Conv n m := buffer_injective (ht.unique hu)

theorem HasType.reference_type_unique (ht : HasType env Γ mode t (.ref A))
    (hu : HasType env Γ mode' t (.ref B)) : Conv A B := ref_injective (ht.unique hu)

end Jihoo.NativeKernel.Environment
