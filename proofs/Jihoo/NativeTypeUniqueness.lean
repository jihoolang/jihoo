import Jihoo.NativeConfluence
import Jihoo.NativeCheckerSoundness

/-! Type uniqueness for every rule of the universe-aware native judgment,
including comparisons between code and ghost derivations. The proof uses the
actual native conversion relation and its proved constructor injectivity. -/
namespace Jihoo.NativeKernel
open Conversion

private def TypeView (Γ : Context) (mode : Bool) : Term → Term → Prop
  | .var x, T => ∃ b, lookup Γ x = some b ∧ Conv b.ty T
  | .univ n, T => Conv (.univ (n+1)) T
  | .prop, T | .u64, T | .i64, T | .array _, T | .refine _, T => Conv (.univ 0) T
  | .lt _ _, T | .eq _ _, T => Conv .prop T
  | .natural _, T | .uadd _ _, T | .usub _ _ _, T | .witness _, T => Conv .u64 T
  | .integer _, T | .index _ _ _, T | .arith _ _ _, T => Conv .i64 T
  | .elements _ xs, T => Conv (.array (.natural xs.length)) T
  | .decide a b, T => Conv (.lt a b) T
  | .refl a, T => Conv (.eq a a) T
  | .zeroLe a, T => Conv (.lt (.natural 0) (.uadd a (.natural 1))) T
  | .ltAdd a b c _, T => Conv (.lt (.uadd a c) (.uadd b c)) T
  | .ltCancel a b _ _, T => Conv (.lt a b) T
  | .ltLe a _ c _ _, T => Conv (.lt a c) T
  | .pack p _ _, T => Conv (.refine p) T
  | .pi e A B, T => ∃ s r : SortTag,
      HasType Γ true A s.term ∧ HasType (⟨A,e⟩ :: Γ) true B r.term ∧ Conv (s.pi r).term T
  | .lam e A body, T => ∃ B, HasType (⟨A,e⟩ :: Γ) mode body B ∧ Conv (.pi e A B) T
  | .app f a, T => ∃ e A B, HasType Γ mode f (.pi e A B) ∧ Conv (B.subst (single a)) T
  | .strict _ b, T => ∃ B, HasType Γ mode b B ∧ Conv B T
  | .transport f e _, T => ∃ a b, HasType Γ true e (.eq a b) ∧ Conv (.app f b) T
  | .proof s, T => ∃ p, HasType Γ true s (.refine p) ∧ Conv (.app p (.witness s)) T
  | .ifLt _ _ _ no, T | .ifEq _ _ _ no, T => ∃ B, HasType Γ mode no B ∧ Conv B T
  | .absurd U _, T => Conv U T
  | _, _ => False

private theorem TypeView.convert (h : TypeView Γ mode t A) (hc : Conv A B) :
    TypeView Γ mode t B := by
  fun_cases TypeView Γ mode t A <;> simp only [TypeView] at h ⊢
  all_goals first
    | exact False.elim h
    | exact .trans h hc
    | (obtain ⟨a,b,c,d,e⟩ := h; exact ⟨a,b,c,d,.trans e hc⟩)
    | (obtain ⟨a,b,c,d⟩ := h; exact ⟨a,b,c,.trans d hc⟩)
    | (obtain ⟨a,b,c⟩ := h; exact ⟨a,b,.trans c hc⟩)

private theorem HasType.typeView (h : HasType Γ mode t T) : TypeView Γ mode t T := by
  induction h using HasType.rec (motive_1 := fun _ _ _ _ _ => True)
  all_goals first | trivial | exact Conv.refl _ | skip
  case var hx readable => exact ⟨_, hx, .refl _⟩
  case pi hA hB _ _ =>
    cases hA with
    | intro typed allowed => exact ⟨_,_,typed,hB,.refl _⟩
  case lam hA hb _ _ => exact ⟨_,hb,.refl _⟩
  case app hf ha allowed _ _ => exact ⟨_,_,_,hf,.refl _⟩
  case strict ha hb _ _ => exact ⟨_,hb,.refl _⟩
  case transport hf he hp _ _ _ => exact ⟨_,_,he,.refl _⟩
  case proof hs _ => exact ⟨_,hs,.refl _⟩
  case ifLt ha hb hy hn _ _ _ _ => exact ⟨_,hn,.refl _⟩
  case ifEq ha hb hy hn _ _ _ _ => exact ⟨_,hn,.refl _⟩
  case convert ht conv ih => exact ih.convert conv

 theorem HasType.unique (ht : HasType Γ mode t A) (hu : HasType Γ mode' t B) : Conv A B := by
  have aux : ∀ t, ∀ Γ mode mode' A B, HasType Γ mode t A → HasType Γ mode' t B → Conv A B := by
    have wf : WellFounded (fun a b : Term => sizeOf a < sizeOf b) := (measure sizeOf).wf
    intro t
    induction t using wf.induction with
    | h t ih =>
        intro Γ mode mode' A B ht hu
        have hv := ht.typeView
        have hw := hu.typeView
        fun_cases TypeView Γ mode t A <;> simp only [TypeView] at hv hw
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
  exact aux t Γ mode mode' A B ht hu

/-- The sort assigned to a binder domain is unique. -/
theorem Binder.unique (h : Binder Γ e A s) (h' : Binder Γ e A r) : s = r := by
  cases h with
  | intro ht allowed =>
      cases h' with
      | intro ht' allowed' => exact (ht.unique ht').sort_injective

theorem HasType.sort_unique {s r : SortTag} (ht : HasType Γ mode t s.term)
    (hu : HasType Γ mode' t r.term) : s = r := (ht.unique hu).sort_injective

theorem HasType.no_scalar_confusion (hu : HasType Γ mode t .u64)
    (hi : HasType Γ mode' t .i64) : False := Conv.u64_i64_separate (hu.unique hi)

theorem HasType.array_index_unique (ht : HasType Γ mode t (.array m))
    (hu : HasType Γ mode' t (.array n)) : Conv m n := (ht.unique hu).array_injective

theorem HasType.array_length_unique (ht : HasType Γ mode t (.array (.natural m)))
    (hu : HasType Γ mode' t (.array (.natural n))) : m = n :=
  (ht.array_index_unique hu).natural_injective

theorem HasType.function_unique (ht : HasType Γ mode t (.pi e A B))
    (hu : HasType Γ mode' t (.pi e' A' B')) :
    e = e' ∧ Conv A A' ∧ Conv B B' := (ht.unique hu).pi_injective

theorem HasType.equality_indices_unique (ht : HasType Γ mode t (.eq a b))
    (hu : HasType Γ mode' t (.eq c d)) : Conv a c ∧ Conv b d := (ht.unique hu).eq_injective

theorem HasType.bound_indices_unique (ht : HasType Γ mode t (.lt a b))
    (hu : HasType Γ mode' t (.lt c d)) : Conv a c ∧ Conv b d := (ht.unique hu).lt_injective

theorem HasType.refinement_predicate_unique (ht : HasType Γ mode t (.refine p))
    (hu : HasType Γ mode' t (.refine q)) : Conv p q := (ht.unique hu).refine_injective

theorem HasType.excludes (ht : HasType Γ mode t A) (apart : ¬ Conv A B) :
    ¬ HasType Γ mode' t B := fun hu => apart (ht.unique hu)

theorem HasType.universe_level_unique (ht : HasType Γ mode t (.univ m))
    (hu : HasType Γ mode' t (.univ n)) : m = n := (ht.unique hu).universe_injective

/-- A universe literal's type is its exact successor, even after any number
of result-type conversions. Administrative Universe32 can classify Universe31. -/
theorem HasType.universe_successor (h : HasType Γ mode (.univ n) (.univ m)) : m = n+1 :=
  (show Conv (.univ (n+1)) (.univ m) from h.typeView).universe_injective.symm

theorem HasType.no_type_in_type : ¬ HasType Γ mode (.univ n) (.univ n) := by
  intro h
  have same := h.universe_successor
  omega

theorem HasType.universe_not_proposition : ¬ HasType Γ mode (.univ n) .prop :=
  fun h => Conv.universe_prop_separate (n+1) h.typeView

theorem HasType.sorts_do_not_collapse (hp : HasType Γ mode t .prop)
    (hu : HasType Γ mode' t (.univ n)) : False :=
  Conv.universe_prop_separate n (.symm (hp.unique hu))

private theorem universe_bound_aux (h : HasType Γ mode t T) :
    ∀ n, t = .univ n → n < 32 := by
  induction h using HasType.rec (motive_1 := fun _ _ _ _ _ => True) with
  | univ bound =>
      intro n he
      cases he
      exact bound
  | convert ht conv ih => exact ih
  | _ => first | trivial | (intro n he; cases he)

/-- The input universe ceiling survives arbitrary result-type conversion. -/
theorem HasType.universe_input_bound (h : HasType Γ mode (.univ n) T) : n < 32 :=
  universe_bound_aux h n rfl

theorem HasType.universe_limit_rejected (outside : 32 ≤ n) :
    ¬ HasType Γ mode (.univ n) T := by
  intro h
  have bound := h.universe_input_bound
  omega

/-- A reflected open expression cannot be assigned two distinct numeral endpoints. -/
theorem HasType.refl_numeral_consistency
    (h : HasType Γ mode (.refl a) (.eq (.natural m) (.natural n))) : m = n := by
  have hc : Conv (.eq a a) (.eq (.natural m) (.natural n)) := h.typeView
  obtain ⟨hm, hn⟩ := hc.eq_injective
  exact (Conv.trans (.symm hm) hn).natural_injective

theorem HasType.refl_false_equality_rejected (apart : m ≠ n) :
    ¬ HasType Γ mode (.refl a) (.eq (.natural m) (.natural n)) :=
  fun h => apart h.refl_numeral_consistency

/-- The executable inferred type determines every declarative type, even
when that second derivation uses another mode and arbitrary conversions. -/
theorem Checker.infer_unique (hi : Checker.infer fuel Γ mode t = some A)
    (ht : HasType Γ mode' t B) : Conv A B := (Checker.infer_sound hi).unique ht

theorem Checker.check_unique (hc : Checker.check fuel Γ mode t A = true)
    (ht : HasType Γ mode' t B) : Conv A B := (Checker.check_sound hc).unique ht

end Jihoo.NativeKernel
