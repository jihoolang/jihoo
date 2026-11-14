import Jihoo.CoreBridgeBetaShapes

/-! Uniqueness of declarative dependent types modulo conversion. The theorem
covers the entire existing beta-aware Raw judgment, including unrestricted
contexts, arrays, evidence and dependent application. Conversion injectivity is
the proved Church–Rosser consequence from CoreBridgeBetaConversion. -/
namespace Jihoo.CoreBridge.Raw.Beta

private def TypeView (Γ : Context) (t T : Raw) : Prop :=
  match t with
  | .var x => ∃ A, Γ x = some A ∧ Conv A T
  | .natural _ | .uadd _ _ | .usub _ _ _ => Conv .u64 T
  | .integer _ | .index _ _ _ => Conv .i64 T
  | .elements xs => Conv (.array (.natural xs.length)) T
  | .decide a b => Conv (.lt a b) T
  | .refl a => Conv (.eq a a) T
  | .zeroLe a => Conv (.lt (.natural 0) (.uadd a (.natural 1))) T
  | .lam e A body =>
      ∃ B, HasType (Γ.extend A) body B ∧ Conv (.pi e A B) T
  | .app f a =>
      ∃ e A B, HasType Γ f (.pi e A B) ∧ Conv (B.subst (single a)) T
  | _ => False

private theorem TypeView.convert (h : TypeView Γ t A) (hc : Conv A B) :
    TypeView Γ t B := by
  cases t <;> simp only [TypeView] at h ⊢
  all_goals first
    | exact False.elim h
    | exact .trans h hc
    | (obtain ⟨T, ht, conv⟩ := h; exact ⟨T, ht, .trans conv hc⟩)
    | (obtain ⟨e, X, Y, hf, conv⟩ := h; exact ⟨e, X, Y, hf, .trans conv hc⟩)

private theorem HasType.typeView (h : HasType Γ t A) : TypeView Γ t A := by
  induction h using HasType.rec (motive_1 := fun _ _ _ => True)
  all_goals first | exact True.intro | skip
  case var hx => exact ⟨_, hx, .refl _⟩
  case natural => exact .refl _
  case integer => exact .refl _
  case uadd => exact .refl _
  case usub => exact .refl _
  case elements => exact .refl _
  case decide => exact .refl _
  case refl => exact .refl _
  case zeroLe => exact .refl _
  case index => exact .refl _
  case lam hA he hb ihA ihb => exact ⟨_, hb, .refl _⟩
  case app hf ha ihf iha => exact ⟨_, _, _, hf, .refl _⟩
  case convert ht hc ih => exact ih.convert hc

/-- A term has a unique type up to the actual beta/arithmetic/read conversion
relation. No context formation, normalization, checker acceptance, or source
encoding is assumed. -/
theorem HasType.unique (ht : HasType Γ t A) (hu : HasType Γ t B) : Conv A B := by
  induction t using Raw.rec (motive_2 := fun _ => True) generalizing Γ A B
  all_goals first | exact True.intro | skip
  all_goals have hv := ht.typeView
  all_goals have hw := hu.typeView
  all_goals simp only [TypeView] at hv hw
  all_goals first
    | exact False.elim hv
    | exact .trans (.symm hv) hw
    | skip
  case var x =>
    obtain ⟨X, hx, hc⟩ := hv
    obtain ⟨Y, hy, hd⟩ := hw
    have he : X = Y := Option.some.inj (hx.symm.trans hy)
    subst Y
    exact .trans (.symm hc) hd
  case lam e X body ihX ihbody =>
    obtain ⟨Y, hy, hc⟩ := hv
    obtain ⟨Z, hz, hd⟩ := hw
    exact .trans (.symm hc) (.trans (.pi (.refl _) (ihbody hy hz)) hd)
  case app f a ihf iha =>
    obtain ⟨e, X, Y, hf, hc⟩ := hv
    obtain ⟨e', X', Y', hf', hd⟩ := hw
    have hpi := (ihf hf hf').pi_injective
    exact .trans (.symm hc) (.trans (hpi.2.2.substitution (single a)) hd)

/-- In particular, the two machine scalar types cannot both classify a term. -/
theorem HasType.no_scalar_confusion (hu : HasType Γ t .u64)
    (hi : HasType Γ t .i64) : False :=
  Conv.u64_i64_separate (hu.unique hi)

/-- Any alleged second type outside the inferred conversion class is rejected
by the declarative judgment itself. -/
theorem HasType.excludes (ht : HasType Γ t A) (apart : ¬ Conv A B) :
    ¬ HasType Γ t B := fun hu => apart (ht.unique hu)

/-- A term cannot acquire two different rigid outer type constructors through
different typing derivations, even when conversion contains beta expansions. -/
theorem HasType.rigid_head_unique (ht : HasType Γ t A) (hu : HasType Γ t B)
    (ha : typeHead A = some k) (hb : typeHead B = some l) : k = l :=
  (ht.unique hu).rigid_head ha hb

/-- Array length expressions inferred by different derivations must convert. -/
theorem HasType.array_index_unique (ht : HasType Γ t (.array m))
    (hu : HasType Γ t (.array n)) : Conv m n :=
  (ht.unique hu).array_injective

/-- Concrete array lengths are genuinely unique, rather than merely having the
same erased shape. -/
theorem HasType.array_length_unique (ht : HasType Γ t (.array (.natural m)))
    (hu : HasType Γ t (.array (.natural n))) : m = n :=
  (ht.array_index_unique hu).natural_injective

/-- The same evidence cannot be assigned independently incompatible equality
endpoints by two derivations. -/
theorem HasType.equality_indices_unique (ht : HasType Γ t (.eq a b))
    (hu : HasType Γ t (.eq c d)) : Conv a c ∧ Conv b d :=
  (ht.unique hu).eq_injective

/-- Function type uniqueness retains binder mode and dependent codomain, not
just the runtime arity. -/
theorem HasType.function_unique (ht : HasType Γ t (.pi e A B))
    (hu : HasType Γ t (.pi e' A' B')) :
    e = e' ∧ Conv A A' ∧ Conv B B' :=
  (ht.unique hu).pi_injective

/-- Reflexivity cannot prove an equality between distinct numerals, including
after arbitrary conversions of either endpoint. The reflected expression may
itself be open or higher order. -/
theorem HasType.refl_numeral_consistency
    (h : HasType Γ (.refl a) (.eq (.natural m) (.natural n))) : m = n := by
  have hc : Conv (.eq a a) (.eq (.natural m) (.natural n)) := h.typeView
  obtain ⟨hm, hn⟩ := hc.eq_injective
  exact (Conv.trans (.symm hm) hn).natural_injective

theorem HasType.refl_false_equality_rejected (apart : m ≠ n) :
    ¬ HasType Γ (.refl a) (.eq (.natural m) (.natural n)) :=
  fun h => apart h.refl_numeral_consistency

end Jihoo.CoreBridge.Raw.Beta
