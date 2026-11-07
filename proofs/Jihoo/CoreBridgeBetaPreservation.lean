import Jihoo.CoreBridgeBetaTyping

/-! Full contextual beta preservation for the beta-aware target judgment.
Reductions include binder annotations, dependent arguments, proof evidence and
array elements. The original result type is retained by conversion. -/
namespace Jihoo.CoreBridge.Raw.Beta

/-- One beta contraction at any raw syntax position. No runtime evaluation
strategy, effectful term, erasure pass or executable checker is modeled. -/
inductive Step : Raw → Raw → Prop where
  | beta (e A body a) : Step (.app (.lam e A body) a) (body.subst (single a))
  | array : Step a a' → Step (.array a) (.array a')
  | ltLeft : Step a a' → Step (.lt a b) (.lt a' b)
  | ltRight : Step b b' → Step (.lt a b) (.lt a b')
  | eqLeft : Step a a' → Step (.eq a b) (.eq a' b)
  | eqRight : Step b b' → Step (.eq a b) (.eq a b')
  | piDomain : Step A A' → Step (.pi e A B) (.pi e A' B)
  | piCodomain : Step B B' → Step (.pi e A B) (.pi e A B')
  | lamDomain : Step A A' → Step (.lam e A b) (.lam e A' b)
  | lamBody : Step b b' → Step (.lam e A b) (.lam e A b')
  | appFunction : Step f f' → Step (.app f a) (.app f' a)
  | appArgument : Step a a' → Step (.app f a) (.app f a')
  | elements (pre post) : Step a a' →
      Step (.elements (pre ++ a :: post)) (.elements (pre ++ a' :: post))
  | indexArray : Step a a' → Step (.index a i p) (.index a' i p)
  | indexIndex : Step i i' → Step (.index a i p) (.index a i' p)
  | indexProof : Step p p' → Step (.index a i p) (.index a i p')
  | reflTerm : Step a a' → Step (.refl a) (.refl a')
  | zeroLe : Step a a' → Step (.zeroLe a) (.zeroLe a')
  | decideLeft : Step a a' → Step (.decide a b) (.decide a' b)
  | decideRight : Step b b' → Step (.decide a b) (.decide a b')
  | uaddLeft : Step a a' → Step (.uadd a b) (.uadd a' b)
  | uaddRight : Step b b' → Step (.uadd a b) (.uadd a b')
  | usubLeft : Step a a' → Step (.usub a b p) (.usub a' b p)
  | usubRight : Step b b' → Step (.usub a b p) (.usub a b' p)
  | usubProof : Step p p' → Step (.usub a b p) (.usub a b p')

private theorem list_refl (xs : List Raw) : ListRel Conv xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (.refl _) ih

private theorem list_replace (pre post : List Raw) (h : Conv a b) :
    ListRel Conv (pre ++ a :: post) (pre ++ b :: post) := by
  induction pre with
  | nil => exact .cons h (list_refl post)
  | cons x xs ih => exact .cons (.refl _) ih

theorem Step.conversion (h : Step t u) : Conv t u := by
  induction h with
  | beta e A body a => exact .beta e A body a
  | array _ ih => exact .array ih
  | ltLeft _ ih => exact .lt ih (.refl _)
  | ltRight _ ih => exact .lt (.refl _) ih
  | eqLeft _ ih => exact .eq ih (.refl _)
  | eqRight _ ih => exact .eq (.refl _) ih
  | piDomain _ ih => exact .pi ih (.refl _)
  | piCodomain _ ih => exact .pi (.refl _) ih
  | lamDomain _ ih => exact .lam ih (.refl _)
  | lamBody _ ih => exact .lam (.refl _) ih
  | appFunction _ ih => exact .app ih (.refl _)
  | appArgument _ ih => exact .app (.refl _) ih
  | elements pre post _ ih => exact .elements (list_replace pre post ih)
  | indexArray _ ih => exact .index ih (.refl _) (.refl _)
  | indexIndex _ ih => exact .index (.refl _) ih (.refl _)
  | indexProof _ ih => exact .index (.refl _) (.refl _) ih
  | reflTerm _ ih => exact .reflTerm ih
  | zeroLe _ ih => exact .zeroLe ih
  | decideLeft _ ih => exact .decide ih (.refl _)
  | decideRight _ ih => exact .decide (.refl _) ih
  | uaddLeft _ ih => exact .uadd ih (.refl _)
  | uaddRight _ ih => exact .uadd (.refl _) ih
  | usubLeft _ ih => exact .usub ih (.refl _) (.refl _)
  | usubRight _ ih => exact .usub (.refl _) ih (.refl _)
  | usubProof _ ih => exact .usub (.refl _) (.refl _) ih

/-- Formation, rather than arbitrary raw conversion, controls erasure flags.
Raw applications can beta-reduce to propositions, but are not formed types. -/
theorem IsType.proposition_step (h : IsType Γ A) (hs : Step A A') :
    A'.proposition = A.proposition := by
  induction A using Raw.rec (motive_2 := fun _ => True) generalizing Γ A' <;>
    first | trivial | (cases h <;> cases hs <;> simp_all [proposition])
  case pi.pi.piCodomain => solve_by_elim

private theorem preservation_mutual :
    (∀ Γ A, IsType Γ A → ∀ A', Step A A' → IsType Γ A') ∧
    (∀ Γ t A, HasType Γ t A → ∀ t', Step t t' → HasType Γ t' A) := by
  constructor
  · intro Γ A h
    induction h using IsType.rec
      (motive_2 := fun Γ t A _ => ∀ t', Step t t' → HasType Γ t' A)
    case u64 => intro A' hs; cases hs
    case i64 => intro A' hs; cases hs
    case array hn ih =>
      intro A' hs
      cases hs with
      | array hs => exact .array (ih _ hs)
    case lt ha hb iha ihb =>
      intro A' hs
      cases hs with
      | ltLeft hs => exact .lt (iha _ hs) hb
      | ltRight hs => exact .lt ha (ihb _ hs)
    case eq ha hb iha ihb =>
      intro A' hs
      cases hs with
      | eqLeft hs => exact .eq (iha _ hs) hb
      | eqRight hs => exact .eq ha (ihb _ hs)
    case pi hA he hB ihA ihB =>
      intro A' hs
      cases hs with
      | piDomain hs =>
          exact .pi (ihA _ hs) (he.trans (hA.proposition_step hs).symm)
            (hB.context_conversion ((ContextConversion.refl _).extend hs.conversion))
      | piCodomain hs => exact .pi hA he (ihB _ hs)
    case var hx t' hs => cases hs
    case natural hn t' hs => cases hs
    case integer hlo hhi t' hs => cases hs
    case uadd ha hb iha ihb t' hs =>
      cases hs with
      | uaddLeft hs => exact .uadd (iha _ hs) hb
      | uaddRight hs => exact .uadd ha (ihb _ hs)
    case usub ha hb hp iha ihb ihp t' hs =>
      cases hs with
      | usubLeft hs =>
          exact .usub (iha _ hs) hb
            (.convert hp (.lt (.refl _) (.uadd hs.conversion (.refl _))))
      | usubRight hs => exact .usub ha (ihb _ hs) (.convert hp (.lt hs.conversion (.refl _)))
      | usubProof hs => exact .usub ha hb (ihp _ hs)
    case elements xs Γ hs hlen ih t' hstep =>
      cases hstep with
      | elements pre post hstep =>
          refine HasType.convert (HasType.elements ?_ ?_) ?_
          · intro x hx
            simp only [List.mem_append, List.mem_cons] at hx
            rcases hx with hx | rfl | hx
            · exact hs _ (List.mem_append_left _ hx)
            · exact ih _ (by simp) _ hstep
            · exact hs _ (by simp [hx])
          · simpa only [List.length_append, List.length_cons] using hlen
          · simp only [List.length_append, List.length_cons]
            exact .refl _
    case decide ha hb hab t' hs =>
      cases hs with
      | decideLeft hs => cases hs
      | decideRight hs => cases hs
    case refl ha ih t' hs =>
      cases hs with
      | reflTerm hs =>
          exact .convert (.refl (ih _ hs)) (.eq (.symm hs.conversion) (.symm hs.conversion))
    case index ha hi hp iha ihi ihp t' hs =>
      cases hs with
      | indexArray hs => exact .index (iha _ hs) hi hp
      | indexIndex hs => exact .index ha (ihi _ hs) (.convert hp (.lt hs.conversion (.refl _)))
      | indexProof hs => exact .index ha hi (ihp _ hs)
    case lam hA he hb ihA ihb t' hs =>
      cases hs with
      | lamDomain hs =>
          exact .convert
            (.lam (ihA _ hs) (he.trans (hA.proposition_step hs).symm)
              (hb.context_conversion ((ContextConversion.refl _).extend hs.conversion)))
            (.pi (.symm hs.conversion) (.refl _))
      | lamBody hs => exact .lam hA he (ihb _ hs)
    case app hf ha ihf iha t' hs =>
      cases hs with
      | beta => exact hf.beta_contract ha
      | appFunction hs => exact .app (ihf _ hs) ha
      | appArgument hs =>
          exact .convert (.app hf (iha _ hs)) (.symm (Conv.instantiate_congr hs.conversion))
    case convert ht hc ih t' hs => exact .convert (ih _ hs) hc
  · intro Γ t A h
    induction h using HasType.rec
      (motive_1 := fun Γ A _ => ∀ A', Step A A' → IsType Γ A')
    case u64 A' hs => cases hs
    case i64 A' hs => cases hs
    case array hn ih A' hs =>
      cases hs with
      | array hs => exact .array (ih _ hs)
    case lt ha hb iha ihb A' hs =>
      cases hs with
      | ltLeft hs => exact .lt (iha _ hs) hb
      | ltRight hs => exact .lt ha (ihb _ hs)
    case eq ha hb iha ihb A' hs =>
      cases hs with
      | eqLeft hs => exact .eq (iha _ hs) hb
      | eqRight hs => exact .eq ha (ihb _ hs)
    case pi hA he hB ihA ihB A' hs =>
      cases hs with
      | piDomain hs =>
          exact .pi (ihA _ hs) (he.trans (hA.proposition_step hs).symm)
            (hB.context_conversion ((ContextConversion.refl _).extend hs.conversion))
      | piCodomain hs => exact .pi hA he (ihB _ hs)
    case var hx =>
      intro t' hs
      cases hs
    case natural hn =>
      intro t' hs
      cases hs
    case integer hlo hhi =>
      intro t' hs
      cases hs
    case uadd ha hb iha ihb =>
      intro t' hs
      cases hs with
      | uaddLeft hs => exact .uadd (iha _ hs) hb
      | uaddRight hs => exact .uadd ha (ihb _ hs)
    case usub ha hb hp iha ihb ihp =>
      intro t' hs
      cases hs with
      | usubLeft hs =>
          exact .usub (iha _ hs) hb
            (.convert hp (.lt (.refl _) (.uadd hs.conversion (.refl _))))
      | usubRight hs => exact .usub ha (ihb _ hs) (.convert hp (.lt hs.conversion (.refl _)))
      | usubProof hs => exact .usub ha hb (ihp _ hs)
    case elements xs Γ hs hlen ih =>
      intro t' hstep
      cases hstep with
      | elements pre post hstep =>
          refine HasType.convert (HasType.elements ?_ ?_) ?_
          · intro x hx
            simp only [List.mem_append, List.mem_cons] at hx
            rcases hx with hx | rfl | hx
            · exact hs _ (List.mem_append_left _ hx)
            · exact ih _ (by simp) _ hstep
            · exact hs _ (by simp [hx])
          · simpa only [List.length_append, List.length_cons] using hlen
          · simp only [List.length_append, List.length_cons]
            exact .refl _
    case decide ha hb hab =>
      intro t' hs
      cases hs with
      | decideLeft hs => cases hs
      | decideRight hs => cases hs
    case refl ha ih =>
      intro t' hs
      cases hs with
      | reflTerm hs =>
          exact .convert (.refl (ih _ hs)) (.eq (.symm hs.conversion) (.symm hs.conversion))
    case index ha hi hp iha ihi ihp =>
      intro t' hs
      cases hs with
      | indexArray hs => exact .index (iha _ hs) hi hp
      | indexIndex hs => exact .index ha (ihi _ hs) (.convert hp (.lt hs.conversion (.refl _)))
      | indexProof hs => exact .index ha hi (ihp _ hs)
    case lam hA he hb ihA ihb =>
      intro t' hs
      cases hs with
      | lamDomain hs =>
          exact .convert
            (.lam (ihA _ hs) (he.trans (hA.proposition_step hs).symm)
              (hb.context_conversion ((ContextConversion.refl _).extend hs.conversion)))
            (.pi (.symm hs.conversion) (.refl _))
      | lamBody hs => exact .lam hA he (ihb _ hs)
    case app hf ha ihf iha =>
      intro t' hs
      cases hs with
      | beta => exact hf.beta_contract ha
      | appFunction hs => exact .app (ihf _ hs) ha
      | appArgument hs =>
          exact .convert (.app hf (iha _ hs)) (.symm (Conv.instantiate_congr hs.conversion))
    case convert ht hc ih =>
      intro t' hs
      exact .convert (ih _ hs) hc


/-- Every contextual beta step preserves formed types, including annotations. -/
theorem IsType.preservation (h : IsType Γ A) (hs : Step A A') : IsType Γ A' :=
  preservation_mutual.1 _ _ h _ hs

/-- Fixed-type contextual beta preservation, now enabled by proved beta
conversion and context transport. The result type is the original raw syntax. -/
theorem HasType.preservation (h : HasType Γ t A) (hs : Step t t') : HasType Γ t' A :=
  preservation_mutual.2 _ _ _ h _ hs

/-- Finite contextual beta sequences. -/
inductive Steps : Raw → Raw → Prop where
  | refl : Steps t t
  | next : Step t u → Steps u v → Steps t v

theorem HasType.preservation_steps (h : HasType Γ t A) (hs : Steps t t') : HasType Γ t' A := by
  induction hs with
  | refl => exact h
  | next hs _ ih => exact ih (h.preservation hs)

theorem IsType.preservation_steps (h : IsType Γ A) (hs : Steps A A') : IsType Γ A' := by
  induction hs with
  | refl => exact h
  | next hs _ ih => exact ih (h.preservation hs)

end Jihoo.CoreBridge.Raw.Beta
