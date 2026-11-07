import Jihoo.CoreBridgeBetaTyping

/-! Consequences of the existing untyped Church–Rosser theorem. No semantic
interpretation or normalization hypothesis is added to conversion. -/
namespace Jihoo.CoreBridge.Raw.Beta

/-- Heads of formed types. Indices are deliberately not interpreted here. -/
def typeHead : Raw → Option Nat
  | .u64 => some 0
  | .i64 => some 1
  | .array _ => some 2
  | .lt _ _ => some 3
  | .eq _ _ => some 4
  | .pi _ _ _ => some 5
  | _ => none

theorem Par.type_head (h : Par t u) (ht : typeHead t = some k) :
    typeHead u = some k := by
  cases h <;> simp_all [typeHead]

theorem Star.type_head (h : Star t u) (ht : typeHead t = some k) :
    typeHead u = some k := by
  induction h with
  | refl => exact ht
  | cons hp _ ih => exact ih (hp.type_head ht)

/-- Both endpoints must have rigid heads: arbitrary beta expansion does not
preserve the syntactic head of an arbitrary raw term. -/
theorem Conv.rigid_head (h : Conv t u)
    (ht : typeHead t = some k) (hu : typeHead u = some l) : k = l := by
  obtain ⟨w, hw, hw'⟩ := h.church_rosser
  exact Option.some.inj ((hw.type_head ht).symm.trans (hw'.type_head hu))

private theorem Star.eq_shape (h : Star t u) : ∀ {a b}, t = .eq a b →
    ∃ a' b', u = .eq a' b' ∧ Star a a' ∧ Star b b' := by
  induction h with
  | refl =>
      intro a b ht
      exact ⟨a, b, ht, .refl, .refl⟩
  | cons hp _ ih =>
      intro a b ht
      subst ht
      cases hp with
      | eq ha hb =>
          obtain ⟨a'', b'', hu, ha', hb'⟩ := ih rfl
          exact ⟨a'', b'', hu, .cons ha ha', .cons hb hb'⟩

theorem Conv.eq_injective (h : Conv (.eq a b) (.eq a2 b2)) :
    Conv a a2 ∧ Conv b b2 := by
  obtain ⟨w, hw, hw'⟩ := h.church_rosser
  obtain ⟨wa, wb, heq, ha, hb⟩ := hw.eq_shape rfl
  obtain ⟨za, zb, heq', ha2, hb2⟩ := hw'.eq_shape rfl
  have same := heq.symm.trans heq'
  cases same
  exact ⟨.trans ha.conv (.symm ha2.conv), .trans hb.conv (.symm hb2.conv)⟩

private theorem Star.lt_shape (h : Star t u) : ∀ {a b}, t = .lt a b →
    ∃ a' b', u = .lt a' b' ∧ Star a a' ∧ Star b b' := by
  induction h with
  | refl =>
      intro a b ht
      exact ⟨a, b, ht, .refl, .refl⟩
  | cons hp _ ih =>
      intro a b ht
      subst ht
      cases hp with
      | lt ha hb =>
          obtain ⟨a'', b'', hu, ha', hb'⟩ := ih rfl
          exact ⟨a'', b'', hu, .cons ha ha', .cons hb hb'⟩

theorem Conv.lt_injective (h : Conv (.lt a b) (.lt a2 b2)) :
    Conv a a2 ∧ Conv b b2 := by
  obtain ⟨w, hw, hw'⟩ := h.church_rosser
  obtain ⟨wa, wb, heq, ha, hb⟩ := hw.lt_shape rfl
  obtain ⟨za, zb, heq', ha2, hb2⟩ := hw'.lt_shape rfl
  have same := heq.symm.trans heq'
  cases same
  exact ⟨.trans ha.conv (.symm ha2.conv), .trans hb.conv (.symm hb2.conv)⟩

private theorem Star.array_shape (h : Star t u) : ∀ {a}, t = .array a →
    ∃ a', u = .array a' ∧ Star a a' := by
  induction h with
  | refl =>
      intro a ht
      exact ⟨a, ht, .refl⟩
  | cons hp _ ih =>
      intro a ht
      subst ht
      cases hp with
      | array ha =>
          obtain ⟨a'', hu, ha'⟩ := ih rfl
          exact ⟨a'', hu, .cons ha ha'⟩

theorem Conv.array_injective (h : Conv (.array a) (.array a2)) :
    Conv a a2 := by
  obtain ⟨w, hw, hw'⟩ := h.church_rosser
  obtain ⟨wa, heq, ha⟩ := hw.array_shape rfl
  obtain ⟨za, heq', ha2⟩ := hw'.array_shape rfl
  have same := heq.symm.trans heq'
  cases same
  exact .trans ha.conv (.symm ha2.conv)

private theorem Star.natural_shape (h : Star t u) (ht : t = .natural n) :
    u = .natural n := by
  induction h with
  | refl => exact ht
  | cons hp _ ih =>
      subst ht
      cases hp
      exact ih rfl

theorem Conv.natural_injective (h : Conv (.natural m) (.natural n)) : m = n := by
  obtain ⟨w, hw, hw'⟩ := h.church_rosser
  exact Raw.natural.inj ((hw.natural_shape rfl).symm.trans (hw'.natural_shape rfl))

/-- Structural type information; scalar indices are erased, but higher-order
Pi domains/codomains and their binder modes are retained. -/
inductive Skeleton where
  | u64 | i64 | array | lt | eq
  | pi : Bool → Skeleton → Skeleton → Skeleton
  deriving DecidableEq, Repr

def skeleton : Raw → Option Skeleton
  | .u64 => some .u64
  | .i64 => some .i64
  | .array _ => some .array
  | .lt _ _ => some .lt
  | .eq _ _ => some .eq
  | .pi e A B => do
      let a ← skeleton A
      let b ← skeleton B
      pure (.pi e a b)
  | _ => none

private theorem skeleton_conversion : ∀ Γ A, IsType Γ A →
    ∀ Δ B, IsType Δ B → Conv A B → skeleton A = skeleton B := by
  intro Γ A hA
  induction hA using IsType.rec (motive_2 := fun _ _ _ _ => True)
  case u64 | i64 | array | lt | eq =>
    intro Δ B hB hc
    cases hB <;> first | rfl | (have hh := hc.rigid_head rfl rfl; contradiction)
  case pi hA he hB ihA ihB =>
    intro Δ C hC hc
    cases hC <;> try (have hh := hc.rigid_head rfl rfl; contradiction)
    case pi hD heD hE =>
      obtain ⟨hee, hd, he⟩ := hc.pi_injective
      simp only [skeleton]
      rw [hee, ihA _ _ heD hd, ihB _ _ hE he]
  all_goals trivial

/-- Both endpoints are independently formed. This theorem intentionally makes
no assertion about the syntactic skeleton of an arbitrary beta expansion. -/
theorem IsType.skeleton_conversion (hA : IsType Γ A) (hB : IsType Δ B)
    (hc : Conv A B) : skeleton A = skeleton B := Jihoo.CoreBridge.Raw.Beta.skeleton_conversion _ _ hA _ _ hB hc

theorem IsType.skeleton_exists (hA : IsType Γ A) : ∃ s, skeleton A = some s := by
  induction hA using IsType.rec (motive_2 := fun _ _ _ _ => True)
  case u64 | i64 | array | lt | eq => exact ⟨_, rfl⟩
  case pi hA he hB ihA ihB =>
    obtain ⟨a, ha⟩ := ihA
    obtain ⟨b, hb⟩ := ihB
    exact ⟨.pi _ a b, by simp [skeleton, ha, hb]; rfl⟩
  all_goals trivial

end Jihoo.CoreBridge.Raw.Beta
