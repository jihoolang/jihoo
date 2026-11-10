import Jihoo.CoreSubtraction

/-! Pure local-array selection as contextual computation. This is an abstract
read semantics, not Core.normal's conversion algorithm or a heap semantics. -/
namespace Jihoo.CoreBridge.Raw.Beta

theorem Step.computation (h : Step t u) : Computation.Step t u := by
  induction h with
  | beta e A body a => exact .beta e A body a
  | elements pre post _ ih => exact .elements pre post ih
  | array _ ih => exact .array ih
  | ltLeft _ ih => exact .ltLeft ih
  | ltRight _ ih => exact .ltRight ih
  | eqLeft _ ih => exact .eqLeft ih
  | eqRight _ ih => exact .eqRight ih
  | piDomain _ ih => exact .piDomain ih
  | piCodomain _ ih => exact .piCodomain ih
  | lamDomain _ ih => exact .lamDomain ih
  | lamBody _ ih => exact .lamBody ih
  | appFunction _ ih => exact .appFunction ih
  | appArgument _ ih => exact .appArgument ih
  | indexArray _ ih => exact .indexArray ih
  | indexIndex _ ih => exact .indexIndex ih
  | indexProof _ ih => exact .indexProof ih
  | reflTerm _ ih => exact .reflTerm ih
  | zeroLe _ ih => exact .zeroLe ih
  | decideLeft _ ih => exact .decideLeft ih
  | decideRight _ ih => exact .decideRight ih
  | uaddLeft _ ih => exact .uaddLeft ih
  | uaddRight _ ih => exact .uaddRight ih
  | usubLeft _ ih => exact .usubLeft ih
  | usubRight _ ih => exact .usubRight ih
  | usubProof _ ih => exact .usubProof ih

theorem Steps.computation (h : Steps t u) : Computation.Steps t u := by
  induction h with
  | refl => exact .refl
  | next hs _ ih => exact .next hs.computation ih

/-- Closed typing derives the array bounds and selected entry. Only the finite
index evaluation is supplied; array head preparation and proof truth are derived. -/
theorem HasType.closed_index_computes
    (h : HasType (fun _ => none) (.index a i p) T)
    (hi : Computation.Steps i (.natural k)) :
    ∃ v, Computation.Steps (.index a i p) v ∧ HasType (fun _ => none) v T := by
  have prepare := hi.map (fun i => .index a i p) (fun hs => .indexIndex hs)
  obtain ⟨xs, v, ha, _, selected, typed⟩ :=
    (Computation.preservation_steps h prepare).closed_index_safe
  have array := ha.computation.map (fun a => .index a (.natural k) p)
    (fun hs => .indexArray hs)
  exact ⟨v, prepare.trans (array.trans (.next (.read xs k p v selected) .refl)), typed⟩

private theorem ListRel.lookup_none {k : Nat} (h : ListRel R xs ys)
    (selected : xs[k]? = none) : ys[k]? = none := by
  induction h generalizing k with
  | nil => rfl
  | cons hr hs ih =>
      cases k with
      | zero => simp at selected
      | succ k => exact ih selected

private theorem Par.invalid_read_shape {k : Nat} (selected : xs[k]? = none)
    (h : Par (.index (.elements xs) (.natural k) p) u) :
    ∃ ys q, u = .index (.elements ys) (.natural k) q ∧ ys[k]? = none := by
  cases h with
  | read _ _ _ _ _ found _ => rw [selected] at found; contradiction
  | index ha hi hp =>
      cases ha with
      | elements hs => cases hi; exact ⟨_, _, rfl, hs.lookup_none selected⟩

private theorem Star.invalid_read_shape (h : Star t u) :
    ∀ xs (k : Nat) p, t = .index (.elements xs) (.natural k) p → xs[k]? = none →
      ∃ ys q, u = .index (.elements ys) (.natural k) q ∧ ys[k]? = none := by
  induction h with
  | refl => intro xs k p ht hn; exact ⟨xs, p, ht, hn⟩
  | cons hs _ ih =>
      intro xs k p ht hn
      subst ht
      obtain ⟨ys, q, heq, hnone⟩ := hs.invalid_read_shape hn
      exact ih ys k q heq hnone

private theorem Star.integer_shape (h : Star t u) (ht : t = .integer z) :
    u = .integer z := by
  induction h with
  | refl => exact ht
  | cons hs _ ih => subst ht; cases hs; exact ih rfl

/-- Conversion cannot manufacture an integer for an out-of-range local read. -/
theorem Conv.invalid_read_not_integer {k : Nat} (selected : xs[k]? = none) :
    ¬ Conv (.index (.elements xs) (.natural k) p) (.integer z) := by
  intro hc
  obtain ⟨u, left, right⟩ := hc.church_rosser
  obtain ⟨ys, q, heq, _⟩ := left.invalid_read_shape xs k p rfl selected
  have same := heq.symm.trans (right.integer_shape rfl)
  contradiction

theorem Conv.integer_injective (h : Conv (.integer m) (.integer n)) : m = n := by
  obtain ⟨u, left, right⟩ := h.church_rosser
  exact Raw.integer.inj ((left.integer_shape rfl).symm.trans (right.integer_shape rfl))

/-- Successful literal selection has a unique integer result even under arbitrary
untyped beta expansion and reduction inside discarded proof/array positions. -/
theorem Conv.read_integer_unique {k : Nat} (selected : xs[k]? = some (.integer m))
    (h : Conv (.index (.elements xs) (.natural k) p) (.integer n)) : m = n :=
  ((Conv.read xs k p (.integer m) selected).symm.trans h).integer_injective

end Jihoo.CoreBridge.Raw.Beta
