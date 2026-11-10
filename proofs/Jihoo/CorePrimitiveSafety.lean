import Jihoo.CoreBridgeClosedNormalization
import Jihoo.CoreBridgeComputation

/-! Closed primitive safety from the higher-order declarative typing derivation.
No normalization premise is placed on proof terms. These results concern local
array reads and unsigned subtraction, not heap ownership or compiler lowering. -/
namespace Jihoo.CoreBridge.Raw.Beta

private def PrimitiveInversion (Γ : Context) (t T : Raw) : Prop :=
  match t with
  | .natural n => n < wordBound ∧ Conv .u64 T
  | .elements xs => (∀ x ∈ xs, HasType Γ x .i64) ∧ xs.length < wordBound ∧
      Conv (.array (.natural xs.length)) T
  | .index a i p => ∃ n, HasType Γ a (.array n) ∧ HasType Γ i .u64 ∧
      HasType Γ p (.lt i n) ∧ Conv .i64 T
  | .usub a b p => HasType Γ a .u64 ∧ HasType Γ b .u64 ∧
      HasType Γ p (.lt b (.uadd a (.natural 1))) ∧ Conv .u64 T
  | _ => True

private theorem PrimitiveInversion.convert (h : PrimitiveInversion Γ t A) (hc : Conv A B) :
    PrimitiveInversion Γ t B := by
  cases t <;> first | trivial | simp only [PrimitiveInversion] at h ⊢
  case natural => exact ⟨h.1, h.2.trans hc⟩
  case elements => exact ⟨h.1, h.2.1, h.2.2.trans hc⟩
  case index => obtain ⟨n, ha, hi, hp, hT⟩ := h; exact ⟨n, ha, hi, hp, hT.trans hc⟩
  case usub => exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans hc⟩

private theorem primitive_inversion (h : HasType Γ t T) : PrimitiveInversion Γ t T := by
  induction h using HasType.rec (motive_1 := fun _ _ _ => True) <;> first | trivial | skip
  case natural h => exact ⟨h, .refl _⟩
  case elements hs hlen _ => exact ⟨hs, hlen, .refl _⟩
  case index ha hi hp _ _ _ => exact ⟨_, ha, hi, hp, .refl _⟩
  case usub ha hb hp _ _ _ => exact ⟨ha, hb, hp, .refl _⟩
  case convert _ hc ih => exact ih.convert hc

theorem HasType.natural_bound (h : HasType Γ (.natural n) T) : n < wordBound :=
  (primitive_inversion h).1

/-- Conversion at any point in the typing derivation is retained. -/
theorem HasType.elements_inversion (h : HasType Γ (.elements xs) T) :
    (∀ x ∈ xs, HasType Γ x .i64) ∧ xs.length < wordBound ∧
      Conv (.array (.natural xs.length)) T := primitive_inversion h

theorem HasType.index_inversion (h : HasType Γ (.index a i p) T) :
    ∃ n, HasType Γ a (.array n) ∧ HasType Γ i .u64 ∧
      HasType Γ p (.lt i n) ∧ Conv .i64 T := primitive_inversion h

theorem HasType.usub_inversion (h : HasType Γ (.usub a b p) T) :
    HasType Γ a .u64 ∧ HasType Γ b .u64 ∧
      HasType Γ p (.lt b (.uadd a (.natural 1))) ∧ Conv .u64 T := primitive_inversion h

private theorem closed_array_head (h : HasType Γ t T) : Γ = (fun _ => none) →
    headNormal t = true → ∀ n, Conv T (.array n) →
      ∃ xs, t = .elements xs ∧ (∀ x ∈ xs, HasType (fun _ => none) x .i64) ∧
        xs.length < wordBound ∧ Conv (.natural xs.length) n := by
  induction h using HasType.rec (motive_1 := fun _ _ _ => True)
  case u64 | i64 | array | lt | eq | pi => trivial
  case var hx => intro hΓ _; rw [hΓ] at hx; cases hx
  case natural | integer | uadd | usub | index | decide | refl | zeroLe | lam =>
    intro _ _ n hc
    have bad := hc.rigid_head rfl rfl
    contradiction
  case elements hs hlen _ =>
    intro hΓ _ n hc
    subst hΓ
    exact ⟨_, rfl, hs, hlen, hc.array_injective⟩
  case app hf ha _ _ =>
    intro hΓ hn n hc
    rw [hΓ] at hf
    have hnf := (Bool.and_eq_true_iff.mp hn).1
    obtain ⟨e, A, body, he⟩ := (hf.head_canonical hnf).1 _ _ _ (.refl _)
    subst he
    change false = true at hn
    contradiction
  case convert _ hc ih =>
    intro hΓ hn n hnT
    exact ih hΓ hn n (hc.trans hnT)

/-- Every closed array producer, including higher-order beta applications,
reaches Elements. Its entries remain typed; its length is derived from typing. -/
theorem HasType.closed_array (h : HasType (fun _ => none) a (.array n)) :
    ∃ xs, Steps a (.elements xs) ∧ (∀ x ∈ xs, HasType (fun _ => none) x .i64) ∧
      xs.length < wordBound ∧ Conv (.natural xs.length) n := by
  obtain ⟨u, steps, normal⟩ := h.closed_head_normalizes
  obtain ⟨xs, rfl, typed, bound, length⟩ :=
    closed_array_head (h.preservation_steps steps) rfl normal n (.refl _)
  exact ⟨xs, steps, typed, bound, length⟩

/-- An unchecked array read is ready after the array's head-beta preparation.
This is a selection specification, not a new Core.normal reduction rule. -/
def ArrayRead (a : Raw) (k : Nat) (v : Raw) : Prop :=
  ∃ xs, Steps a (.elements xs) ∧ xs[k]? = some v

/-- Proof normalization and a bound premise are not supplied by the caller.
Closed typing derives the actual array length, an in-range index, a selected
entry, and typing of that entry at the original (possibly converted) result. -/
theorem HasType.closed_index_safe (h : HasType (fun _ => none) (.index a (.natural k) p) T) :
    ∃ xs v, Steps a (.elements xs) ∧ k < xs.length ∧ xs[k]? = some v ∧
      HasType (fun _ => none) v T := by
  obtain ⟨n, ha, _, hp, result⟩ := h.index_inversion
  obtain ⟨xs, steps, typed, _, length⟩ := ha.closed_array
  have hp' : HasType (fun _ => none) p (.lt (.natural k) (.natural xs.length)) :=
    .convert hp (.lt (.refl _) length.symm)
  have bound := hp'.closed_literal_lt
  exact ⟨xs, xs[k], steps, bound, by simp [bound],
    .convert (typed _ (List.getElem_mem bound)) result⟩

theorem HasType.closed_read_progress (h : HasType (fun _ => none) (.index a (.natural k) p) T) :
    ∃ v, ArrayRead a k v ∧ HasType (fun _ => none) v T := by
  obtain ⟨xs, v, steps, _, selected, typed⟩ := h.closed_index_safe
  exact ⟨v, ⟨xs, steps, selected⟩, typed⟩

/-- The maximum-word case is handled from the operand bounds. It does not
silently assume a+1 is a representable literal or truncate the ghost bound. -/
theorem HasType.closed_usub_safe
    (h : HasType (fun _ => none) (.usub (.natural a) (.natural b) p) T) :
    b ≤ a ∧ a - b < wordBound ∧ HasType (fun _ => none) (.natural (a - b)) T := by
  obtain ⟨ha, hb, hp, result⟩ := h.usub_inversion
  have hwa := (primitive_inversion ha).1
  have hwb := (primitive_inversion hb).1
  have safe : b ≤ a := by
    by_cases hw : a + 1 < wordBound
    · have hlt : HasType (fun _ => none) p (.lt (.natural b) (.natural (a + 1))) :=
        .convert hp (.lt (.refl _) (.add a 1 hw))
      have := hlt.closed_literal_lt
      omega
    · omega
  have bound : a - b < wordBound := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hwa
  exact ⟨safe, bound, .convert (.natural bound) result⟩

/-- Mathematical word subtraction agrees with ordinary natural subtraction;
no saturating/underflow behavior is being used to justify an unsafe operand. -/
theorem HasType.closed_usub_reconstructs
    (h : HasType (fun _ => none) (.usub (.natural a) (.natural b) p) T) :
    (a - b) + b = a := Nat.sub_add_cancel h.closed_usub_safe.1

/-- Contextual beta/add/subtract evaluations of operands can be transported into the
primitive theorem. The finite operand evaluation premise is explicit; no
universal arithmetic normalization or runtime evaluator correspondence is claimed. -/
theorem HasType.evaluated_index_safe
    (h : HasType (fun _ => none) (.index a i p) T)
    (hi : Computation.Steps i (.natural k)) :
    ∃ v, ArrayRead a k v ∧ HasType (fun _ => none) v T := by
  have h' := Computation.preservation_steps h
    (hi.map (fun x => .index a x p) (fun hx => .indexIndex hx))
  exact h'.closed_read_progress

theorem HasType.evaluated_usub_safe
    (h : HasType (fun _ => none) (.usub a b p) T)
    (ha : Computation.Steps a (.natural x)) (hb : Computation.Steps b (.natural y)) :
    y ≤ x ∧ x - y < wordBound ∧ HasType (fun _ => none) (.natural (x - y)) T := by
  have h' := Computation.preservation_steps h
    (ha.map (fun t => .usub t b p) (fun ht => .usubLeft ht))
  have h'' := Computation.preservation_steps h'
    (hb.map (fun t => .usub (.natural x) t p) (fun ht => .usubRight ht))
  exact h''.closed_usub_safe

end Jihoo.CoreBridge.Raw.Beta
