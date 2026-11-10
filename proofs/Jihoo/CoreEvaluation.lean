import Jihoo.CoreArrayReduction

/-! A strict pure evaluation strategy with explicit unsigned-addition traps.
This is not an implementation refinement or a heap/ownership semantics. -/
namespace Jihoo.CoreBridge.Raw.Beta.Evaluation

inductive Value : Raw → Prop where
  | natural (n) : Value (.natural n)
  | integer (n) : Value (.integer n)
  | lam (e A body) : Value (.lam e A body)
  | elements : (∀ x ∈ xs, Value x) → Value (.elements xs)
  | refl (a) : Value (.refl a)
  | zeroLe (a) : Value (.zeroLe a)
  | decide (a b) : Value (.decide (.natural a) (.natural b))

/-- Frames select the next runtime position, left-to-right. No proof or type
annotation frame exists, and erased applications do not evaluate their argument. -/
inductive Frame where
  | appFunction (a : Raw)
  | appArgument (A body : Raw)
  | uaddLeft (b : Raw)
  | uaddRight (a : Nat)
  | usubLeft (b p : Raw)
  | usubRight (a : Nat) (p : Raw)
  | indexArray (i p : Raw)
  | indexIndex (xs : List Raw) (p : Raw) (ready : ∀ x ∈ xs, Value x)
  | elements (pre post : List Raw) (ready : ∀ x ∈ pre, Value x)

def Frame.fill : Frame → Raw → Raw
  | .appFunction a, f => .app f a
  | .appArgument A body, a => .app (.lam false A body) a
  | .uaddLeft b, a => .uadd a b
  | .uaddRight a, b => .uadd (.natural a) b
  | .usubLeft b p, a => .usub a b p
  | .usubRight a p, b => .usub (.natural a) b p
  | .indexArray i p, a => .index a i p
  | .indexIndex xs p _, i => .index (.elements xs) i p
  | .elements pre post _, x => .elements (pre ++ x :: post)

inductive Step : Raw → Raw → Prop where
  | betaRuntime : Value a →
      Step (.app (.lam false A body) a) (body.subst (single a))
  | betaErased : Step (.app (.lam true A body) a) (body.subst (single a))
  | add : a + b < wordBound → Step (.uadd (.natural a) (.natural b)) (.natural (a + b))
  | sub : b ≤ a → a < wordBound →
      Step (.usub (.natural a) (.natural b) p) (.natural (a - b))
  | read : (∀ x ∈ xs, Value x) → xs[k]? = some v →
      Step (.index (.elements xs) (.natural k) p) v
  | context (f : Frame) : Step t u → Step (f.fill t) (f.fill u)

inductive Trap : Raw → Prop where
  | overflow : wordBound ≤ a + b → Trap (.uadd (.natural a) (.natural b))
  | context (f : Frame) : Trap t → Trap (f.fill t)

theorem Step.computation (h : Step t u) : Computation.Step t u := by
  induction h with
  | betaRuntime => exact .beta _ _ _ _
  | betaErased => exact .beta _ _ _ _
  | add h => exact .add _ _ h
  | sub hb ha => exact .subLiteral _ _ _ hb ha
  | read _ selected => exact .read _ _ _ _ selected
  | context f _ ih =>
      cases f with
      | appFunction => exact .appFunction ih
      | appArgument => exact .appArgument ih
      | uaddLeft => exact .uaddLeft ih
      | uaddRight => exact .uaddRight ih
      | usubLeft => exact .usubLeft ih
      | usubRight => exact .usubRight ih
      | indexArray => exact .indexArray ih
      | indexIndex => exact .indexIndex ih
      | elements pre post _ => exact .elements pre post ih

theorem preservation (h : HasType Γ t A) (hs : Step t u) : HasType Γ u A :=
  Computation.preservation h hs.computation

theorem Step.not_value (h : Step t u) : ¬ Value t := by
  induction h with
  | betaRuntime | betaErased | add | sub | read => intro hv; cases hv
  | context f _ ih =>
      cases f <;> intro hv <;> cases hv
      case elements.elements ready => exact ih (ready _ (by simp))

theorem Trap.not_value (h : Trap t) : ¬ Value t := by
  induction h with
  | overflow => intro hv; cases hv
  | context f _ ih =>
      cases f <;> intro hv <;> cases hv
      case elements.elements ready => exact ih (ready _ (by simp))

private theorem Value.head_normal (h : Value t) : headNormal t = true := by
  cases h <;> rfl

private theorem natural_canonical (h : HasType Γ t A) :
    Value t → Conv A .u64 → ∃ n, t = .natural n := by
  induction h using HasType.rec (motive_1 := fun _ _ _ => True)
  case u64 | i64 | array | lt | eq | pi => trivial
  case var | uadd | usub | index | app => intro hv; cases hv
  case natural => intros; exact ⟨_, rfl⟩
  case integer | elements | decide | refl | zeroLe | lam =>
    intro _ hc
    have := hc.rigid_head rfl rfl
    contradiction
  case convert _ hc ih => intro hv hc'; exact ih hv (hc.trans hc')

private theorem array_canonical (h : HasType Γ t A) :
    Value t → ∀ n, Conv A (.array n) → ∃ xs, t = .elements xs ∧ ∀ x ∈ xs, Value x := by
  induction h using HasType.rec (motive_1 := fun _ _ _ => True)
  case u64 | i64 | array | lt | eq | pi => trivial
  case var | uadd | usub | index | app => intro hv; cases hv
  case elements => intro hv n _; cases hv with | elements ready => exact ⟨_, rfl, ready⟩
  case natural | integer | decide | refl | zeroLe | lam =>
    intro _ n hc
    have := hc.rigid_head rfl rfl
    contradiction
  case convert _ hc ih => intro hv n hc'; exact ih hv n (hc.trans hc')



/-- Final values, an available runtime step, or an explicit arithmetic trap. -/
def Outcome (t : Raw) : Prop := Value t ∨ (∃ u, Step t u) ∨ Trap t

private inductive Sequence : List Raw → Prop where
  | done : (∀ x ∈ xs, Value x) → Sequence xs
  | step (pre post) : (∀ x ∈ pre, Value x) → Step a b → Sequence (pre ++ a :: post)
  | trap (pre post) : (∀ x ∈ pre, Value x) → Trap a → Sequence (pre ++ a :: post)

private theorem sequence_ready (xs : List Raw) (h : ∀ x ∈ xs, Outcome x) : Sequence xs := by
  induction xs with
  | nil => exact .done (by simp)
  | cons x xs ih =>
      rcases h x (by simp) with hv | ⟨y, hs⟩ | ht
      · have rest := ih (fun y hy => h y (by simp [hy]))
        cases rest with
        | done ready => exact .done (by simpa using And.intro hv ready)
        | step pre post ready hs =>
          exact .step (x :: pre) post (by simpa using And.intro hv ready) hs
        | trap pre post ready ht =>
          exact .trap (x :: pre) post (by simpa using And.intro hv ready) ht
      · exact .step [] xs (by simp) hs
      · exact .trap [] xs (by simp) ht

private theorem progress_aux (h : HasType Γ t A) : Γ = (fun _ => none) → Outcome t := by
  induction h using HasType.rec (motive_1 := fun _ _ _ => True)
  case u64 | i64 | array | lt | eq | pi => trivial
  case var hx => intro hΓ; rw [hΓ] at hx; cases hx
  case natural => intro _; exact .inl (.natural _)
  case integer => intro _; exact .inl (.integer _)
  case decide => intro _; exact .inl (.decide _ _)
  case refl => intro _; exact .inl (.refl _)
  case zeroLe => intro _; exact .inl (.zeroLe _)
  case lam => intro _; exact .inl (.lam _ _ _)
  case convert _ _ ih => exact ih
  case elements xs Γ hs hlen ih =>
    intro hΓ
    have ready := sequence_ready xs (fun x hx => ih x hx hΓ)
    cases ready with
    | done ready => exact .inl (.elements ready)
    | step pre post ready hstep => exact .inr (.inl ⟨_, .context (.elements pre post ready) hstep⟩)
    | trap pre post ready ht => exact .inr (.inr (.context (.elements pre post ready) ht))
  case uadd ha hb iha ihb =>
    intro hΓ; subst hΓ
    rcases iha rfl with va | ⟨a', hs⟩ | ht
    · obtain ⟨x, rfl⟩ := natural_canonical ha va (.refl _)
      rcases ihb rfl with vb | ⟨b', hs⟩ | ht
      · obtain ⟨y, rfl⟩ := natural_canonical hb vb (.refl _)
        by_cases bound : x + y < wordBound
        · exact .inr (.inl ⟨_, .add bound⟩)
        · exact .inr (.inr (.overflow (Nat.le_of_not_gt bound)))
      · exact .inr (.inl ⟨_, .context (.uaddRight x) hs⟩)
      · exact .inr (.inr (.context (.uaddRight x) ht))
    · exact .inr (.inl ⟨_, .context (.uaddLeft _) hs⟩)
    · exact .inr (.inr (.context (.uaddLeft _) ht))
  case usub ha hb hp iha ihb ihp =>
    intro hΓ; subst hΓ
    rcases iha rfl with va | ⟨a', hs⟩ | ht
    · obtain ⟨x, rfl⟩ := natural_canonical ha va (.refl _)
      rcases ihb rfl with vb | ⟨b', hs⟩ | ht
      · obtain ⟨y, rfl⟩ := natural_canonical hb vb (.refl _)
        have safe := (HasType.usub ha hb hp).closed_usub_safe
        exact .inr (.inl ⟨_, .sub safe.1 ha.natural_bound⟩)
      · exact .inr (.inl ⟨_, .context (.usubRight x _) hs⟩)
      · exact .inr (.inr (.context (.usubRight x _) ht))
    · exact .inr (.inl ⟨_, .context (.usubLeft _ _) hs⟩)
    · exact .inr (.inr (.context (.usubLeft _ _) ht))
  case index ha hi hp iha ihi ihp =>
    intro hΓ; subst hΓ
    rcases iha rfl with va | ⟨a', hs⟩ | ht
    · obtain ⟨xs, rfl, ready⟩ := array_canonical ha va _ (.refl _)
      rcases ihi rfl with vi | ⟨i', hs⟩ | ht
      · obtain ⟨k, rfl⟩ := natural_canonical hi vi (.refl _)
        have length := ha.elements_inversion.2.2.array_injective
        have bound := (HasType.convert hp (.lt (.refl _) length.symm)).closed_literal_lt
        exact .inr (.inl ⟨xs[k], .read ready (by simp [bound])⟩)
      · exact .inr (.inl ⟨_, .context (.indexIndex xs _ ready) hs⟩)
      · exact .inr (.inr (.context (.indexIndex xs _ ready) ht))
    · exact .inr (.inl ⟨_, .context (.indexArray _ _) hs⟩)
    · exact .inr (.inr (.context (.indexArray _ _) ht))
  case app hf ha ihf iha =>
    intro hΓ; subst hΓ
    rcases ihf rfl with vf | ⟨f', hs⟩ | ht
    · obtain ⟨e, D, body, rfl⟩ := (hf.head_canonical vf.head_normal).1 _ _ _ (.refl _)
      cases e with
      | true => exact .inr (.inl ⟨_, .betaErased⟩)
      | false =>
        rcases iha rfl with va | ⟨a', hs⟩ | ht
        · exact .inr (.inl ⟨_, .betaRuntime va⟩)
        · exact .inr (.inl ⟨_, .context (.appArgument D body) hs⟩)
        · exact .inr (.inr (.context (.appArgument D body) ht))
    · exact .inr (.inl ⟨_, .context (.appFunction _) hs⟩)
    · exact .inr (.inr (.context (.appFunction _) ht))

/-- Every closed well-typed term in the Beta fragment is a value, can take a
strict runtime step, or has an explicitly propagated unsigned-addition trap. -/
theorem progress (h : HasType (fun _ => none) t A) : Outcome t := progress_aux h rfl

inductive Steps : Raw → Raw → Prop where
  | refl : Steps t t
  | next : Step t u → Steps u v → Steps t v

theorem preservation_steps (h : HasType Γ t A) (hs : Steps t u) : HasType Γ u A := by
  induction hs with
  | refl => exact h
  | next hs _ ih => exact ih (preservation h hs)

/-- All finite strict executions retain typing and cannot end in an unexplained
stuck state. This permits explicit overflow traps and does not assert termination. -/
theorem execution_safety (h : HasType (fun _ => none) t A) (hs : Steps t u) :
    HasType (fun _ => none) u A ∧ Outcome u :=
  ⟨preservation_steps h hs, progress (preservation_steps h hs)⟩

end Jihoo.CoreBridge.Raw.Beta.Evaluation
