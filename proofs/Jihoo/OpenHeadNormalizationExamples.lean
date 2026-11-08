import Jihoo.OpenHeadNormalization

namespace Jihoo.CoreBridge.Raw.Beta.OpenNormalizationExamples

private def naturals : Raw.Context := Raw.Context.extend (fun _ => none) .u64
private theorem naturals_formed : FormedContext naturals := .extend .empty .u64
private def identity : Raw := .lam false .u64 (.var 0)
private def iterated : Nat → Raw
  | 0 => .var 0
  | n + 1 => .app identity (iterated n)
private theorem identity_typed : HasType naturals identity (.pi false .u64 .u64) :=
  .lam .u64 rfl (.var (by simp [Raw.Context.extend, Raw.rename]))
private theorem iterated_typed (n : Nat) : HasType naturals (iterated n) .u64 := by
  induction n with
  | zero => exact .var (by simp [naturals, Raw.Context.extend, Raw.rename])
  | succ n ih => simpa [iterated, subst] using HasType.app identity_typed ih

/-- The variable remains open; there is no producer fuel or substituted value
in the statement of the resulting normalization theorem. -/
theorem arbitrary_open_chain (n : Nat) :
    ∃ u, Steps (iterated n) u ∧ headNormal u = true ∧ HasType naturals u .u64 :=
  (iterated_typed n).typed_head_normalizes naturals_formed

theorem beyond_producer_fuel :
    ∃ u, Steps (iterated 65) u ∧ headNormal u = true ∧ HasType naturals u .u64 :=
  arbitrary_open_chain 65

private def functions : Raw.Context :=
  (Raw.Context.extend (fun _ => none) (.pi false .u64 .u64)).extend .u64
private theorem functions_formed : FormedContext functions :=
  .extend (.extend .empty (.pi .u64 rfl .u64)) .u64
private def higher : Raw :=
  .app (.lam false (.pi false .u64 .u64) (.app (.var 0) (.var 1))) (.var 1)
private theorem higher_typed : HasType functions higher .u64 := by
  have hf : HasType (functions.extend (.pi false .u64 .u64)) (.var 0)
      (.pi false .u64 .u64) := .var (by simp [Raw.Context.extend, Raw.rename])
  have hx : HasType (functions.extend (.pi false .u64 .u64)) (.var 1) .u64 :=
    .var (by simp [functions, Raw.Context.extend, Raw.rename])
  have body : HasType (functions.extend (.pi false .u64 .u64))
      (.app (.var 0) (.var 1)) .u64 := by simpa [Raw.subst] using HasType.app hf hx
  have arg : HasType functions (.var 1) (.pi false .u64 .u64) :=
    .var (by simp [functions, Raw.Context.extend, Raw.rename])
  simpa [higher, Raw.subst, Raw.proposition] using HasType.app (HasType.lam (.pi .u64 rfl .u64) rfl body) arg

theorem open_higher_order_normalizes :
    ∃ u, Steps higher u ∧ headNormal u = true ∧ HasType functions u .u64 :=
  higher_typed.typed_head_normalizes functions_formed

private def dependent : Raw.Context := naturals.extend (.eq (.var 0) (.var 0))
private theorem dependent_formed : FormedContext dependent :=
  .extend naturals_formed (.eq (.var (by simp [naturals, Raw.Context.extend, Raw.rename]))
    (.var (by simp [naturals, Raw.Context.extend, Raw.rename])))

theorem dependent_evidence_context :
    ∃ u, Steps (.var 0) u ∧ headNormal u = true ∧
      HasType dependent u (.eq (.var 1) (.var 1)) :=
  (HasType.var (Γ := dependent) (A := .eq (.var 1) (.var 1)) (x := 0)
    (by simp [dependent, Raw.Context.extend, Raw.rename])).typed_head_normalizes dependent_formed

private def falseContext : Raw.Context :=
  Raw.Context.extend (fun _ => none) (.eq (.natural 0) (.natural 1))
private theorem falseContext_formed : FormedContext falseContext :=
  .extend .empty (.eq (.natural (n := 0) (by decide)) (.natural (n := 1) (by decide)))

/-- Open normalization must not be confused with truth of open assumptions.
A false proposition is a formed type and can be hypothesized in a telescope. -/
theorem false_hypothesis_still_normalizes :
    (∃ u, Steps (.var 0) u ∧ headNormal u = true ∧
      HasType falseContext u (.eq (.natural 0) (.natural 1))) ∧ (0 : Nat) ≠ 1 := by
  exact ⟨(HasType.var (Γ := falseContext) (A := .eq (.natural 0) (.natural 1)) (x := 0)
      (by simp [falseContext, Raw.Context.extend, Raw.rename])).typed_head_normalizes falseContext_formed,
    by decide⟩

/-- Closing can introduce a new redex; reflection does not assume an inverse
step simulation or that an open normal form stays normal after substitution. -/
theorem closing_can_introduce_redex :
    headNormal (.app (.var 0) (.natural 7)) = true ∧
      SimpleErasure.SimpleStep
        ((SimpleErasure.Term.app (.var 0) .atom).subst
          (fun _ => SimpleErasure.Term.lam (.var 0))) .atom := by
  constructor
  · rfl
  · exact .beta

private def delta : Raw := .lam false .u64 (.app (.var 0) (.var 0))
private def omega : Raw := .app delta delta

/-- A real infinite head reduction remains outside the theorem, rather than
being declared normal by erasure or bounded search exhaustion. -/
theorem untyped_loop_not_accessible : ¬ Acc (fun u v => SimpleErasure.HeadStep v u) omega := by
  have loop : SimpleErasure.HeadStep omega omega := by
    simpa [omega, delta, Raw.subst, Raw.single] using
      (SimpleErasure.HeadStep.beta (e := false) (A := .u64)
        (body := .app (.var 0) (.var 0)) (a := delta))
  have irreflexive : ∀ t, Acc (fun u v => SimpleErasure.HeadStep v u) t →
      ¬ SimpleErasure.HeadStep t t := by
    intro t h
    induction h with
    | intro t _ ih =>
        intro step
        exact ih t step step
  exact fun h => irreflexive omega h loop

theorem looping_term_not_typable (hΓ : FormedContext Γ) : ¬ HasType Γ omega A :=
  fun h => untyped_loop_not_accessible (h.head_accessible hΓ)

end Jihoo.CoreBridge.Raw.Beta.OpenNormalizationExamples
