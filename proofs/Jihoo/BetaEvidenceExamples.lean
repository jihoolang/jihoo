import Jihoo.TypingEvidence

namespace Jihoo.CoreBridge.Raw.Beta.EvidenceExamples

private def redex : Raw := .app (.lam false .u64 (.var 0)) (.natural 7)

private theorem redex_typed : HasType (fun _ => none) redex .u64 := by
  have hf : HasType (fun _ => none) (.lam false .u64 (.var 0)) (.pi false .u64 .u64) :=
    .lam .u64 rfl (.var (by simp [Context.extend, rename]))
  simpa [redex, subst] using (HasType.app hf (HasType.natural (n := 7) (by decide +kernel)))

private theorem redex_converts : Conv redex (.natural 7) := by
  simpa [redex, subst, single] using (Conv.beta false .u64 (.var 0) (.natural 7))

/-- The indices remain unnormalized: only the evidence's function spine is
observed. Conversion soundness here follows from Church–Rosser injectivity. -/
theorem nonnormal_index_evidence :
    HasType (fun _ => none) (.refl redex) (.eq (.natural 7) (.natural 7)) :=
  .convert (.refl redex_typed) (.eq redex_converts redex_converts)

theorem nonnormal_index_truth : (7 : Nat) = 7 :=
  nonnormal_index_evidence.head_literal_eq rfl

private def expandedType : Raw := .app (.lam false .u64 .u64) (.natural 0)

theorem expanded_type_convertible : Conv expandedType .u64 := by
  simpa [expandedType, subst] using (Conv.beta false .u64 .u64 (.natural 0))

theorem expanded_type_not_formed : ¬ IsType Γ expandedType := by
  intro h
  cases h

/-- A concrete reason the skeleton theorem needs BOTH formation hypotheses. -/
theorem arbitrary_expansion_changes_skeleton :
    skeleton expandedType = none ∧ skeleton .u64 = some .u64 := ⟨rfl, rfl⟩

theorem higher_order_skeleton :
    skeleton (.pi false (.pi false .u64 .u64) (.eq (.natural 0) (.natural 0))) =
      some (.pi false (.pi false .u64 .u64) .eq) := rfl

theorem no_head_false_lt (h : HasType (fun _ => none) t (.lt (.natural 3) (.natural 2))) :
    headNormal t ≠ true := by
  intro hn
  have := h.head_literal_lt hn
  omega

theorem no_head_false_eq (h : HasType (fun _ => none) t (.eq (.natural 0) (.natural 1))) :
    headNormal t ≠ true := by
  intro hn
  have := h.head_literal_eq hn
  contradiction

theorem normal_neutral_is_not_closed_typed :
    ¬ HasType (fun _ => none) (.app (.var 0) (.natural 7)) (.eq (.natural 0) (.natural 1)) := by
  intro h
  exact no_head_false_eq h rfl

end Jihoo.CoreBridge.Raw.Beta.EvidenceExamples

namespace Jihoo.GraphCertificates.Typing.Evidence.Examples
open Typing.Wire

private def typing : Typing.Certificate := {
  graph := #[.u64, .natural 7, .refl 1, .eq 1 1]
  termRoot := 2, typeRoot := 3, typingStep := 1, formationStep := 2
  steps := [⟨11, [], 1, 0, []⟩, ⟨17, [], 2, 3, [0]⟩, ⟨4, [], 3, 3, [0, 0]⟩] }
private def snapshot : Snapshot := ⟨2, 3, typing.graph⟩

theorem false_equality_rejected : validate s c (.equal 0 1) = false :=
  false_claim_rejected (by simp [Claim.Holds])

theorem false_bound_rejected : validate s c (.less n n) = false :=
  false_claim_rejected (Nat.lt_irrefl n)

#eval show IO Unit from do
  let falseSnapshot : Snapshot := ⟨3, 4, #[.u64, .natural 0, .natural 1, .refl 1, .eq 1 2]⟩
  unless observe falseSnapshot (.equal 0 1) do
    throw (IO.userError "observer unexpectedly decides arithmetic truth")
  unless validateBytes (encodeSnapshot snapshot) (Typing.Wire.encode typing) (.equal 7 7) do
    throw (IO.userError "true literal evidence rejected")
  if validate snapshot typing (.equal 8 8) then
    throw (IO.userError "different true proposition substituted")
  if validate snapshot typing (.less 7 8) then
    throw (IO.userError "different proposition constructor substituted")
  if validate { snapshot with termRoot := 1 } typing (.equal 7 7) then
    throw (IO.userError "changed evidence root accepted")
  if validate { snapshot with graph := snapshot.graph.push .prop } typing (.equal 7 7) then
    throw (IO.userError "changed unreachable graph accepted")

end Jihoo.GraphCertificates.Typing.Evidence.Examples
