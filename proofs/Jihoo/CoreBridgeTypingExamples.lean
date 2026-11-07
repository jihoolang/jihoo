import Jihoo.CoreBridgeTyping
import Jihoo.CoreBridgeExamples

namespace Jihoo.CoreBridge

private def seven : Index := .lit ⟨7, by decide⟩
private def signedSeven : Signed := ⟨7, by decide⟩

/-- Dependency on the lambda-bound index appears in the inferred result type. -/
theorem identityProof_typed : SourceTyping 0 [] identityProof
    (.pi (.eq (.var 0) (.var 0))) := by
  exact .lam (.refl (by simp [Index.Scoped]))

/-- An index binder, erased evidence-value let, then another index binder.
The proof variable must move behind the second unified binder. -/
theorem mixedProof_typed : SourceTyping 0 [] mixedProof
    (.pi (.pi (.eq (.var 1) (.var 1)))) := by
  refine .lam (.letValue ?_ (.refl ?_) (.lam (.var rfl ?_)))
  all_goals simp [Ty.Scoped, Index.Scoped]

theorem nestedValues_typed : SourceTyping 0 [] nestedValues .i64 := by
  exact .letValue trivial .integer (.letValue trivial .integer (.var rfl trivial))

theorem arrayRead_typed : SourceTyping 0 [] arrayRead .i64 := by
  refine .letValue trivial (.elements _ (by decide))
    (.index (.var rfl trivial) trivial .decide)

/-- Both mixed lets and ordinary dependent applications are covered, not merely
closed literal terms or nondependent function types. -/
theorem dependentApplication_typed : SourceTyping 0 [] (.app identityProof seven)
    (.eq seven seven) := by
  exact .app identityProof_typed trivial

theorem nestedDependentApplication_typed : SourceTyping 0 [] (.app mixedProof seven)
    (.pi (.eq seven seven)) := by
  exact .app mixedProof_typed trivial

theorem mixedProof_target : Raw.HasType (fun _ => none)
    (.lam false .u64 (.app (.lam true (.eq (.var 0) (.var 0))
      (.lam false .u64 (.var 1))) (.refl (.var 0))))
    (.pi false .u64 (.pi false .u64 (.eq (.var 1) (.var 1)))) :=
  mixedProof_typed.translate_closed

theorem dependentApplication_target : Raw.HasType (fun _ => none)
    ((Term.app mixedProof seven).encode id id)
    (.pi false .u64 (.eq (.natural 7) (.natural 7))) :=
  nestedDependentApplication_typed.translate_closed

example : Indexed.ScopedTyping 0 [] mixedProof.erase
    (.pi (.pi (.eq (.var 1) (.var 1)))) := mixedProof_typed.erase_closed

example : Raw.HasType (fun _ => none)
    ((Term.natural (.closedSub 10 3 (by decide) (by decide))).encode id id) .u64 :=
  (SourceTyping.natural (n := 0) (Γ := [])
    (a := .closedSub 10 3 (by decide) (by decide)) trivial).translate_closed

example : Raw.HasType (fun _ => none)
    ((Term.natural (.add (.lit ⟨wordBound - 1, by decide⟩) (.lit ⟨1, by decide⟩))).encode id id)
    .u64 :=
  (SourceTyping.natural (n := 0) (Γ := [])
    (a := .add (.lit ⟨wordBound - 1, by decide⟩) (.lit ⟨1, by decide⟩))
    ⟨trivial, trivial⟩).translate_closed

/-- Erasure alone accepts this I64 value despite its false U64 annotation. -/
def wrongAnnotation : Term := .letValue .u64 (.integer signedSeven) (.var 0)

example : Indexed.HasType (Indexed.complete []) wrongAnnotation.erase .i64 :=
  .letValue (.integer _ _) (.param _ _)

/-- The checked source judgment rejects that exact annotated syntax at EVERY
claimed result type. This catches the gap that scope and erasure cannot catch. -/
theorem wrongAnnotation_rejected (A : Ty) : ¬ SourceTyping 0 [] wrongAnnotation A := by
  intro h
  cases h with
  | letValue _ hv _ => cases hv

example (A : Ty) : ¬ SourceTyping 0 [] (.var 0) A := by
  intro h
  cases h with
  | var hx _ => simp at hx

-- Zero-le is an explicit coverage omission, not a claimed counterexample to
-- core soundness: the core reasons symbolically about arithmetic successors.
-- No admission or hidden target premise brings this constructor into the theorem.
example (a : Index) (A : Ty) : ¬ SourceTyping 0 [] (.zeroLe a) A := by
  intro h
  cases h

/-- Every declaration actually emitted by EmitCore has a checked source
annotation and therefore an independent target typing derivation. Parser/checker
agreement for the serialized file remains a separately executable regression. -/
theorem generatedExamples_typed (entry : String × Ty × Term) (h : entry ∈ examples) :
    SourceTyping 0 [] entry.2.2 entry.2.1 := by
  simp only [examples, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact identityProof_typed
  · exact mixedProof_typed
  · exact nestedValues_typed
  · exact dependentApplication_typed
  · exact nestedDependentApplication_typed
  · exact arrayRead_typed
  · exact .natural trivial
  · exact .natural trivial
  · exact .natural ⟨trivial, trivial⟩
  · exact .natural trivial
  · exact .integer
  · exact .integer

theorem generatedExamples_target (entry : String × Ty × Term) (h : entry ∈ examples) :
    Raw.HasType (fun _ => none) (entry.2.2.encode id id) (entry.2.1.encode id) :=
  (generatedExamples_typed entry h).translate_closed

end Jihoo.CoreBridge
