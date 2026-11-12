import Jihoo.CommonDataCoreErasure

/-! Determinism of the compact CommonData target, independently of source
execution, typing, lowering, and compiler success. This is uniqueness of
terminating runs, not a termination or memory-safety theorem. -/
namespace Jihoo.CommonDataCoreErasure
open RecursiveLexicalFields

/-- All terminating executions of the same target in the same environment and
initial state agree on the value, exact projected event trace, and entire final
state. No well-formedness or ownership premise is required. -/
theorem Eval.deterministic (first : Eval env term s v es t)
    (second : Eval env term s w fs u) : v = w ∧ es = fs ∧ t = u := by
  induction first generalizing w fs u with
  | scalarLet arg body ih =>
    cases second with
    | scalarLet otherArg otherBody =>
      obtain ⟨eq, rfl, rfl⟩ := SizedErasure.Eval.deterministic arg otherArg
      cases eq
      obtain ⟨rfl, rfl, rfl⟩ := ih otherBody
      exact ⟨rfl, rfl, rfl⟩
  -- A producer may perform arbitrary compact Core effects before returning
  -- its owner; both its full buffer state and its trace are aligned first.
  | ownerLet arg body ih =>
    cases second with
    | ownerLet otherArg otherBody =>
      obtain ⟨eq, rfl, rfl⟩ := SizedErasure.Eval.deterministic arg otherArg
      cases eq
      obtain ⟨rfl, rfl, rfl⟩ := ih otherBody
      exact ⟨rfl, rfl, rfl⟩
  | literal => cases second; exact ⟨rfl, rfl, rfl⟩
  | empty => cases second; exact ⟨rfl, rfl, rfl⟩
  | var lookup => cases second <;> try simp_all
  | construct left right => cases second <;> try simp_all
  | letData arg body argIH bodyIH =>
    cases second with
    | letData otherArg otherBody =>
      obtain ⟨eq, rfl, rfl⟩ := argIH otherArg
      cases eq
      obtain ⟨rfl, rfl, rfl⟩ := bodyIH otherBody
      exact ⟨rfl, rfl, rfl⟩
  | drop lookup destroyed body ih =>
    cases second <;> try simp_all
    rename_i otherDestroyed otherBody
    obtain ⟨rfl, rfl⟩ := CommonData.Destroy.deterministic destroyed otherDestroyed
    obtain ⟨rfl, rfl, rfl⟩ := ih otherBody
    exact ⟨rfl, rfl, rfl⟩
  | freeBuffer lookup body ih =>
    cases second <;> try simp_all
    exact ih (by assumption)
  -- The empty/node rules cannot overlap. Branch induction includes arbitrary
  -- nested cases, and node exit appends the same pending-parent release.
  | emptyCase lookup body ih =>
    cases second <;> try simp_all
    case emptyCase => exact ih (by assumption)
    case nodeCase => simp_all [RecursiveLexicalFields.enter]
  | nodeCase entered body ih =>
    cases second <;> try simp_all
    case emptyCase => simp_all [RecursiveLexicalFields.enter]
    case nodeCase =>
      obtain ⟨rfl, rfl, rfl⟩ := ih (by assumption)
      exact ⟨rfl, rfl, rfl⟩

end Jihoo.CommonDataCoreErasure
