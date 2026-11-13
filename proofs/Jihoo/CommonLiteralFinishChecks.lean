import Jihoo.CommonLiteralBodyChecks
import Jihoo.CommonDataInstalledFinish

/-! Literal/free composition starts with an already pending shell, not a
Case node entry: that entry still owns two child images. -/
namespace Jihoo.CommonLiteralFinishChecks
open CommonCompositionContract CommonDataTargetContext RecursiveLexicalFields
open CommonLiteralBody CommonDataInstalledFinish CommonDataBranchFinish

def before : Boundary :=
  { CommonLiteralBody.Checks.before with target :=
    { CommonLiteralBody.Checks.before.target with frame :=
      { CommonLiteralBody.Checks.before.target.frame with locals :=
        #[some (.i64 77), none, some (.pointer 3 0), some (.i64 123)] } } }
def fn : ReferenceCalls.Function :=
  ⟨⟨⟨#[.i64,.i64,.ptr,.unit], #[⟨#[], .ret⟩, block 1 7 2,
    ⟨#[], .free (.copy ⟨2,false⟩) ⟨3,false⟩ 3⟩, ⟨#[], .goto 3⟩]⟩, #[]⟩, #[]⟩
def program : ReferenceCalls.Program := #[fn]
def shell : Pending := ⟨7,3,CommonDataReferenceChecks.image.object⟩
def middle := out before 1 7 2
def after := finished middle shell [] (stopped middle shell 3 3)

theorem valid : before.Valid := by
  have old := CommonLiteralBody.Checks.valid
  exact ⟨{ old.toContext with bindings := .cons ⟨77,rfl⟩ (.cons trivial .nil) }, old.bufferSizes⟩

theorem body : BodyResult #[.core (.integer 7)] 0 .scalar program 1 2
    before middle (.scalar 7) [] [] 1 :=
  literal before fn rfl (by decide) rfl rfl rfl valid CommonLiteralBody.Checks.fresh
    rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)

theorem site : Site program middle shell 2 3 3 := by
  exact ⟨⟨fn,rfl,rfl,rfl,rfl,by decide⟩,rfl,by decide⟩

theorem reserved : CommonDataCaseEntryContext.Reserved middle.ctx middle.slots [3] := by
  intro k e slot _ hs _
  have member := List.mem_of_getElem? hs
  change slot ∈ [0,99] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide

/-- Both certificates are constructed; neither is a premise. -/
theorem combined : Transfer program 1 3 before after [.free 3] ∧
    FinishResult program 1 1 middle after shell [] .scalar (.scalar 7) 1 := by
  exact installed_body_finish valid body rfl site (by decide) reserved (by decide)

theorem final_valid : after.Valid := combined.1.context valid

theorem result : Local after.target.frame 1 (.i64 7) :=
  live_result_preserved (tail := []) body
    (installed_live_execution site (body.transfer.context valid) rfl (by decide) reserved (by decide))

theorem reduction : CommonDataCaseRelocation.walk program 3 1 before.target =
    some (after.target, [.free 3]) := by decide

theorem scratch_changed : before.target.frame.locals[3]? = some (some (.i64 123)) ∧
    after.target.frame.locals[3]? = some (some .unit) := by decide

/-- The literal constructor cannot be applied immediately after Node entry. -/
theorem node_inventory_nonempty (i : CaseInput) (x j : Nat)
    (l r : CommonDataReference.Image) (rest : List CommonDataReference.Image) :
    (i.nodeOut x j l r rest).images ≠ [] := by
  simp [CaseInput.nodeOut]

#print axioms node_inventory_nonempty
#print axioms valid
#print axioms body
#print axioms site
#print axioms reserved
#print axioms combined
#print axioms final_valid
#print axioms result
#print axioms reduction
#print axioms scratch_changed
#check @combined
end Jihoo.CommonLiteralFinishChecks
