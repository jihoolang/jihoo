import Jihoo.CommonLiteralBody
import Jihoo.CommonDataReferenceChecks

namespace Jihoo.CommonLiteralBody.Checks
open CommonCompositionContract CommonDataTargetContext RecursiveLexicalFields
open CommonDataReferenceChecks (source image)

def fn : ReferenceCalls.Function :=
  ⟨⟨⟨#[.i64,.i64], #[⟨#[], .ret⟩, block 1 7 2, ⟨#[], .goto 2⟩]⟩, #[]⟩, #[]⟩
def program : ReferenceCalls.Program := #[fn]
def caller : ReferenceCalls.Continuation := ⟨0, 2, #[some (.i64 31)], ⟨0,false⟩⟩
def before : Boundary :=
  { images := [], buffers := [], sizes := [], pending := [⟨7,3,image.object⟩],
    sf := [4], tf := [10], ctx := [.scalar,.ghost], env := [.scalar 77,.ghost],
    slots := [0,99], source := source,
    target := ⟨0, ⟨1,0,#[some (.i64 77),none],CommonDataReferenceChecks.heap⟩,[caller]⟩ }

theorem valid : before.Valid := by
  constructor
  · constructor
    · exact CommonDataReferenceChecks.source_valid
    · exact .cons ⟨77,rfl⟩ (.cons rfl .nil)
    · exact .cons ⟨77,rfl⟩ (.cons trivial .nil)
    · intro r hr; cases hr
    · refine ⟨by decide, ?_, ?_⟩
      · intro x hx
        change x ∈ [7,4] at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> rfl
      · simp [before, source, HeapLeases.Unborrowed]
    · decide
    · intro a ha
      have eq : a = ⟨7,3,image.object⟩ := by simpa [before] using ha
      subst a
      exact ⟨rfl,rfl,rfl⟩
  · exact ⟨rfl, by intro k x n hx; simp [before] at hx⟩

theorem fresh : Fresh before.ctx before.slots 1 := by
  intro k e slot _ hs _
  have mem := List.mem_of_getElem? hs
  simp [before] at mem
  omega

/-- Nonzero entry and continuation; active scalar survives; ghost slot is
out of bounds; pending shell, source/target frames and caller are nonempty. -/
theorem certificate : BodyResult #[.core (.integer 7)] 0 .scalar program 1 2
    before (out before 1 7 2) (.scalar 7) [] [] 1 :=
  literal before fn rfl (by decide) rfl rfl rfl valid fresh
    rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)

theorem preserved : (out before 1 7 2).target.frame.locals[0]? = some (some (.i64 77)) ∧
    (out before 1 7 2).target.stack = [caller] ∧
    (out before 1 7 2).pending = before.pending ∧
    (out before 1 7 2).target.frame.block = 2 := ⟨rfl,rfl,rfl,rfl⟩

theorem insufficient_budget : CommonDataCaseRelocation.walk program 2 0 before.target = none := by decide

theorem collision_rejected : ¬ Fresh before.ctx before.slots 0 := by
  intro h; exact h 0 .scalar 0 rfl rfl trivial rfl

theorem bad_continuation :
    ¬ 3 < fn.code.base.blocks.size := by decide

#print axioms literal
#print axioms run
#print axioms certificate
#print axioms preserved
#print axioms insufficient_budget
#print axioms collision_rejected
end Jihoo.CommonLiteralBody.Checks
