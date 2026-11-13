import Jihoo.CommonCompositionContract
namespace Jihoo.CommonCompositionContract

-- Concrete source subset checks, including a forbidden node.
theorem literal_supported : Supported #[.core (.integer 7)] 0 :=
  .literal rfl (by decide)
theorem opaque_rejected : ¬ Supported #[.core .opaque] 0 := by
  intro h
  cases h <;> simp [CommonDataSource.nodeAt] at *

-- The neutral seam really executes the bounded interpreter and preserves
-- the entire boundary, including nonempty inventories/frames when supplied.
theorem idle (a : Boundary) (p : ReferenceCalls.Program)
    (bound : ReferenceCalls.stackDepth a.target ≤ limit) :
    Transfer p limit 0 a a [] := by
  exact ⟨by simp [CommonDataCaseRelocation.walk, bound], id, rfl, rfl, rfl⟩

theorem two_idles (a : Boundary) (p : ReferenceCalls.Program)
    (bound : ReferenceCalls.stackDepth a.target ≤ limit) :
    Transfer p limit 0 a a [] := (idle a p bound).then (idle a p bound)

-- Compile the conditional A/B/C wiring without fabricating a provider.
example (A : EntryProvider) (i : CaseInput) x j l r rest limit
    (valid : i.before.Valid) (shape : i.before.images = .node x j l r :: rest)
    (reserved : CommonDataCaseEntryContext.Reserved i.before.ctx i.before.slots [0,1,2,3,4,5])
    (bound : i.before.target.stack.length ≤ limit)
    (body : BodyResult g term kind i.program limit n (i.nodeOut x j l r rest) c v se te slot)
    (finish : FinishResult i.program limit m c d shell tail kind v slot) :
    Transfer i.program limit (11+n+m) i.before d (te ++ [.free shell.target]) :=
  node_pipeline (A.node i x j l r rest limit valid shape reserved bound).2 body finish

#check TreeCreateContext.node_prefix_context
#check TreeCreateContext.nil_prefix_context
#check CommonDataCaseRelocation.node_entry
#check CommonDataCaseEntryContext.node_entry_context
#print axioms Transfer.then
#print axioms Transfer.steps
#print axioms node_pipeline
#print axioms supported_induction
#print axioms literal_supported
#print axioms opaque_rejected
#print axioms idle
#print axioms two_idles
end Jihoo.CommonCompositionContract
