import Jihoo.CommonDataCoreCompilerCompleteness
import Jihoo.CommonDataCoreErasureChecks

namespace Jihoo.CommonDataCoreCompilerChecks
open CommonDataCoreErasure

/-- Dynamic producers and delayed frees keep their full Core argument grammar. -/
theorem dynamic_producer :
    (compileTarget CommonDataBufferProducerChecks.delayedNodes 64
      [true,true,true,true,true,true] [false,true,true,true,true,true] 33).isSome = true := by decide +kernel

theorem dynamic_allocation :
    (compileTarget CommonDataBufferChecks.nodes 64 [true,true] [false,true] 17).isSome = true := by decide +kernel

theorem owned_lend_case :
    (compileTarget SymbolicCompositionChecks.commonGraph 128
      [true,true,true,true,true] [true,true,true,true,false] 93).isSome = true := by decide +kernel

def twoMasks : CommonDataSource.Graph := #[
  .core (.var 1), .core .i64, .core (.integer 7),
  .core (.lam false 1 2), .core (.app 3 0)]

theorem different_masks : compileTarget twoMasks 2 [true,true] [false,true] 4 =
    some (.scalarLet (.var 0) (.literal 7)) := by decide +kernel

theorem core_slot_unavailable : compileTarget twoMasks 2 [true,true] [true,false] 4 = none := by decide +kernel

theorem common_slot_unavailable : compileTarget twoMasks 1 [true,false] [true,true] 0 = none := by decide +kernel

theorem missing_slot : compileTarget twoMasks 1 [] [true,true] 0 = none := by decide +kernel

def caseGraph : CommonDataSource.Graph := #[
  .ind 0 [], .core .i64, .core (.lam false 0 1),
  .core (.integer 7), .core (.var 0), .core (.var 1), .con 0 1 [4,5],
  .core (.lam false 0 6), .core (.lam false 0 7),
  .caseOf 0 2 [3,8] 4]

theorem both_case_branches : compileTarget caseGraph 2 [true] [false] 9 =
    some (.caseTree 0 (.literal 7) (.construct 0 1)) := by decide +kernel

theorem bad_nil_branch : compileTarget (caseGraph.set! 3 (.core .opaque)) 8 [true] [false] 9 = none := by decide +kernel

theorem bad_node_branch : compileTarget (caseGraph.set! 6 (.core .opaque)) 8 [true] [false] 9 = none := by decide +kernel

theorem bad_motive : compileTarget (caseGraph.set! 2 (.core .opaque)) 8 [true] [false] 9 = none := by decide +kernel

theorem bad_branch_binders : compileTarget (caseGraph.set! 7 (.core (.lam true 0 6))) 8 [true] [false] 9 = none := by decide +kernel

theorem bad_case_arity : compileTarget (caseGraph.push (.caseOf 0 2 [3] 4)) 8 [true] [false] 10 = none := by decide +kernel

theorem bad_constructor : compileTarget #[.con 0 1 []] 8 [] [] 0 = none := by decide +kernel

theorem missing_root : compileTarget #[] 8 [] [] 0 = none := by decide +kernel

theorem zero_fuel : compileTarget g 0 slots mask root = none := rfl

theorem insufficient_fuel : compileTarget caseGraph 1 [true] [false] 9 = none := by decide +kernel

/-- A cyclic recursive edge consumes its budget and fails; no general cyclic
normalization or native compiler refinement is claimed. -/
theorem cycle_exhausts : compileTarget #[.core (.var 0), .drop 0 0 1] 32 [true] [false] 1 = none := by decide +kernel

def deepGraph : Nat → CommonDataSource.Graph
  | 0 => #[.core (.var 0), .core (.integer 7)]
  | n+1 => (deepGraph n).push (.drop 0 0 (n+1))

def deepTarget : Nat → Term
  | 0 => .literal 7
  | n+1 => .drop 0 (deepTarget n)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem deep_nesting : compileTarget (deepGraph 64) 65 [true] [false] 65 = some (deepTarget 64) := by decide +kernel

set_option maxRecDepth 4096 in
theorem deep_insufficient : compileTarget (deepGraph 64) 64 [true] [false] 65 = none := by decide +kernel

theorem typed_dynamic : ∃ target bound, ∀ fuel, bound ≤ fuel →
    compileTarget CommonDataBufferChecks.nodes fuel [true,true] [false,true] 17 = some target := by
  apply typing_compiles CommonDataBufferChecks.symbolic_lifecycle
  intro k e h
  match k with
  | 0 | 1 => cases h; trivial
  | k+2 => simp at h

end Jihoo.CommonDataCoreCompilerChecks
