import Jihoo.BoundedMir
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Jihoo.BoundedMir.Examples

/-- Exact retained 13-local/7-block O0 MIR shape exported from the compiler for
one Buffer1 allocation, scalar load, free and return. Block/local IDs are kept. -/
def single : Code := ⟨#[.i64, .u64, .u64, .ptr, .u64, .bool, .u64, .bool, .ptr, .ptr, .ptr, .i64, .unit], #[ ⟨#[⟨⟨1, false⟩, (.bin .mul (.constant (.u64 1)) (.constant (.u64 8)))⟩,
    ⟨⟨2, false⟩, (.bin .add (.copy ⟨1, false⟩) (.constant (.u64 8)))⟩], (.malloc (.copy ⟨2, false⟩) ⟨3, false⟩ 1)⟩, ⟨#[⟨⟨4, false⟩, (.ptrCast (.copy ⟨3, false⟩))⟩,
    ⟨⟨5, false⟩, (.bin .ne (.copy ⟨4, false⟩) (.constant (.u64 0)))⟩], (.assert (.copy ⟨5, false⟩) 2)⟩, ⟨#[⟨⟨6, false⟩, (.use (.constant (.u64 0)))⟩], (.goto 3)⟩, ⟨#[⟨⟨7, false⟩, (.bin .lt (.copy ⟨6, false⟩) (.constant (.u64 1)))⟩], (.switch (.copy ⟨7, false⟩) [(0, 5)] 4)⟩, ⟨#[⟨⟨8, false⟩, (.offset (.copy ⟨3, false⟩) (.copy ⟨6, false⟩))⟩,
    ⟨⟨8, true⟩, (.use (.constant (.i64 11)))⟩,
    ⟨⟨6, false⟩, (.bin .add (.copy ⟨6, false⟩) (.constant (.u64 1)))⟩], (.goto 3)⟩, ⟨#[⟨⟨9, false⟩, (.use (.copy ⟨3, false⟩))⟩,
    ⟨⟨10, false⟩, (.offset (.copy ⟨9, false⟩) (.constant (.u64 0)))⟩,
    ⟨⟨11, false⟩, (.use (.copy ⟨10, true⟩))⟩], (.free (.copy ⟨3, false⟩) ⟨12, false⟩ 6)⟩, ⟨#[⟨⟨0, false⟩, (.use (.copy ⟨11, false⟩))⟩], .ret⟩]⟩

def accepted : Accepted single := (admit single 1000).get (by decide +kernel)

theorem single_returns_payload : accepted.outcome.value = 11 := by decide +kernel

theorem exact_allocator_extent : accepted.outcome.events = [.alloc 0 16, .free 0] := by decide +kernel

theorem fill_initialized_first_cell :
    (accepted.outcome.frame.heap[0]?).map (fun obj => obj.cells) = some #[some 11, none] := by decide +kernel

theorem filled_object_is_dead :
    (accepted.outcome.frame.heap[0]?).map (fun obj => obj.alive) = some false := by decide +kernel

theorem concrete_steps : Steps single (.running (initial single)) accepted.outcome.events
    (.returned 11 accepted.outcome.frame) := by
  simpa [single_returns_payload] using accepted_execution accepted

theorem all_returns_payload (run : Steps single (.running (initial single)) events (.returned v f)) : v = 11 := by
  have h := (accepted_all_returns accepted run).1
  exact h.trans single_returns_payload

theorem all_returns_same_frame (run : Steps single (.running (initial single)) events (.returned v f)) :
    f = accepted.outcome.frame := (accepted_all_returns accepted run).2.1

theorem all_returns_no_live_heap (run : Steps single (.running (initial single)) events (.returned v f)) :
    heapEmpty f = true := accepted_all_return_heaps accepted run

theorem exact_statement_and_term_fuel : (execute 22 single (initial single)).isSome = true := by decide +kernel

theorem one_less_fuel_rejected : execute 21 single (initial single) = none := by decide +kernel

theorem zero_fuel_rejected : execute 0 single (initial single) = none := rfl

theorem oversized_fuel_rejected : (admit single 10001).isNone = true := by decide +kernel

def noInitialization : Code := {single with blocks := single.blocks.set! 2 ⟨#[⟨⟨6, false⟩, .use (.constant (.u64 0))⟩], .goto 5⟩}

theorem raw_malloc_is_not_initialized : (admit noInitialization 1000).isNone = true := by decide +kernel

def useAfterFree : Code := {single with blocks := single.blocks.set! 6 ⟨#[⟨⟨0, false⟩, .use (.copy ⟨3, true⟩)⟩], .ret⟩}

theorem dead_load_rejected : (admit useAfterFree 1000).isNone = true := by decide +kernel

def doubleFree : Code := {single with blocks := single.blocks.set! 6 ⟨#[], .free (.copy ⟨3, false⟩) ⟨12, false⟩ 6⟩}

theorem double_free_rejected : (admit doubleFree 1000).isNone = true := by decide +kernel

def leaked : Code := {single with blocks := single.blocks.set! 5 ⟨(single.blocks[5]).statements, .goto 6⟩}

theorem leaked_heap_rejected : (admit leaked 1000).isNone = true := by decide +kernel

def narrower : Code := {single with blocks := single.blocks.set! 0 ⟨#[⟨⟨2, false⟩, .use (.constant (.u64 8))⟩], .malloc (.copy ⟨2, false⟩) ⟨3, false⟩ 1⟩}

def narrowAccepted : Accepted narrower := (admit narrower 1000).get (by decide +kernel)

/-- A smaller successful allocation can return the same scalar; paired
validation must compare exact byte extents, not just allocation counts. -/
theorem different_extent_same_value : narrowAccepted.outcome.value = 11 ∧
    narrowAccepted.outcome.events = [.alloc 0 8, .free 0] := by decide +kernel

def uninitializedReturn : Code := ⟨#[.i64], #[⟨#[], .ret⟩]⟩

theorem uninitialized_return_rejected : (admit uninitializedReturn 100).isNone = true := by decide +kernel

def unreachableBadLocal : Code := {single with blocks := single.blocks.push ⟨#[⟨⟨999, false⟩, .use (.constant (.i64 0))⟩], .ret⟩}

theorem unreachable_local_rejected : valid unreachableBadLocal = false := by decide +kernel

def unreachableBadCast : Code := {single with blocks := single.blocks.push ⟨#[⟨⟨4, false⟩, .ptrCast (.constant (.i64 0))⟩], .ret⟩}

theorem unreachable_unsupported_cast_rejected : valid unreachableBadCast = false := by decide +kernel

def duplicateCases : Code := {single with blocks := single.blocks.set! 3 ⟨(single.blocks[3]).statements, .switch (.copy ⟨7, false⟩) [(0,5),(0,4)] 4⟩}

theorem duplicate_switch_values_rejected : valid duplicateCases = false := by decide +kernel

def liveHeap : Array Object := #[⟨true, #[some 11, none]⟩]

theorem interior_free_rejected : freeHeap liveHeap 0 1 = none := by decide +kernel

theorem uninitialized_spare_cell_rejected : load liveHeap 0 1 = none := by decide +kernel

theorem out_of_bounds_load_rejected : load liveHeap 0 2 = none := by decide +kernel

theorem huge_malloc_rejected_before_materializing : mallocHeap #[] wordBound = none := by decide +kernel

theorem excessive_total_cells_rejected :
    mallocHeap #[⟨false, Array.replicate 4096 none⟩] 16 = none := by decide +kernel

theorem byte_alignment_rejected : mallocHeap #[] 9 = none := by decide +kernel

theorem checked_u64_add_overflow : binary .add (.u64 (wordBound - 1)) (.u64 1) = none := by decide +kernel

theorem checked_u64_mul_overflow : binary .mul (.u64 (wordBound / 2)) (.u64 2) = none := by decide +kernel

theorem address_null_observation : binary .ne (.address 0) (.u64 0) = some (.boolean true) := rfl

theorem address_arithmetic_rejected : binary .add (.address 0) (.u64 1) = none := rfl

theorem address_ordering_rejected : binary .lt (.address 0) (.u64 1) = none := rfl

theorem address_nonzero_comparison_rejected : binary .ne (.address 0) (.u64 1) = none := rfl

end Jihoo.BoundedMir.Examples
