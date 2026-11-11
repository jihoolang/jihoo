import Jihoo.SymbolicMirEntryExamples

/-! Kernel-checked regressions for the generated root-40 program and its actual
ABI. Boundary theorem consumption avoids evaluating thousands of fill steps. -/
namespace Jihoo.SymbolicMirEntryChecks
open BoundedMir SizedMir SymbolicMirEntryExamples
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Observe both the returned heap/lifecycle and the unchanged ABI inputs. -/
def observe (fuel n i value : Nat) :
    Option (Nat × Array Object × List Event × List (Option Value)) := do
  let f ← entryFrame code abi [.i64 value,.u64 i,.u64 n]
  let out ← runFor fuel code (.running f)
  let .returned result final := out.machine | none
  return (result, final.heap, out.events, (final.locals.toList.drop 1).take 3)

theorem zero_length : observe 100 0 0 42 =
    some (99,#[⟨false,#[none]⟩],[.alloc 0 8,.free 0],
      [some (.u64 0),some (.u64 0),some (.i64 42)]) := by decide +kernel

theorem in_bounds : observe 100 2 1 42 =
    some (42,#[⟨false,#[some 42,some 42,none]⟩],[.alloc 0 24,.free 0],
      [some (.u64 2),some (.u64 1),some (.i64 42)]) := by decide +kernel

theorem equal_length : observe 100 2 2 42 =
    some (99,#[⟨false,#[some 42,some 42,none]⟩],[.alloc 0 24,.free 0],
      [some (.u64 2),some (.u64 2),some (.i64 42)]) := by decide +kernel

theorem outside_length : observe 100 2 3 42 =
    some (99,#[⟨false,#[some 42,some 42,none]⟩],[.alloc 0 24,.free 0],
      [some (.u64 2),some (.u64 3),some (.i64 42)]) := by decide +kernel

theorem maximum_payload : observe 100 1 0 (scalarBound - 1) =
    some (scalarBound - 1,#[⟨false,#[some (scalarBound - 1),none]⟩],
      [.alloc 0 16,.free 0],[some (.u64 1),some (.u64 0),some (.i64 (scalarBound - 1))]) := by
  decide +kernel

theorem maximum_index : observe 100 1 (wordBound - 1) 42 =
    some (99,#[⟨false,#[some 42,none]⟩],[.alloc 0 16,.free 0],
      [some (.u64 1),some (.u64 (wordBound - 1)),some (.i64 42)]) := by decide +kernel

theorem natural_overflow_rejected :
    entryFrame code abi [.i64 42,.u64 wordBound,.u64 1] = none := by decide +kernel

theorem length_overflow_rejected :
    entryFrame code abi [.i64 42,.u64 0,.u64 wordBound] = none := by decide +kernel

theorem scalar_overflow_rejected :
    entryFrame code abi [.i64 scalarBound,.u64 0,.u64 1] = none := by decide +kernel

theorem wrong_type_rejected :
    entryFrame code abi [.u64 42,.u64 0,.u64 1] = none := by decide +kernel

theorem short_arity_rejected :
    entryFrame code abi [.i64 42,.u64 0] = none := by decide +kernel

theorem extra_arity_rejected :
    entryFrame code abi [.i64 42,.u64 0,.u64 1,.u64 2] = none := by decide +kernel

/-- One tick executes the wrapper jump, leaving a successful running prefix. -/
theorem short_fuel_partial :
    (do let f ← entryFrame code abi [.i64 42,.u64 0,.u64 1]
        let out ← runFor 1 code (.running f)
        pure (match out.machine with | .running _ => true | _ => false, out.events)) =
      some (true,[]) := by decide +kernel

theorem short_fuel_no_return : observe 1 1 0 42 = none := by decide +kernel

/-- At the abstract allocator's capacity edge, the universal theorem constructs
termination and a final source-related heap without a large kernel simulation. -/
theorem capacity_edge :
    ∃ f final,
      entryFrame code abi [.i64 (scalarBound - 1),.u64 4094,.u64 4095] = some f ∧
      Steps code (.running f) [.alloc 0 32768,.free 0]
        (.returned (scalarBound - 1) final) ∧
      HeapRel (SizedCoreExamples.bodyFinal 4095 4094 (scalarBound - 1)) final.heap := by
  obtain ⟨f, final, admitted, _, _, _, target, heap, _⟩ :=
    total (n := 4095) (i := 4094) (value := scalarBound - 1)
      (by decide) (by decide) (by decide)
  exact ⟨f, final, admitted, by simpa using target, heap⟩

/-- Width-valid ABI admission does not itself prove allocator adequacy. -/
theorem over_capacity_still_admitted :
    (entryFrame code abi [.i64 0,.u64 0,.u64 4096]).isSome = true := by decide +kernel

theorem over_capacity_not_bounded :
    ¬ Trace.Bounds (SizedCoreExamples.bodyFinal 4096 0 0) := by
  intro bounds
  have cells := bounds.cells
  change 4097 ≤ 4096 at cells
  omega

end Jihoo.SymbolicMirEntryChecks
