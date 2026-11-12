import Jihoo.ReferenceCalls
import Jihoo.ReferenceCfgChecks

namespace Jihoo.ReferenceCalls.Checks
open ReferenceCfg

def arg (n : Nat) : Operand := .copy ⟨n, false⟩

/-- Fixed four-block function, recursively walking a nullable linked chain.
The parent is freed before calling the same code on the saved child reference. -/
def chainFunction : Function := ⟨⟨⟨#[.ptr, .ptr, .i64, .bool, .unit], #[
  ⟨#[⟨⟨3, false⟩, .nullTest (arg 0)⟩], .switch (arg 3) [(1, 3)] 1⟩,
  ⟨#[⟨⟨2, false⟩, .use (.copy ⟨0, true⟩)⟩,
      ⟨⟨1, false⟩, .wordToPointer (arg 2)⟩], .free (arg 0) ⟨4, false⟩ 2⟩,
  ⟨#[], .ret⟩, ⟨#[], .ret⟩]⟩,
  #[none, none, some (.call ⟨0, #[arg 1], ⟨4, false⟩, 3⟩), some .retUnit]⟩, #[0]⟩
def chain : Program := #[chainFunction]
def chainHeap : ReferenceHeap.Heap :=
  #[⟨true, #[some (.reference (.object 1 0))]⟩, ⟨true, #[some (.reference .null)]⟩]
def chainStart : State := ⟨0, ⟨0, 0, #[some (.pointer 0 0), none, none, none, none], chainHeap⟩, []⟩
def chainFinal : State := ⟨0, ⟨3, 0,
  #[some (.pointer 0 0), some (.pointer 1 0), some (.referenceWord (.object 1 0)),
    some (.boolean false), some .unit],
  #[⟨false, #[some (.reference (.object 1 0))]⟩, ⟨false, #[some (.reference .null)]⟩]⟩, []⟩

theorem recursive_chain_exact : execute 17 chain chainStart =
    some ⟨.unit, chainFinal, [.free 0, .free 1]⟩ := by decide +kernel
theorem recursive_chain_fuel_boundary : execute 16 chain chainStart = none := by decide +kernel
theorem recursive_chain_steps : Steps chain (.running chainStart)
    [.free 0, .free 1] (.returned .unit chainFinal) := execute_sound recursive_chain_exact

def writer : Function := ⟨⟨⟨#[.ptr], #[
  ⟨#[⟨⟨0, true⟩, .use (.constant (.i64 42))⟩], .ret⟩]⟩,
  #[some .retUnit]⟩, #[0]⟩
def reader : Function := ⟨⟨⟨#[.i64, .ptr, .unit], #[
  ⟨#[], .ret⟩, ⟨#[⟨⟨0, false⟩, .use (.copy ⟨1, true⟩)⟩], .ret⟩]⟩,
  #[some (.call ⟨1, #[arg 1], ⟨2, false⟩, 1⟩)]⟩, #[]⟩
def sharing : Program := #[reader, writer]
def sharingStart : State := ⟨0, ⟨0, 0, #[none, some (.pointer 0 0), none],
  #[⟨true, #[some (.scalar 7)]⟩]⟩, []⟩
def sharingFinal : State := ⟨0, ⟨1, 1, #[some (.i64 42), some (.pointer 0 0), some .unit],
  #[⟨true, #[some (.scalar 42)]⟩]⟩, []⟩
def writerCall : Call := ⟨1, #[arg 1], ⟨2, false⟩, 1⟩

theorem shared_write_exact : execute 5 sharing sharingStart =
    some ⟨.i64 42, sharingFinal, []⟩ := by decide +kernel
theorem shared_write_needs_return : execute 4 sharing sharingStart = none := by decide +kernel
theorem call_depth_and_heap : (enter sharing sharingStart writerCall).map
    (fun s => (stackDepth s, s.frame.heap)) = some (1, sharingStart.frame.heap) := by decide +kernel

theorem unknown_function : enter sharing sharingStart {writerCall with function := 2} = none := by decide +kernel
theorem wrong_arity : enter sharing sharingStart {writerCall with arguments := #[]} = none := by decide +kernel
theorem wrong_type : enter sharing sharingStart {writerCall with arguments := #[.constant (.i64 0)]} = none := by decide +kernel
theorem bad_continuation : enter sharing sharingStart {writerCall with continuation := 2} = none := by decide +kernel
theorem bad_destination : enter sharing sharingStart {writerCall with destination := ⟨0, false⟩} = none := by decide +kernel
theorem deref_destination : enter sharing sharingStart {writerCall with destination := ⟨1, true⟩} = none := by decide +kernel
theorem duplicate_parameters : enter #[reader, {writer with parameters := #[0, 0]}] sharingStart
    {writerCall with arguments := #[arg 1, arg 1]} = none := by decide +kernel
theorem unknown_parameter : enter #[reader, {writer with parameters := #[9]}] sharingStart writerCall = none := by decide +kernel
theorem uninitialized_argument : enter sharing sharingStart {writerCall with arguments := #[arg 0]} = none := by decide +kernel

def scalarCallee : Function := ⟨embedCode ⟨#[.i64], #[
  ⟨#[⟨⟨0, false⟩, .use (.constant (.i64 3))⟩], .ret⟩]⟩, #[]⟩
theorem internal_scalar_return_rejected : execute 10
    #[{reader with code.exits := #[some (.call {writerCall with arguments := #[]})]}, scalarCallee]
    sharingStart = none := by decide +kernel

theorem override_does_not_skip_statement : extension writer.code
    ⟨0, 0, #[some (.pointer 0 0)], sharingStart.frame.heap⟩ = none := by decide +kernel
theorem override_does_not_rescue_bad_pc : extension writer.code
    ⟨0, 2, #[some (.pointer 0 0)], sharingStart.frame.heap⟩ = none := by decide +kernel

theorem old_cycle_preserved : execute 8 (embedProgram ReferenceCfg.Checks.cycle)
    (embedState (ReferenceCfg.initial ReferenceCfg.Checks.cycle)) =
    some (embedOutcome ⟨7, ReferenceCfg.Checks.cycleFinal, [.alloc 0 8, .free 0]⟩) := by
  rw [execute_embed, ReferenceCfg.Checks.reference_cycle_exact]; rfl

theorem old_failure_preserved : execute 7 (embedProgram ReferenceCfg.Checks.cycle)
    (embedState (ReferenceCfg.initial ReferenceCfg.Checks.cycle)) = none := by
  rw [execute_embed, ReferenceCfg.Checks.reference_cycle_needs_return_fuel]; rfl

end Jihoo.ReferenceCalls.Checks
