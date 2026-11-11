import Jihoo.BoundedMirArguments

/-! One retained actual dynamic Buffer MIR CFG, not a program specialized to
individual inputs. The native exporter compares every local, statement and edge.
The existing bounded scalar model represents nonnegative I64 values only. -/
namespace Jihoo.DynamicMir
open BoundedMir

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Exact U64/U64/I64 entry ABI metadata. Slot zero remains the return slot. -/
def entry : Entry := ⟨#[1, 2, 3]⟩

/-- Exact 19-local, 11-block compiler output for core_dependent_index.jhc. -/
def code : Code := ⟨#[.i64, .u64, .u64, .i64, .u64, .u64, .ptr, .u64, .bool, .u64, .bool, .ptr, .bool, .ptr, .ptr, .i64, .unit, .i64, .unit], #[
  ⟨#[⟨⟨4, false⟩, .bin .mul (.copy ⟨1, false⟩) (.constant (.u64 8))⟩, ⟨⟨5, false⟩, .bin .add (.copy ⟨4, false⟩) (.constant (.u64 8))⟩], .malloc (.copy ⟨5, false⟩) ⟨6, false⟩ 1⟩,
  ⟨#[⟨⟨7, false⟩, .ptrCast (.copy ⟨6, false⟩)⟩, ⟨⟨8, false⟩, .bin .ne (.copy ⟨7, false⟩) (.constant (.u64 0))⟩], .assert (.copy ⟨8, false⟩) 2⟩,
  ⟨#[⟨⟨9, false⟩, .use (.constant (.u64 0))⟩], .goto 3⟩,
  ⟨#[⟨⟨10, false⟩, .bin .lt (.copy ⟨9, false⟩) (.copy ⟨1, false⟩)⟩], .switch (.copy ⟨10, false⟩) [(0, 5)] 4⟩,
  ⟨#[⟨⟨11, false⟩, .offset (.copy ⟨6, false⟩) (.copy ⟨9, false⟩)⟩, ⟨⟨11, true⟩, .use (.copy ⟨3, false⟩)⟩, ⟨⟨9, false⟩, .bin .add (.copy ⟨9, false⟩) (.constant (.u64 1))⟩], .goto 3⟩,
  ⟨#[⟨⟨12, false⟩, .bin .lt (.copy ⟨2, false⟩) (.copy ⟨1, false⟩)⟩], .switch (.copy ⟨12, false⟩) [(0, 7)] 6⟩,
  ⟨#[⟨⟨13, false⟩, .use (.copy ⟨6, false⟩)⟩, ⟨⟨14, false⟩, .offset (.copy ⟨13, false⟩) (.copy ⟨2, false⟩)⟩, ⟨⟨15, false⟩, .use (.copy ⟨14, true⟩)⟩], .free (.copy ⟨6, false⟩) ⟨16, false⟩ 9⟩,
  ⟨#[], .free (.copy ⟨6, false⟩) ⟨18, false⟩ 10⟩,
  ⟨#[⟨⟨0, false⟩, .use (.copy ⟨17, false⟩)⟩], .ret⟩,
  ⟨#[⟨⟨17, false⟩, .use (.copy ⟨15, false⟩)⟩], .goto 8⟩,
  ⟨#[⟨⟨17, false⟩, .use (.constant (.i64 99))⟩], .goto 8⟩]⟩

theorem code_valid : valid code = true := by decide +kernel

end Jihoo.DynamicMir
