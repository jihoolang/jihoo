import Jihoo.BoundedMirArguments

/-! The complete actual native MIR exported for the unchanged sized-composition
Core graph (body root 81). This is distinct from the generated Lean MIR graph;
external snapshot comparison checks the trusted export association. -/
namespace Jihoo.NativeCompositionMir
open BoundedMir
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Native ABI order is n, m, i, value; slot zero is the return slot. -/
def entry : Entry := ⟨#[1, 2, 3, 4]⟩

/-- All 36 locals and 22 blocks, including unused branch-local slots. -/
def code : Code := ⟨#[.i64, .u64, .u64, .u64, .i64, .u64, .u64, .ptr, .u64, .bool, .u64, .bool, .ptr, .bool, .ptr, .ptr, .i64, .u64, .u64, .ptr, .u64, .bool, .u64, .bool, .ptr, .bool, .ptr, .ptr, .i64, .unit, .unit, .i64, .unit, .unit, .i64, .unit], #[
  ⟨#[⟨⟨5, false⟩, .bin .mul (.copy ⟨1, false⟩) (.constant (.u64 8))⟩, ⟨⟨6, false⟩, .bin .add (.copy ⟨5, false⟩) (.constant (.u64 8))⟩], .malloc (.copy ⟨6, false⟩) ⟨7, false⟩ 1⟩,
  ⟨#[⟨⟨8, false⟩, .ptrCast (.copy ⟨7, false⟩)⟩, ⟨⟨9, false⟩, .bin .ne (.copy ⟨8, false⟩) (.constant (.u64 0))⟩], .assert (.copy ⟨9, false⟩) 2⟩,
  ⟨#[⟨⟨10, false⟩, .use (.constant (.u64 0))⟩], .goto 3⟩,
  ⟨#[⟨⟨11, false⟩, .bin .lt (.copy ⟨10, false⟩) (.copy ⟨1, false⟩)⟩], .switch (.copy ⟨11, false⟩) [(0, 5)] 4⟩,
  ⟨#[⟨⟨12, false⟩, .offset (.copy ⟨7, false⟩) (.copy ⟨10, false⟩)⟩, ⟨⟨12, true⟩, .use (.copy ⟨4, false⟩)⟩, ⟨⟨10, false⟩, .bin .add (.copy ⟨10, false⟩) (.constant (.u64 1))⟩], .goto 3⟩,
  ⟨#[⟨⟨13, false⟩, .bin .lt (.copy ⟨3, false⟩) (.copy ⟨1, false⟩)⟩], .switch (.copy ⟨13, false⟩) [(0, 7)] 6⟩,
  ⟨#[⟨⟨14, false⟩, .use (.copy ⟨7, false⟩)⟩, ⟨⟨15, false⟩, .offset (.copy ⟨14, false⟩) (.copy ⟨3, false⟩)⟩, ⟨⟨16, false⟩, .use (.copy ⟨15, true⟩)⟩, ⟨⟨17, false⟩, .bin .mul (.copy ⟨2, false⟩) (.constant (.u64 8))⟩, ⟨⟨18, false⟩, .bin .add (.copy ⟨17, false⟩) (.constant (.u64 8))⟩], .malloc (.copy ⟨18, false⟩) ⟨19, false⟩ 9⟩,
  ⟨#[], .free (.copy ⟨7, false⟩) ⟨35, false⟩ 21⟩,
  ⟨#[⟨⟨0, false⟩, .use (.copy ⟨34, false⟩)⟩], .ret⟩,
  ⟨#[⟨⟨20, false⟩, .ptrCast (.copy ⟨19, false⟩)⟩, ⟨⟨21, false⟩, .bin .ne (.copy ⟨20, false⟩) (.constant (.u64 0))⟩], .assert (.copy ⟨21, false⟩) 10⟩,
  ⟨#[⟨⟨22, false⟩, .use (.constant (.u64 0))⟩], .goto 11⟩,
  ⟨#[⟨⟨23, false⟩, .bin .lt (.copy ⟨22, false⟩) (.copy ⟨2, false⟩)⟩], .switch (.copy ⟨23, false⟩) [(0, 13)] 12⟩,
  ⟨#[⟨⟨24, false⟩, .offset (.copy ⟨19, false⟩) (.copy ⟨22, false⟩)⟩, ⟨⟨24, true⟩, .use (.copy ⟨16, false⟩)⟩, ⟨⟨22, false⟩, .bin .add (.copy ⟨22, false⟩) (.constant (.u64 1))⟩], .goto 11⟩,
  ⟨#[⟨⟨25, false⟩, .bin .lt (.constant (.u64 0)) (.copy ⟨2, false⟩)⟩], .switch (.copy ⟨25, false⟩) [(0, 15)] 14⟩,
  ⟨#[⟨⟨26, false⟩, .use (.copy ⟨19, false⟩)⟩, ⟨⟨27, false⟩, .offset (.copy ⟨26, false⟩) (.constant (.u64 0))⟩, ⟨⟨28, false⟩, .use (.copy ⟨27, true⟩)⟩], .free (.copy ⟨7, false⟩) ⟨29, false⟩ 17⟩,
  ⟨#[], .free (.copy ⟨7, false⟩) ⟨32, false⟩ 19⟩,
  ⟨#[⟨⟨34, false⟩, .use (.copy ⟨31, false⟩)⟩], .goto 8⟩,
  ⟨#[], .free (.copy ⟨19, false⟩) ⟨30, false⟩ 18⟩,
  ⟨#[⟨⟨31, false⟩, .use (.copy ⟨28, false⟩)⟩], .goto 16⟩,
  ⟨#[], .free (.copy ⟨19, false⟩) ⟨33, false⟩ 20⟩,
  ⟨#[⟨⟨31, false⟩, .use (.copy ⟨4, false⟩)⟩], .goto 16⟩,
  ⟨#[⟨⟨34, false⟩, .use (.constant (.i64 99))⟩], .goto 8⟩]⟩

theorem code_valid : valid code = true := by decide +kernel

end Jihoo.NativeCompositionMir
