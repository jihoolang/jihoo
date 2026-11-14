import Jihoo.NativeSyntax

/-! Complete native constructor wire schema. Tags follow the source Term enum;
scalar payloads are separate from ordered child references. The source/Lean
schema agreement is regression-tested, not assumed to prove source execution. -/
namespace Jihoo.NativeKernel.NativeSchema

private def boolCode : Bool → Nat | false => 0 | true => 1
private def arithCode : Arith → Nat | .add => 0 | .sub => 1 | .mul => 2
private def signedPayload : Int → List Nat
  | .ofNat n => [0, n]
  | .negSucc n => [1, n + 1]

def tag : Op → Nat
  | .global _ => 1
  | .universe _ => 2
  | .prop => 3
  | .u64 => 4
  | .i64 => 5
  | .array => 6
  | .lt => 7
  | .eq => 8
  | .refl => 9
  | .transport => 10
  | .ind _ _ => 11
  | .con _ _ _ => 12
  | .elim _ _ => 13
  | .arith _ => 14
  | .fold => 15
  | .strict => 16
  | .uadd => 17
  | .ltAdd => 18
  | .ltCancel => 19
  | .ltLe => 20
  | .usub => 21
  | .zeroLe => 22
  | .refine => 23
  | .pack => 24
  | .witness => 25
  | .proof => 26
  | .buffer => 27
  | .alloc => 28
  | .load => 29
  | .store => 30
  | .free => 31
  | .drop _ => 32
  | .ref => 33
  | .lend => 34
  | .back _ => 35
  | .give _ => 36
  | .take => 37
  | .borrow => 38
  | .deref => 39
  | .view _ _ _ => 40
  | .loop => 41
  | .absurd => 42
  | .caseOf _ _ => 43
  | .pi _ => 44
  | .lam _ => 45
  | .app => 46
  | .natural _ => 47
  | .integer _ => 48
  | .elements _ => 49
  | .index => 50
  | .decide => 51
  | .ifLt => 52
  | .ifEq => 53

def payload : Op → List Nat
  | .global id => [id]
  | .universe level => [level]
  | .prop => []
  | .u64 => []
  | .i64 => []
  | .array => []
  | .lt => []
  | .eq => []
  | .refl => []
  | .transport => []
  | .ind family count => [family, count]
  | .con family constructor count => [family, constructor, count]
  | .elim family cases => [family, cases]
  | .arith op => [arithCode op]
  | .fold => []
  | .strict => []
  | .uadd => []
  | .ltAdd => []
  | .ltCancel => []
  | .ltLe => []
  | .usub => []
  | .zeroLe => []
  | .refine => []
  | .pack => []
  | .witness => []
  | .proof => []
  | .buffer => []
  | .alloc => []
  | .load => []
  | .store => []
  | .free => []
  | .drop family => [family]
  | .ref => []
  | .lend => []
  | .back erased => [boolCode erased]
  | .give erased => [boolCode erased]
  | .take => []
  | .borrow => []
  | .deref => []
  | .view recursive family cases => [boolCode recursive, family, cases]
  | .loop => []
  | .absurd => []
  | .caseOf family cases => [family, cases]
  | .pi erased => [boolCode erased]
  | .lam erased => [boolCode erased]
  | .app => []
  | .natural value => [value]
  | .integer value => signedPayload value
  | .elements count => [count]
  | .index => []
  | .decide => []
  | .ifLt => []
  | .ifEq => []

def ofCode : Nat → List Nat → Option Op
  | 1, [id] => some (.global id)
  | 2, [level] => some (.universe level)
  | 3, [] => some (.prop)
  | 4, [] => some (.u64)
  | 5, [] => some (.i64)
  | 6, [] => some (.array)
  | 7, [] => some (.lt)
  | 8, [] => some (.eq)
  | 9, [] => some (.refl)
  | 10, [] => some (.transport)
  | 11, [family, count] => some (.ind family count)
  | 12, [family, constructor, count] => some (.con family constructor count)
  | 13, [family, cases] => some (.elim family cases)
  | 14, [0] => some (.arith .add)
  | 14, [1] => some (.arith .sub)
  | 14, [2] => some (.arith .mul)
  | 15, [] => some (.fold)
  | 16, [] => some (.strict)
  | 17, [] => some (.uadd)
  | 18, [] => some (.ltAdd)
  | 19, [] => some (.ltCancel)
  | 20, [] => some (.ltLe)
  | 21, [] => some (.usub)
  | 22, [] => some (.zeroLe)
  | 23, [] => some (.refine)
  | 24, [] => some (.pack)
  | 25, [] => some (.witness)
  | 26, [] => some (.proof)
  | 27, [] => some (.buffer)
  | 28, [] => some (.alloc)
  | 29, [] => some (.load)
  | 30, [] => some (.store)
  | 31, [] => some (.free)
  | 32, [family] => some (.drop family)
  | 33, [] => some (.ref)
  | 34, [] => some (.lend)
  | 35, [0] => some (.back false)
  | 35, [1] => some (.back true)
  | 36, [0] => some (.give false)
  | 36, [1] => some (.give true)
  | 37, [] => some (.take)
  | 38, [] => some (.borrow)
  | 39, [] => some (.deref)
  | 40, [0, family, cases] => some (.view false family cases)
  | 40, [1, family, cases] => some (.view true family cases)
  | 41, [] => some (.loop)
  | 42, [] => some (.absurd)
  | 43, [family, cases] => some (.caseOf family cases)
  | 44, [0] => some (.pi false)
  | 44, [1] => some (.pi true)
  | 45, [0] => some (.lam false)
  | 45, [1] => some (.lam true)
  | 46, [] => some (.app)
  | 47, [value] => some (.natural value)
  | 48, [0, n] => some (.integer (Int.ofNat n))
  | 48, [1, n + 1] => some (.integer (.negSucc n))
  | 49, [count] => some (.elements count)
  | 50, [] => some (.index)
  | 51, [] => some (.decide)
  | 52, [] => some (.ifLt)
  | 53, [] => some (.ifEq)
  | _, _ => none

@[simp] theorem tag_nonzero (op : Op) : tag op ≠ 0 := by cases op <;> simp [tag]

@[simp] theorem ofCode_payload (op : Op) : ofCode (tag op) (payload op) = some op := by
  cases op
  all_goals first | rfl | skip
  case arith op => cases op <;> rfl
  case back e => cases e <;> rfl
  case give e => cases e <;> rfl
  case view r f n => cases r <;> rfl
  case pi e => cases e <;> rfl
  case lam e => cases e <;> rfl
  case integer n => cases n <;> rfl

/-- Payload bounds of the actual native scalar types. Vector counts are capped
separately by the envelope; administrative Universe 32 may occur in output. -/
def payloadBounded : Op → Bool
  | .global id => decide (id < 2^32)
  | .universe level => decide (level < 33)
  | .natural value => decide (value < 2^64)
  | .integer value => decide (-(2^63 : Int) ≤ value ∧ value < (2^63 : Int))
  | .ind f _ | .elim f _ | .drop f => decide (f < 2^32)
  | .con f k _ => decide (f < 2^32 ∧ k < 2^32)
  | .caseOf f _ => decide (f < 2^32)
  | .view _ f _ => decide (f < 2^32)
  | _ => true

/-- Representative operations for mechanically comparing the entire schema to
native source. Counts one and three exercise every vector-bearing constructor. -/
def representatives (count : Nat) : List Op := [
  .global 0,
  .universe 0,
  .prop,
  .u64,
  .i64,
  .array,
  .lt,
  .eq,
  .refl,
  .transport,
  .ind 0 count,
  .con 0 0 count,
  .elim 0 count,
  .arith .add,
  .fold,
  .strict,
  .uadd,
  .ltAdd,
  .ltCancel,
  .ltLe,
  .usub,
  .zeroLe,
  .refine,
  .pack,
  .witness,
  .proof,
  .buffer,
  .alloc,
  .load,
  .store,
  .free,
  .drop 0,
  .ref,
  .lend,
  .back false,
  .give false,
  .take,
  .borrow,
  .deref,
  .view false 0 count,
  .loop,
  .absurd,
  .caseOf 0 count,
  .pi false,
  .lam false,
  .app,
  .natural 0,
  .integer 0,
  .elements count,
  .index,
  .decide,
  .ifLt,
  .ifEq]

end Jihoo.NativeKernel.NativeSchema
