import Jihoo.SizedErasureCompiler
import Jihoo.SizedErasureForward

namespace Jihoo.SizedErasure

/-- Zero fuel never silently authorizes an unvisited graph. -/
example : compileTarget #[.integer 7] 0 [] 0 = none := rfl

/-- Removed proof slots cannot be observed as runtime variables. -/
example : compileTarget #[.var 0] 4 [false] 0 = none := rfl

/-- Runtime owner aliases retain their slots independently of whether source
resource typing still authorizes their use. Erasure is not an ownership checker. -/
example : compileTarget #[.var 0] 4 [true] 0 = some (.var 0) := rfl

/-- Two intervening proof binders produce actual index compaction. -/
example : compileTarget #[.var 4] 4 [true, false, true, false, true] 0 =
    some (.var 2) := rfl

/-- Out-of-range graph references and unsupported runtime type nodes fail. -/
example : compileTarget #[.integer 7] 4 [] 99 = none := rfl
example : compileTarget #[.u64] 4 [] 0 = none := rfl

/-- Static erasure checks the true arm even if a particular closing runtime
comparison would be false: its proof variable may not become a runtime value. -/
example : compileTarget #[.ifLt 1 2 3 4, .natural 2, .natural 1, .var 0, .integer 9]
    8 [] 0 = none := rfl

/-- The false arm is also visited even when the literal comparison is true. -/
example : compileTarget #[.ifLt 1 2 3 4, .natural 0, .natural 1, .integer 9, .u64]
    8 [] 0 = none := rfl

/-- Computational variables in the true arm move across the removed proof
binder; the false arm keeps its original layout. -/
example : compileTarget #[.ifLt 1 2 3 4, .natural 0, .natural 1, .var 1, .var 0]
    8 [true] 0 = some (.ifLt (.literal 0) (.literal 1) (.var 0) (.var 0)) := rfl

/-- A cyclic syntactic application consumes fuel and is rejected. -/
example : compileTarget #[.app 1 2, .lam false 3 0, .integer 7, .i64]
    8 [] 0 = none := rfl

/-- Computed compaction of the input environment supplies the complete
correspondence premise; a target run is never part of the compiler contract. -/
theorem compiled_execution_iff
    (success : compileTarget g fuel (compactEnv env).1 root = some term) :
    SizedCoreExecution.Eval g env root s value events t ↔
      ∃ result, value = result.embed ∧ Eval (compactEnv env).2 term s result events t :=
  (compileTarget_correct success).execution_iff (compactEnv_related env)

end Jihoo.SizedErasure
