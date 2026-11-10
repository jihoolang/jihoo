/-! Shared allocator observations. Initialization/read/write operations are
intentionally not identified with these allocation/free lifecycle events. -/
namespace Jihoo.HeapLifecycle
inductive Event where
  | alloc (object bytes : Nat)
  | free (object : Nat)
  deriving DecidableEq, Repr
end Jihoo.HeapLifecycle
