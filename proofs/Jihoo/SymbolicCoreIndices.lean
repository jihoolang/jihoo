import Jihoo.SymbolicCoreTyping

/-! Static U64 derivations reuse the existing pure Raw typing and substitution
calculus. Closing never invents an index evaluation or an Lt witness. -/
namespace Jihoo.SymbolicCoreTyping
open ScopedLend SymbolicCoreContext
open DependentBufferIndices (Expr Represents Available)
variable {a b : Expr}

/-- Owner/dead slots stay unavailable; the common pure projection retains
natural, scalar and erased-bound positions rather than compacting them. -/
theorem Index.raw_typed (typed : Index g ctx root e) :
    CoreBridge.Raw.Beta.HasType (SymbolicCoreContext.rawContext ctx) e.encode .u64 :=
  typed.represents.raw_typed typed.available (fun _ present => rawTypes present)

/-- The syntactic argument is substituted into the dependent result using the
same capture-avoiding substitution as the pure Core beta theorem. -/
theorem index_beta_preservation
    (body : CoreBridge.Raw.Beta.HasType (Γ.extend .u64) b.encode .u64)
    (argument : CoreBridge.Raw.Beta.HasType Γ a.encode .u64) :
    CoreBridge.Raw.Beta.HasType Γ (b.subst (Expr.single a)).encode .u64 :=
  Expr.raw_beta_typing body argument

theorem Index.instantiate (typed : Index g ctx root e)
    (value : e.eval env = some n) : DependentBufferIndices.Eval g env root n :=
  ⟨e, typed.represents, value⟩

theorem BufferType.instantiate (typed : BufferType g ctx root e)
    (value : e.eval env = some n) : DependentBufferIndices.BufferLength g env root n := by
  obtain ⟨indexRoot, shape, index⟩ := typed
  exact ⟨indexRoot, shape, index.instantiate value⟩

theorem RefType.instantiate (typed : RefType g ctx root e)
    (value : e.eval env = some n) : DependentBufferIndices.RefLength g env root n := by
  obtain ⟨bufferRoot, shape, buffer⟩ := typed
  exact ⟨bufferRoot, shape, buffer.instantiate value⟩

end Jihoo.SymbolicCoreTyping
