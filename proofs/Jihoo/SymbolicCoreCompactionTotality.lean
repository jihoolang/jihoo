import Jihoo.SymbolicCoreCompaction
import Jihoo.SymbolicCoreCompactionCompiler

/-! Symbolic typing discharges structural compiler success. The witness target
and fuel threshold are independent of evaluation, heap safety, and lowering. -/
namespace Jihoo.SymbolicCoreCompaction
open SymbolicCoreContext SymbolicCoreTyping SizedErasure

/-- Every constructor-driven symbolic Buffer derivation compacts under its
lexical mask, at all sufficiently large fuel values, to one fixed target. -/
theorem typing_compiles (typing : Typing g ctx sizes root kind)
    (supported : MaskSupports ctx mask) :
    ∃ term bound, ∀ fuel, bound ≤ fuel → compileTarget g fuel mask root = some term := by
  obtain ⟨term, erased⟩ := typing_erases typing supported
  obtain ⟨bound, complete⟩ := erased.compileTarget_complete
  exact ⟨term, bound, complete⟩

/-- The original runtime compaction supplies the mask. Existing closing and
agreement suffice; no extra mask certificate or successful execution is assumed. -/
theorem typing_compiles_closed (typing : Typing g ctx sizes root kind)
    (closing : Closes ctx closed) (agrees : SizedBufferContext.Agrees closed owners env) :
    ∃ term bound, ∀ fuel, bound ≤ fuel →
      compileTarget g fuel (compactEnv env).1 root = some term :=
  typing_compiles typing (MaskSupports.of_closing_agrees closing agrees)

/-- Convenient existential form for callers that choose the compactor fuel. -/
theorem typing_compile_exists (typing : Typing g ctx sizes root kind)
    (closing : Closes ctx closed) (agrees : SizedBufferContext.Agrees closed owners env) :
    ∃ fuel term, compileTarget g fuel (compactEnv env).1 root = some term := by
  obtain ⟨term, bound, complete⟩ := typing_compiles_closed typing closing agrees
  exact ⟨bound, term, complete bound (Nat.le_refl bound)⟩

end Jihoo.SymbolicCoreCompaction
