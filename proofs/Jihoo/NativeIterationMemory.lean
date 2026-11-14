import Jihoo.NativeOwnedLoopSyntax
import Jihoo.NativeKernelEnvironment

/-! An executable inverse of Core.effectful for repeated function expressions.
The check follows its exact erased edges, including Give and Loop. Three raw
leading lambdas are handled separately and may contain memory operations. -/
namespace Jihoo.NativeKernel.Environment

/-- Only these children are skipped by Core.effectful's special cases. -/
def iterationEffectEdge : Op → Nat → Bool
  | .loop, 1 | .give _, 0 | .give true, 2 => false
  | _, _ => true

mutual
  def iterationMemoryFree (env : Environment) : Term → Bool
    | .var _ => true
    | .node op args =>
        match op with
        | .alloc | .load | .store | .free | .drop _ | .caseOf _ _ => false
        | .absurd | .back _ => true
        | .con family _ _ | .elim family _ =>
            match env.families[family]? with
            | none => false
            | some entry => !entry.boxed && iterationMemoryFreeArgs env op 0 args
        | _ => iterationMemoryFreeArgs env op 0 args
    termination_by term => sizeOf term

  def iterationMemoryFreeArgs (env : Environment) (op : Op) (offset : Nat) : List Term → Bool
    | [] => true
    | arg :: rest =>
        (!iterationEffectEdge op offset || iterationMemoryFree env arg) &&
          iterationMemoryFreeArgs env op (offset + 1) rest
    termination_by args => sizeOf args
end

end Jihoo.NativeKernel.Environment
