import Jihoo.TypingCertificates

/-! Executable inference and formation for a universe-free, ghost-mode fragment
of Raw. Inputs are raw terms, never derivation certificates or proofs. Equality
checks are structural; no normalization or conversion search is attempted.
Acceptance soundness is proved separately, against Raw.Beta judgments. This is
not a refinement theorem for the native Core.infer implementation. -/
namespace Jihoo.KernelChecker

open CoreBridge
open CoreBridge.Raw
open GraphCertificates.Typing (context rawDecidableEq substitutionSafe)

mutual
  /-- Infer a type with a depth budget. Context annotations use the existing
  newest-first, pre-binder convention of GraphCertificates.Typing.context.
  Exhaustion and all unsupported constructors reject. The budget bounds checker
  recursion, not the cost of structural equality, lookup, or substitution. -/
  def infer : Nat → List Raw → Raw → Option Raw
    | 0, _, _ => none
    | fuel + 1, ctx, term =>
      match term with
      | .var x => context ctx x
      | .natural n => if n < wordBound then some .u64 else none
      | .integer n =>
          if -signedBound ≤ n ∧ n < signedBound then some .i64 else none
      | .uadd a b =>
          if infer fuel ctx a = some .u64 ∧ infer fuel ctx b = some .u64
          then some .u64 else none
      | .refl a =>
          if infer fuel ctx a = some .u64 then some (.eq a a) else none
      | .lam e A body =>
          if e = A.proposition ∧ isType fuel ctx A = true then
            match infer fuel (A :: ctx) body with
            | some B => some (.pi e A B)
            | none => none
          else none
      | .app f a =>
          match infer fuel ctx f with
          | some (.pi _ A B) =>
              if infer fuel ctx a = some A ∧ substitutionSafe B a = true
              then some (B.subst (single a)) else none
          | _ => none
      | _ => none

  /-- Check formation separately because this fragment has no universe term.
  Pi formation checks its codomain under the domain binder. Eq relates U64
  expressions, matching the existing declarative judgment. -/
  def isType : Nat → List Raw → Raw → Bool
    | 0, _, _ => false
    | fuel + 1, ctx, ty =>
      match ty with
      | .u64 | .i64 => true
      | .eq a b =>
          decide (infer fuel ctx a = some .u64 ∧ infer fuel ctx b = some .u64)
      | .pi e A B =>
          decide (e = A.proposition) && isType fuel ctx A && isType fuel (A :: ctx) B
      | _ => false
end

@[simp] theorem infer_zero (ctx : List Raw) (term : Raw) :
    infer 0 ctx term = none := rfl

@[simp] theorem isType_zero (ctx : List Raw) (ty : Raw) :
    isType 0 ctx ty = false := rfl

end Jihoo.KernelChecker
