import Jihoo.KernelConversion

/-! Executable inference, checking and formation for the universe-free,
ghost-mode Raw calculus. Inputs are raw terms, never derivation certificates.
Conversion uses the independently verified bounded normalizer. Acceptance
soundness is proved against Raw.Beta judgments in KernelCheckerSoundness. -/
namespace Jihoo.KernelChecker

open CoreBridge
open CoreBridge.Raw
open GraphCertificates.Typing (context rawDecidableEq substitutionSafe)

/-- Compare an inferred type with an expected type by verified conversion.
A failed inference always rejects, even if the expected type is inhabited. -/
def checksType (fuel : Nat) (inferred : Option Raw) (expected : Raw) : Bool :=
  match inferred with
  | none => false
  | some actual => KernelConversion.equal fuel actual expected

mutual
  /-- Infer with a recursion-depth budget. Context annotations use the existing
  newest-first, pre-binder convention. Fuel bounds checker recursion; it is not
  a total bound on lookup, equality, list traversal or substitution work. -/
  def infer : Nat → List Raw → Raw → Option Raw
    | 0, _, _ => none
    | fuel + 1, ctx, term =>
      match term with
      | .var x => context ctx x
      | .natural n => if n < wordBound then some .u64 else none
      | .integer n =>
          if -signedBound ≤ n ∧ n < signedBound then some .i64 else none
      | .uadd a b =>
          if checksType fuel (infer fuel ctx a) .u64 && checksType fuel (infer fuel ctx b) .u64
          then some .u64 else none
      | .usub a b p =>
          if checksType fuel (infer fuel ctx a) .u64 &&
              checksType fuel (infer fuel ctx b) .u64 &&
              checksType fuel (infer fuel ctx p) (.lt b (.uadd a (.natural 1)))
          then some .u64 else none
      | .elements xs =>
          if xs.length < wordBound ∧
              xs.all (fun x => checksType fuel (infer fuel ctx x) .i64) = true
          then some (.array (.natural xs.length)) else none
      | .decide a b =>
          match a, b with
          | .natural a, .natural b =>
              if a < wordBound ∧ b < wordBound ∧ a < b
              then some (.lt (.natural a) (.natural b)) else none
          | _, _ => none
      | .refl a =>
          if checksType fuel (infer fuel ctx a) .u64
          then some (.eq a a) else none
      | .zeroLe a =>
          if checksType fuel (infer fuel ctx a) .u64
          then some (.lt (.natural 0) (.uadd a (.natural 1))) else none
      | .index a i p =>
          match infer fuel ctx a with
          | some T =>
              match KernelConversion.normalize fuel T with
              | .array n =>
                  if checksType fuel (infer fuel ctx i) .u64 &&
                      checksType fuel (infer fuel ctx p) (.lt i n)
                  then some .i64 else none
              | _ => none
          | none => none
      | .lam e A body =>
          if e = A.proposition ∧ isType fuel ctx A = true then
            match infer fuel (A :: ctx) body with
            | some B => some (.pi e A B)
            | none => none
          else none
      | .app f a =>
          match infer fuel ctx f with
          | some T =>
              match KernelConversion.normalize fuel T with
              | .pi _ A B =>
                  if checksType fuel (infer fuel ctx a) A && substitutionSafe B a
                  then some (B.subst (single a)) else none
              | _ => none
          | none => none
      | _ => none

  /-- Formation has its own entry point because Raw contains no universe term.
  Arrays, propositions and Pi codomains check their term indices recursively. -/
  def isType : Nat → List Raw → Raw → Bool
    | 0, _, _ => false
    | fuel + 1, ctx, ty =>
      match ty with
      | .u64 | .i64 => true
      | .array n => checksType fuel (infer fuel ctx n) .u64
      | .eq a b | .lt a b =>
          checksType fuel (infer fuel ctx a) .u64 && checksType fuel (infer fuel ctx b) .u64
      | .pi e A B =>
          decide (e = A.proposition) && isType fuel ctx A && isType fuel (A :: ctx) B
      | _ => false
end

/-- Check both the requested type's formation and the term's inferred type.
The caller supplies no typing derivation or conversion certificate. -/
def check (fuel : Nat) (ctx : List Raw) (term expected : Raw) : Bool :=
  isType fuel ctx expected && checksType fuel (infer fuel ctx term) expected

@[simp] theorem infer_zero (ctx : List Raw) (term : Raw) :
    infer 0 ctx term = none := rfl

@[simp] theorem isType_zero (ctx : List Raw) (ty : Raw) :
    isType 0 ctx ty = false := rfl

@[simp] theorem check_zero (ctx : List Raw) (term ty : Raw) :
    check 0 ctx term ty = false := rfl

end Jihoo.KernelChecker
