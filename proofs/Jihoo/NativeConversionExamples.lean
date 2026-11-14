import Jihoo.NativeNormalization

/-! Kernel-checked computation of the full-syntax normalizer, including every
projection rule, open capture avoidance and traversal under runtime operators. -/
namespace Jihoo.NativeKernel.ConversionExamples

open Conversion

private def lit (n : Nat) : Term := .node (.natural n) []
private def u64 : Term := .node .u64 []
private def ident : Term := .node (.lam false) [u64, .var 0]

macro "native_conversion_example" : tactic =>
  `(tactic| (simp [normalize, children, contract, equal, lit, u64, ident,
    substitutionSafe, treeSize, treeDepth, Term.subst, substArgs, single,
    liftSub, liftSubOne, Term.rename, renameArgs, liftRenaming,
    Indexed.liftRenaming, Op.binders]))

theorem beta : normalize 8 (.node .app [ident, lit 7]) = lit 7 := by
  native_conversion_example

theorem nested_capture : normalize 8
    (.node .app [.node (.lam false) [u64, .node (.lam false) [u64, .var 1]], .var 0]) =
    .node (.lam false) [u64, .var 1] := by native_conversion_example

theorem conditional_binder_capture : normalize 8
    (.node .ifEq [.var 1, .var 1,
      .node .app [.node (.lam false) [u64,
        .node (.lam false) [u64, .node .refl [.var 1]]], .var 0], lit 7]) =
    .node .ifEq [.var 1, .var 1, .node (.lam false) [u64, .node .refl [.var 1]], lit 7] := by
  native_conversion_example

theorem witness_pack : normalize 4
    (.node .witness [.node .pack [.var 2, lit 7, .var 1]]) = lit 7 := by
  native_conversion_example

theorem proof_pack : normalize 4
    (.node .proof [.node .pack [.var 2, lit 7, .var 1]]) = .var 1 := by
  native_conversion_example

theorem deref_borrow : normalize 4 (.node .deref [.node .borrow [.var 0]]) = .var 0 := by
  native_conversion_example

theorem borrow_deref : normalize 4 (.node .borrow [.node .deref [.var 0]]) = .var 0 := by
  native_conversion_example

theorem buffer_index_beta : normalize 8 (.node .buffer [.node .app [ident, lit 7]]) =
    .node .buffer [lit 7] := by native_conversion_example

theorem bounded_add : normalize 4 (.node .uadd [lit (2^64-2), lit 1]) = lit (2^64-1) := by
  native_conversion_example

theorem overflow_neutral : normalize 4 (.node .uadd [lit (2^64-1), lit 1]) =
    .node .uadd [lit (2^64-1), lit 1] := by native_conversion_example

theorem underflow_neutral : normalize 4 (.node .usub [lit 0, lit 1, .var 0]) =
    .node .usub [lit 0, lit 1, .var 0] := by native_conversion_example

theorem array_read : normalize 4
    (.node .index [.node (.elements 2) [lit 7, lit 9], lit 1, .var 0]) = lit 9 := by
  native_conversion_example

theorem malformed_arity_neutral : normalize 4 (.node .uadd [lit 1]) = .node .uadd [lit 1] := by
  native_conversion_example

theorem false_equality_rejected : equal 8 (lit 0) (lit 1) = false := by
  native_conversion_example

theorem beta_forward : Reduction.Steps (.node .app [ident, lit 7]) (lit 7) := by
  simpa only [beta] using normalize_steps 8 (.node .app [ident, lit 7])

end Jihoo.NativeKernel.ConversionExamples
