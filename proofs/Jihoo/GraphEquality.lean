import Jihoo.CoreBridgeTyping

/-! Executable structural equality, with a kernel-checked correctness proof,
including the nested list in `Raw.elements`. -/
namespace Jihoo.GraphCertificates
open CoreBridge

mutual
  def rawEqual (a b : Raw) : Bool :=
    match a, b with
    | .var a0, .var b0 => (a0 == b0)
    | .natural a0, .natural b0 => (a0 == b0)
    | .integer a0, .integer b0 => (a0 == b0)
    | .u64 , .u64  => true
    | .i64 , .i64  => true
    | .array a0, .array b0 => rawEqual a0 b0
    | .lt a0 a1, .lt b0 b1 => rawEqual a0 b0 && rawEqual a1 b1
    | .eq a0 a1, .eq b0 b1 => rawEqual a0 b0 && rawEqual a1 b1
    | .pi a0 a1 a2, .pi b0 b1 b2 => (a0 == b0) && rawEqual a1 b1 && rawEqual a2 b2
    | .lam a0 a1 a2, .lam b0 b1 b2 => (a0 == b0) && rawEqual a1 b1 && rawEqual a2 b2
    | .app a0 a1, .app b0 b1 => rawEqual a0 b0 && rawEqual a1 b1
    | .elements a0, .elements b0 => rawListEqual a0 b0
    | .index a0 a1 a2, .index b0 b1 b2 => rawEqual a0 b0 && rawEqual a1 b1 && rawEqual a2 b2
    | .refl a0, .refl b0 => rawEqual a0 b0
    | .zeroLe a0, .zeroLe b0 => rawEqual a0 b0
    | .decide a0 a1, .decide b0 b1 => rawEqual a0 b0 && rawEqual a1 b1
    | .uadd a0 a1, .uadd b0 b1 => rawEqual a0 b0 && rawEqual a1 b1
    | .usub a0 a1 a2, .usub b0 b1 b2 => rawEqual a0 b0 && rawEqual a1 b1 && rawEqual a2 b2
    | _, _ => false
  termination_by sizeOf a
  def rawListEqual (xs ys : List Raw) : Bool :=
    match xs, ys with
    | [], [] => true
    | x :: xs, y :: ys => rawEqual x y && rawListEqual xs ys
    | _, _ => false
  termination_by sizeOf xs
end

theorem rawEqual_iff (a : Raw) : ∀ b : Raw, rawEqual a b = true ↔ a = b := by
  induction a using Raw.rec (motive_2 := fun xs => ∀ ys, rawListEqual xs ys = true ↔ xs = ys) with
  | elements xs ih => intro b; cases b <;> simp_all [rawEqual]
  | nil ys => cases ys <;> simp [rawListEqual]
  | cons x xs ihx ihxs ys => cases ys <;> simp_all [rawListEqual]
  | _ => intro b; cases b <;> simp_all [rawEqual, and_assoc]


end Jihoo.GraphCertificates
