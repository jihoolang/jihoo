import Jihoo.NativeLoopTelescopes

/-! Conversion of iteration telescopes when their count or dependent motive
changes by a computation. Every inserted motive retains its binding depth. -/
namespace Jihoo.NativeKernel.Conversion

private theorem binary (op : Op) {a a' b b' : Term} (ha : Conv a a') (hb : Conv b b') :
    Conv (.node op [a,b]) (.node op [a',b']) := .node op (.cons ha (.cons hb .nil))

theorem foldBodyType_congr {n n' : Term} (h : Conv n n') : Conv (foldBodyType n) (foldBodyType n') := by
  unfold foldBodyType
  exact binary (.pi false) (.refl _)
    (binary (.pi true) (binary .lt (.refl _) (h.renaming Nat.succ)) (.refl _))

theorem loopBodyType_count_congr {n n' : Term} (m : Term) (proof : Bool) (h : Conv n n') :
    Conv (loopBodyType n m proof) (loopBodyType n' m proof) := by
  unfold loopBodyType
  exact binary (.pi false) (.refl _)
    (binary (.pi true) (binary .lt (.refl _) (h.renaming Nat.succ)) (.refl _))

theorem loopBodyType_motive_congr (n : Term) {m m' : Term} (proof : Bool) (h : Conv m m') :
    Conv (loopBodyType n m proof) (loopBodyType n m' proof) := by
  unfold loopBodyType
  exact binary (.pi false) (.refl _) (binary (.pi true) (.refl _)
    (binary (.pi proof) (binary .app (h.renaming (fun x => x+2)) (.refl _))
      (binary .app (h.renaming (fun x => x+3)) (.refl _))))

end Jihoo.NativeKernel.Conversion
