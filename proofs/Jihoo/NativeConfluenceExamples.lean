import Jihoo.NativeConfluence

/-! Parametric critical-overlap regressions. These cover root/context forks,
including inverse borrow projections, rather than relying on finite reductions
as an assumption of the confluence theorem. -/
namespace Jihoo.NativeKernel.Conversion.Examples

 theorem beta_context_fork (hb : Par body body') (ha : Par a a') :
    Par (.app (.lam e A body) a) (body'.subst (single a')) ∧
    Par (.app (.lam e A body) a) (.app (.lam e A body') a') ∧
    Par (.app (.lam e A body') a') (body'.subst (single a')) := by
  refine ⟨.beta hb ha, ?_, .beta (.refl _) (.refl _)⟩
  exact .node .app (.cons (.node (.lam e) (.cons (.refl A) (.cons hb .nil))) (.cons ha .nil))

 theorem read_context_fork (hs : ListRel Par xs ys) (selected : ys[k]? = some v) :
    Par (.index (.elements count xs) (.natural k) p) v ∧
    Par (.index (.elements count xs) (.natural k) p)
      (.index (.elements count ys) (.natural k) p) ∧
    Par (.index (.elements count ys) (.natural k) p) v := by
  have hsId : ∀ zs : List Term, ListRel Par zs zs := by
    intro zs
    induction zs with
    | nil => exact .nil
    | cons y ys ih => exact .cons (.refl y) ih
  refine ⟨.read count k p hs selected, ?_, .read count k p (hsId ys) selected⟩
  exact .node .index (.cons (.node (.elements count) hs)
    (.cons (.refl _) (.cons (.refl _) .nil)))

 theorem deref_borrow_overlap (h : Par a b) :
    Par (.node .deref [.node .borrow [.node .deref [a]]]) (.node .deref [a]) ∧
    Par (.node .deref [.node .borrow [.node .deref [a]]]) (.node .deref [b]) ∧
    Par (.node .deref [a]) (.node .deref [b]) :=
  ⟨.derefBorrow (.refl _), .node .deref (.cons (.borrowDeref h) .nil),
    .node .deref (.cons h .nil)⟩

 theorem borrow_deref_overlap (h : Par a b) :
    Par (.node .borrow [.node .deref [.node .borrow [a]]]) (.node .borrow [a]) ∧
    Par (.node .borrow [.node .deref [.node .borrow [a]]]) (.node .borrow [b]) ∧
    Par (.node .borrow [a]) (.node .borrow [b]) :=
  ⟨.borrowDeref (.refl _), .node .borrow (.cons (.derefBorrow h) .nil),
    .node .borrow (.cons h .nil)⟩

 theorem witness_context_fork (h : Par a b) :
    Par (.witness (.pack p a q)) b ∧
    Par (.witness (.pack p a q)) (.witness (.pack p b q)) ∧
    Par (.witness (.pack p b q)) b :=
  ⟨.witnessPack h,
    .node .witness (.cons (.node .pack (.cons (.refl _) (.cons h (.cons (.refl _) .nil)))) .nil),
    .witnessPack (.refl b)⟩

 theorem proof_context_fork (h : Par p q) :
    Par (.proof (.pack f a p)) q ∧
    Par (.proof (.pack f a p)) (.proof (.pack f a q)) ∧
    Par (.proof (.pack f a q)) q :=
  ⟨.proofPack h,
    .node .proof (.cons (.node .pack (.cons (.refl _) (.cons (.refl _) (.cons h .nil)))) .nil),
    .proofPack (.refl q)⟩

 theorem beta_and_inverse_borrow_join (e : Bool) (A body a : Term) :
    Join (.app (.lam e A body) a) (.node .deref [.node .borrow [body.subst (single a)]]) :=
  (Conv.trans (Conv.beta e A body a) (.symm (.derefBorrow _))).church_rosser

 theorem all_operators_preserve_join (op : Op) (h : ListRel Conv xs ys) :
    Join (.node op xs) (.node op ys) := (Conv.node op h).church_rosser

 theorem erased_flags_separate : ¬ Conv (.pi false A B) (.pi true A' B') := by
  intro h
  have flags := h.pi_injective.1
  cases flags

 theorem universe_levels_separate (different : n ≠ m) : ¬ Conv (.univ n) (.univ m) :=
  fun h => different h.universe_injective

 theorem concrete_array_lengths_separate (different : n ≠ m) :
    ¬ Conv (.array (.natural n)) (.array (.natural m)) :=
  fun h => different h.array_injective.natural_injective

 theorem equality_reflection_numerals (h : Conv (.eq a a) (.eq (.natural n) (.natural m))) : n = m := by
  obtain ⟨hn, hm⟩ := h.eq_injective
  exact (Conv.trans (.symm hn) hm).natural_injective

 theorem malformed_pi_still_injective
    (h : Conv (.node (.pi e) [A,B,C]) (.node (.pi e') [A',B',C'])) :
    e = e' ∧ ListRel Conv [A,B,C] [A',B',C'] := by
  obtain ⟨he, hs⟩ := h.rigid_node_injective rfl rfl
  exact ⟨Op.pi.inj he, hs⟩

end Jihoo.NativeKernel.Conversion.Examples
