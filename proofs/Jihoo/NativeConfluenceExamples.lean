import Jihoo.NativeConfluence
import Jihoo.NativeNormalization

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

theorem ifLt_true_context_fork (bound : m < n) (h : Par yes yes') :
    Par (.ifLt (.natural m) (.natural n) yes no)
      (yes'.subst (single (.decide (.natural m) (.natural n)))) ∧
    Par (.ifLt (.natural m) (.natural n) yes no) (.ifLt (.natural m) (.natural n) yes' no) ∧
    Par (.ifLt (.natural m) (.natural n) yes' no)
      (yes'.subst (single (.decide (.natural m) (.natural n)))) := by
  refine ⟨.ifLtTrue m n no bound h, ?_, .ifLtTrue m n no bound (.refl _)⟩
  exact .node .ifLt (.cons (.refl _) (.cons (.refl _) (.cons h (.cons (.refl _) .nil))))

theorem ifLt_false_context_fork (bound : n ≤ m) (h : Par no no') :
    Par (.ifLt (.natural m) (.natural n) yes no) no' ∧
    Par (.ifLt (.natural m) (.natural n) yes no) (.ifLt (.natural m) (.natural n) yes no') ∧
    Par (.ifLt (.natural m) (.natural n) yes no') no' := by
  refine ⟨.ifLtFalse m n yes bound h, ?_, .ifLtFalse m n yes bound (.refl _)⟩
  exact .node .ifLt (.cons (.refl _) (.cons (.refl _) (.cons (.refl _) (.cons h .nil))))

theorem ifEq_true_context_fork (h : Par yes yes') :
    Par (.ifEq (.natural n) (.natural n) yes no) (yes'.subst (single (.refl (.natural n)))) ∧
    Par (.ifEq (.natural n) (.natural n) yes no) (.ifEq (.natural n) (.natural n) yes' no) ∧
    Par (.ifEq (.natural n) (.natural n) yes' no) (yes'.subst (single (.refl (.natural n)))) := by
  refine ⟨.ifEqTrue n no h, ?_, .ifEqTrue n no (.refl _)⟩
  exact .node .ifEq (.cons (.refl _) (.cons (.refl _) (.cons h (.cons (.refl _) .nil))))

theorem ifEq_false_context_fork (apart : m ≠ n) (h : Par no no') :
    Par (.ifEq (.natural m) (.natural n) yes no) no' ∧
    Par (.ifEq (.natural m) (.natural n) yes no) (.ifEq (.natural m) (.natural n) yes no') ∧
    Par (.ifEq (.natural m) (.natural n) yes no') no' := by
  refine ⟨.ifEqFalse m n yes apart h, ?_, .ifEqFalse m n yes apart (.refl _)⟩
  exact .node .ifEq (.cons (.refl _) (.cons (.refl _) (.cons (.refl _) (.cons h .nil))))

theorem transport_context_fork (h : Par p q) :
    Par (.transport f (.refl a) p) q ∧
    Par (.transport f (.refl a) p) (.transport f (.refl a) q) ∧
    Par (.transport f (.refl a) q) q := by
  refine ⟨.transportRefl f a h, ?_, .transportRefl f a (.refl _)⟩
  exact .node .transport (.cons (.refl _) (.cons (.refl _) (.cons h .nil)))

private def branchCapture : Term :=
  .lam false .u64
    (.ifLt (.natural 0) (.natural 1)
      (.lam false .u64 (.refl (.var 2))) (.lam false .u64 (.refl (.var 1))))

private def captureResult : Term := .lam false .u64 (.lam false .u64 (.refl (.var 1)))

/-- Removing conditional evidence beneath a value lambda must retain the outer
value variable and must not capture it as the returned function's argument. -/
theorem branch_lambda_capture : normalize 12 branchCapture = captureResult := by cbv

theorem branch_lambda_capture_forward : Reduction.Steps branchCapture captureResult := by
  simpa only [branch_lambda_capture] using normalize_steps 12 branchCapture

theorem equality_inserts_reflexivity :
    normalize 8 (.ifEq (.natural 7) (.natural 7) (.var 0) (.refl (.natural 7))) =
      .refl (.natural 7) := by cbv

theorem inequality_inserts_decision :
    normalize 8 (.ifLt (.natural 0) (.natural 1) (.var 0) (.decide (.natural 0) (.natural 1))) =
      .decide (.natural 0) (.natural 1) := by cbv

theorem false_equality_preserves_free_variable :
    normalize 8 (.ifEq (.natural 0) (.natural 1) (.var 1) (.var 0)) = .var 0 := by cbv

theorem false_inequality_preserves_free_variable :
    normalize 8 (.ifLt (.natural 1) (.natural 0) (.var 1) (.var 0)) = .var 0 := by cbv

theorem nested_conditional_evidence : normalize 12
    (.ifEq (.natural 0) (.natural 0)
      (.ifLt (.natural 0) (.natural 1) (.var 1) (.var 0)) (.refl (.natural 0))) =
      .refl (.natural 0) := by cbv

theorem equality_proof_drives_transport : normalize 12
    (.ifEq (.natural 4) (.natural 4)
      (.transport (.lam false .u64 (.eq (.var 0) (.var 0))) (.var 0) (.refl (.natural 4)))
      (.refl (.natural 4))) = .refl (.natural 4) := by cbv

theorem malformed_conditional_neutral :
    contract (.node .ifLt [.natural 0,.natural 1,.natural 7]) = none := by cbv

end Jihoo.NativeKernel.Conversion.Examples
