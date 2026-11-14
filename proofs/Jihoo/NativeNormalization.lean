import Jihoo.NativeConversion

/-! Exact forward computational meaning of the full-syntax bounded normalizer.
The reduction relation is defined independently, with root computation and
one-child contextual closure under every native Op. Reachability is proved for
all trees; this file does not assume or assert full native typing preservation. -/
namespace Jihoo.NativeKernel.Reduction

inductive Step : Term → Term → Prop where
  | beta (e : Bool) (A body a : Term) :
      Step (.node .app [.node (.lam e) [A, body], a]) (body.subst (single a))
  | add (a b : Nat) : a + b < 2^64 →
      Step (.node .uadd [.node (.natural a) [], .node (.natural b) []]) (.node (.natural (a+b)) [])
  | sub (a b : Nat) (p : Term) : b ≤ a → a < 2^64 →
      Step (.node .usub [.node (.natural a) [], .node (.natural b) [], p]) (.node (.natural (a-b)) [])
  | read (count : Nat) (xs : List Term) (k : Nat) (p v : Term) : xs[k]? = some v →
      Step (.node .index [.node (.elements count) xs, .node (.natural k) [], p]) v
  | witnessPack (p a q : Term) : Step (.node .witness [.node .pack [p,a,q]]) a
  | proofPack (p a q : Term) : Step (.node .proof [.node .pack [p,a,q]]) q
  | derefBorrow (a : Term) : Step (.node .deref [.node .borrow [a]]) a
  | borrowDeref (a : Term) : Step (.node .borrow [.node .deref [a]]) a
  | node (op : Op) (pre post : List Term) : Step a b →
      Step (.node op (pre ++ a :: post)) (.node op (pre ++ b :: post))

private theorem list_refl (xs : List Term) : Conversion.ListRel Conversion.Conv xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (.refl _) ih

private theorem list_replace (pre post : List Term) (h : Conversion.Conv a b) :
    Conversion.ListRel Conversion.Conv (pre ++ a :: post) (pre ++ b :: post) := by
  induction pre with
  | nil => exact .cons h (list_refl post)
  | cons x xs ih => exact .cons (.refl _) ih

theorem Step.conversion {t u : Term} (h : Step t u) : Conversion.Conv t u := by
  induction h with
  | beta e A body a => exact .beta e A body a
  | add a b bound => exact .add a b bound
  | sub a b p hb ha => exact .sub a b p hb ha
  | read count xs k p v selected => exact .read count xs k p v selected
  | witnessPack p a q => exact .witnessPack p a q
  | proofPack p a q => exact .proofPack p a q
  | derefBorrow a => exact .derefBorrow a
  | borrowDeref a => exact .borrowDeref a
  | node op pre post _ ih => exact .node op (list_replace pre post ih)

inductive Steps : Term → Term → Prop where
  | refl : Steps t t
  | next : Step t u → Steps u v → Steps t v

theorem Steps.trans (h : Steps t u) (h' : Steps u v) : Steps t v := by
  induction h with
  | refl => exact h'
  | next hs _ ih => exact .next hs (ih h')

theorem Steps.map (h : Steps t u) (F : Term → Term)
    (lift : ∀ {a b}, Step a b → Step (F a) (F b)) : Steps (F t) (F u) := by
  induction h with
  | refl => exact .refl
  | next hs _ ih => exact .next (lift hs) ih

theorem Steps.conversion (h : Steps t u) : Conversion.Conv t u := by
  induction h with
  | refl => exact .refl _
  | next hs _ ih => exact .trans hs.conversion ih

end Jihoo.NativeKernel.Reduction

namespace Jihoo.NativeKernel.Conversion

open Reduction (Step Steps)

theorem contract_step {t u : Term} (h : contract t = some u) : Step t u := by
  fun_cases contract t <;> simp_all [contract]
  all_goals try (rcases h with ⟨hbound, h⟩)
  all_goals try subst u
  all_goals first
    | exact .beta _ _ _ _
    | exact .add _ _ (by omega)
    | exact .sub _ _ _ (by omega) (by omega)
    | exact .read _ _ _ _ _ (by assumption)
    | exact .witnessPack _ _ _
    | exact .proofPack _ _ _
    | exact .derefBorrow _
    | exact .borrowDeref _

private theorem children_prefix (op : Op) (f : Term → Term)
    (h : ∀ t, Steps t (f t)) (xs pre : List Term) :
    Steps (.node op (pre ++ xs)) (.node op (pre ++ xs.map f)) := by
  induction xs generalizing pre with
  | nil => exact .refl
  | cons x xs ih =>
      have head := (h x).map (fun y => .node op (pre ++ y :: xs))
        (fun hs => Step.node op pre xs hs)
      have tail := ih (pre ++ [f x])
      simp only [List.append_assoc, List.singleton_append] at tail
      exact head.trans tail

theorem children_steps (t : Term) (f : Term → Term) (h : ∀ t, Steps t (f t)) :
    Steps t (children f t) := by
  cases t with
  | var => exact .refl
  | node op xs => exact children_prefix op f h xs []

/-- The exact result computed from syntax is a forward reduct at every fuel. -/
theorem normalize_steps (fuel : Nat) (t : Term) : Steps t (normalize fuel t) := by
  induction fuel generalizing t with
  | zero => exact .refl
  | succ fuel ih =>
      have hc := children_steps t (normalize fuel) ih
      simp only [normalize]
      split
      · rename_i u hu
        exact hc.trans (.next (contract_step hu) (ih u))
      · exact hc

theorem equal_common_reduct {fuel : Nat} {a b : Term} (h : equal fuel a b = true) :
    ∃ u, Steps a u ∧ Steps b u := by
  have he : normalize fuel a = normalize fuel b := of_decide_eq_true h
  exact ⟨normalize fuel b, he ▸ normalize_steps fuel a, normalize_steps fuel b⟩

end Jihoo.NativeKernel.Conversion
