import Jihoo.NativeRootPreservation
import Jihoo.NativeConversionTransport

/-! Fixed-original-type ghost preservation for every contextual computation
step of the full-syntax normalizer. The relation is independently defined over
all native constructors; this theorem covers every rule currently present in
the native typing judgment and does not invent ownership or family rules. -/
namespace Jihoo.NativeKernel.Reduction

inductive RootStep : Term → Term → Prop where
  | beta (e : Bool) (A body a : Term) : RootStep (.app (.lam e A body) a) (body.subst (single a))
  | add (a b : Nat) : a+b < 2^64 → RootStep (.uadd (.natural a) (.natural b)) (.natural (a+b))
  | sub (a b : Nat) (p : Term) : b ≤ a → a < 2^64 →
      RootStep (.usub (.natural a) (.natural b) p) (.natural (a-b))
  | read (count : Nat) (xs : List Term) (k : Nat) (p v : Term) : xs[k]? = some v →
      RootStep (.index (.elements count xs) (.natural k) p) v
  | witnessPack (p a q : Term) : RootStep (.witness (.pack p a q)) a
  | proofPack (p a q : Term) : RootStep (.proof (.pack p a q)) q
  | derefBorrow (a : Term) : RootStep (.node .deref [.node .borrow [a]]) a
  | borrowDeref (a : Term) : RootStep (.node .borrow [.node .deref [a]]) a

  | ifLtTrue (m n : Nat) (yes no : Term) : m < n →
      RootStep (.ifLt (.natural m) (.natural n) yes no)
        (yes.subst (single (.decide (.natural m) (.natural n))))
  | ifLtFalse (m n : Nat) (yes no : Term) : n ≤ m →
      RootStep (.ifLt (.natural m) (.natural n) yes no) no
  | ifEqTrue (n : Nat) (yes no : Term) :
      RootStep (.ifEq (.natural n) (.natural n) yes no) (yes.subst (single (.refl (.natural n))))
  | ifEqFalse (m n : Nat) (yes no : Term) : m ≠ n →
      RootStep (.ifEq (.natural m) (.natural n) yes no) no

  | transportRefl (f a p : Term) : RootStep (.transport f (.refl a) p) p

inductive ListStep : List Term → List Term → Prop where
  | head : Step a b → ListStep (a :: xs) (b :: xs)
  | tail : ListStep xs ys → ListStep (a :: xs) (a :: ys)

theorem ListStep.context (pre post : List Term) (h : Step a b) :
    ListStep (pre ++ a :: post) (pre ++ b :: post) := by
  induction pre with
  | nil => exact .head h
  | cons x xs ih => exact .tail ih

theorem ListStep.length (h : ListStep xs ys) : ys.length = xs.length := by
  induction h with
  | head => rfl
  | tail _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

theorem ListStep.transport {P : Term → Prop} (h : ListStep xs ys)
    (old : ∀ x ∈ xs, P x) (changed : ∀ x y, x ∈ xs → Step x y → P y) :
    ∀ y ∈ ys, P y := by
  revert old changed
  induction h with
  | head step =>
      intro old changed y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact changed _ _ (by simp) step
      · exact old _ (by simp [hy])
  | tail hs ih =>
      intro old changed y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact old _ (by simp)
      · exact ih (fun x hx => old x (by simp [hx]))
          (fun x y hx step => changed x y (by simp [hx]) step) y hy

/-- Every step at a node is either a root computation or exactly one changed
child, retaining its position and every other child. -/
theorem Step.nodeView {op : Op} {xs : List Term} {u : Term}
    (h : Step (.node op xs) u) :
    RootStep (.node op xs) u ∨ ∃ ys, u = .node op ys ∧ ListStep xs ys := by
  cases h with
  | beta e A body a => exact .inl (.beta e A body a)
  | add a b bound => exact .inl (.add a b bound)
  | sub a b p lower upper => exact .inl (.sub a b p lower upper)
  | read count xs k p v selected => exact .inl (.read count xs k p _ selected)
  | witnessPack p a q => exact .inl (.witnessPack p _ q)
  | proofPack p a q => exact .inl (.proofPack p a _)
  | derefBorrow a => exact .inl (.derefBorrow _)
  | borrowDeref a => exact .inl (.borrowDeref _)
  | ifLtTrue m n yes no bound => exact .inl (.ifLtTrue m n yes no bound)
  | ifLtFalse m n yes no bound => exact .inl (.ifLtFalse m n yes _ bound)
  | ifEqTrue n yes no => exact .inl (.ifEqTrue n yes no)
  | ifEqFalse m n yes no apart => exact .inl (.ifEqFalse m n yes _ apart)
  | transportRefl f a p => exact .inl (.transportRefl f a _)
  | node op pre post step => exact .inr ⟨_,rfl,ListStep.context pre post step⟩

theorem Step.natural_impossible {n : Nat} {u : Term} (h : Step (.natural n) u) : False := by
  rcases h.nodeView with root | ⟨ys,he,children⟩
  · cases root
  · cases children

theorem RootStep.ghostPreservation {Γ : Context} {mode : Bool} {t u T : Term}
    (h : RootStep t u) (typed : HasType Γ mode t T) : HasType Γ true u T := by
  cases h with
  | beta => exact typed.ghostBeta
  | add a b bound => exact typed.ghostAdd bound
  | sub a b p lower upper => exact typed.ghostSub upper
  | read count xs k p v selected => exact typed.ghostRead selected
  | witnessPack => exact typed.ghostWitnessPack
  | proofPack => exact typed.ghostProofPack
  | derefBorrow => exact False.elim typed.deref_unavailable
  | borrowDeref => exact False.elim typed.borrow_unavailable
  | ifLtTrue m n yes no bound => exact typed.ghostIfLtTrue bound
  | ifLtFalse => exact typed.ghostIfLtFalse
  | ifEqTrue => exact typed.ghostIfEqTrue rfl
  | ifEqFalse => exact typed.ghostIfEqFalse
  | transportRefl => exact typed.ghostTransportRefl

end Jihoo.NativeKernel.Reduction

namespace Jihoo.NativeKernel

open Reduction (Step Steps)

private theorem congr1 (op : Op) {a b : Term} (h : Conversion.Conv a b) :
    Conversion.Conv (.node op [a]) (.node op [b]) := .node op (.cons h .nil)

private theorem congr2 (op : Op) {a a' b b' : Term}
    (ha : Conversion.Conv a a') (hb : Conversion.Conv b b') :
    Conversion.Conv (.node op [a,b]) (.node op [a',b']) := .node op (.cons ha (.cons hb .nil))

private theorem preservation_mutual :
    (∀ Γ e A s, Binder Γ e A s → ∀ A', Step A A' → Binder Γ e A' s) ∧
    (∀ Γ mode t T, HasType Γ mode t T → ∀ u, Step t u → HasType Γ true u T) := by
  constructor
  · intro Γ e A s h
    induction h using Binder.rec
      (motive_2 := fun Γ mode t T _ => ∀ u, Step t u → HasType Γ true u T) with
    | intro ht allowed ih =>
        first | intro u outer | rename_i u outer
        exact .intro (ih _ outer) (binderAllowed_conversion allowed outer.conversion)
    | var hx allowed =>
        first | intro u outer | rename_i u outer
        cases outer
    | univ bound =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children
    | prop =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children
    | u64 =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children
    | i64 =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children
    | natural bound =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children
    | integer lo hi =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children
    | array hn ih =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .array (ih _ step)
          | tail children =>
              cases children
    | lt ha hb iha ihb =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .lt (iha _ step) hb.ghost
          | tail children =>
              cases children with
            | head step =>
                exact .lt ha.ghost (ihb _ step)
            | tail children =>
                cases children
    | eq ha hb iha ihb =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .eq (iha _ step) hb.ghost
          | tail children =>
              cases children with
            | head step =>
                exact .eq ha.ghost (ihb _ step)
            | tail children =>
                cases children
    | pi hA hB ihA ihB =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .pi (ihA _ step) (hB.ghostContextConversion ((Ghost.ContextConversion.refl _).extend step.conversion _))
          | tail children =>
              cases children with
            | head step =>
                exact .pi hA (ihB _ step)
            | tail children =>
                cases children
    | lam hA hb ihA ihb =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.lam (ihA _ step)
                (hb.ghostContextConversion ((Ghost.ContextConversion.refl _).extend step.conversion _)))
                (congr2 _ (.symm step.conversion) (.refl _))
          | tail children =>
              cases children with
            | head step =>
                exact .lam hA (ihb _ step)
            | tail children =>
                cases children
    | @app Γ mode f e A B a hf ha allowed ihf iha =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (.app hf ha allowed)
        · cases children with
          | head step =>
              exact .app (ihf _ step) (by simpa using ha.ghost) (Or.inl rfl)
          | tail children =>
              cases children with
            | head step =>
                exact .convert (.app hf.ghost (by simpa using iha _ step) (Or.inl rfl))
                  (.symm (Conversion.Conv.instantiate_congr (body := B) step.conversion))
            | tail children =>
                cases children
    | uadd ha hb iha ihb =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (.uadd ha hb)
        · cases children with
          | head step =>
              exact .uadd (iha _ step) hb.ghost
          | tail children =>
              cases children with
            | head step =>
                exact .uadd ha.ghost (ihb _ step)
            | tail children =>
                cases children
    | usub ha hb hp iha ihb ihp =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (.usub ha hb hp)
        · cases children with
          | head step =>
              exact .usub (iha _ step) hb.ghost
                (hp.convert (congr2 .lt (.refl _) (congr2 .uadd step.conversion (.refl _))))
          | tail children =>
              cases children with
            | head step =>
                exact .usub ha.ghost (ihb _ step)
                  (hp.convert (congr2 .lt step.conversion (.refl _)))
            | tail children =>
                cases children with
              | head step =>
                  exact .usub ha.ghost hb.ghost (ihp _ step)
              | tail children =>
                  cases children
    | refl ha ih =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.refl (ih _ step)) (congr2 .eq (.symm step.conversion) (.symm step.conversion))
          | tail children =>
              cases children
    | zeroLe ha ih =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.zeroLe (ih _ step))
                (congr2 .lt (.refl _) (congr2 .uadd (.symm step.conversion) (.refl _)))
          | tail children =>
              cases children
    | decide ha hb hab =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact False.elim step.natural_impossible
          | tail children =>
              cases children with
            | head step =>
                exact False.elim step.natural_impossible
            | tail children =>
                cases children
    | decideConverted ha hb ca cb hm hn hmn iha ihb =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.decideConverted (iha _ step) hb.ghost
                (.trans (.symm step.conversion) ca) cb hm hn hmn)
                (congr2 .lt (.symm step.conversion) (.refl _))
          | tail children =>
              cases children with
            | head step =>
                exact .convert (.decideConverted ha.ghost (ihb _ step)
                  ca (.trans (.symm step.conversion) cb) hm hn hmn)
                  (congr2 .lt (.refl _) (.symm step.conversion))
            | tail children =>
                cases children
    | @elements n xs Γ mode hn hb hs ih =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · have hall : ∀ y ∈ ys, HasType Γ true y .i64 :=
            children.transport (fun x hx => (hs x hx).ghost) (fun x y hx hstep => ih x hx y hstep)
          have typed := HasType.elements (n := n) (by simpa [children.length] using hn)
            (by simpa [children.length] using hb) hall
          simpa only [children.length] using typed
    | index ha hi hp iha ihi ihp =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (.index ha hi hp)
        · cases children with
          | head step =>
              exact .index (iha _ step) hi.ghost hp.ghost
          | tail children =>
              cases children with
            | head step =>
                exact .index ha.ghost (ihi _ step) (hp.convert (congr2 .lt step.conversion (.refl _)))
            | tail children =>
                cases children with
              | head step =>
                  exact .index ha.ghost hi.ghost (ihp _ step)
              | tail children =>
                  cases children
    | arith ha hb iha ihb =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .arith (iha _ step) hb.ghost
          | tail children =>
              cases children with
            | head step =>
                exact .arith ha.ghost (ihb _ step)
            | tail children =>
                cases children
    | strict ha hb iha ihb =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .strict (iha _ step) hb.ghost
          | tail children =>
              cases children with
            | head step =>
                exact .strict ha.ghost (ihb _ step)
            | tail children =>
                cases children
    | ltAdd ha hb hc hp iha ihb ihc ihp =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.ltAdd (iha _ step) hb.ghost hc.ghost
                (hp.convert (congr2 .lt step.conversion (.refl _))))
                (congr2 .lt (congr2 .uadd (.symm step.conversion) (.refl _)) (.refl _))
          | tail children =>
              cases children with
            | head step =>
                exact .convert (.ltAdd ha.ghost (ihb _ step) hc.ghost
                  (hp.convert (congr2 .lt (.refl _) step.conversion)))
                  (congr2 .lt (.refl _) (congr2 .uadd (.symm step.conversion) (.refl _)))
            | tail children =>
                cases children with
              | head step =>
                  exact .convert (.ltAdd ha.ghost hb.ghost (ihc _ step) hp.ghost)
                    (congr2 .lt (congr2 .uadd (.refl _) (.symm step.conversion))
                      (congr2 .uadd (.refl _) (.symm step.conversion)))
              | tail children =>
                  cases children with
                | head step =>
                    exact .ltAdd ha.ghost hb.ghost hc.ghost (ihp _ step)
                | tail children =>
                    cases children
    | ltCancel ha hb hc hp iha ihb ihc ihp =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.ltCancel (iha _ step) hb.ghost hc.ghost
                (hp.convert (congr2 .lt (congr2 .uadd step.conversion (.refl _)) (.refl _))))
                (congr2 .lt (.symm step.conversion) (.refl _))
          | tail children =>
              cases children with
            | head step =>
                exact .convert (.ltCancel ha.ghost (ihb _ step) hc.ghost
                  (hp.convert (congr2 .lt (.refl _) (congr2 .uadd step.conversion (.refl _)))))
                  (congr2 .lt (.refl _) (.symm step.conversion))
            | tail children =>
                cases children with
              | head step =>
                  exact .ltCancel ha.ghost hb.ghost (ihc _ step)
                    (hp.convert (congr2 .lt (congr2 .uadd (.refl _) step.conversion)
                      (congr2 .uadd (.refl _) step.conversion)))
              | tail children =>
                  cases children with
                | head step =>
                    exact .ltCancel ha.ghost hb.ghost hc.ghost (ihp _ step)
                | tail children =>
                    cases children
    | ltLe ha hb hc hp hq iha ihb ihc ihp ihq =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.ltLe (iha _ step) hb.ghost hc.ghost
                (hp.convert (congr2 .lt step.conversion (.refl _))) hq.ghost)
                (congr2 .lt (.symm step.conversion) (.refl _))
          | tail children =>
              cases children with
            | head step =>
                exact .ltLe ha.ghost (ihb _ step) hc.ghost
                  (hp.convert (congr2 .lt (.refl _) step.conversion))
                  (hq.convert (congr2 .lt step.conversion (.refl _)))
            | tail children =>
                cases children with
              | head step =>
                  exact .convert (.ltLe ha.ghost hb.ghost (ihc _ step) hp.ghost
                    (hq.convert (congr2 .lt (.refl _) (congr2 .uadd step.conversion (.refl _)))))
                    (congr2 .lt (.refl _) (.symm step.conversion))
              | tail children =>
                  cases children with
                | head step =>
                    exact .ltLe ha.ghost hb.ghost hc.ghost (ihp _ step) hq.ghost
                | tail children =>
                    cases children with
                  | head step =>
                      exact .ltLe ha.ghost hb.ghost hc.ghost hp.ghost (ihq _ step)
                  | tail children =>
                      cases children
    | transport hf he hp ihf ihe ihp =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (HasType.transport (ghost := true) hf he hp)
        · cases children with
          | head step =>
              exact .convert (.transport (ihf _ step) he.ghost
                (hp.convert (congr2 .app step.conversion (.refl _))))
                (congr2 .app (.symm step.conversion) (.refl _))
          | tail children =>
              cases children with
            | head step =>
                exact .transport hf.ghost (ihe _ step) hp.ghost
            | tail children =>
                cases children with
              | head step =>
                  exact .transport hf.ghost he.ghost (ihp _ step)
              | tail children =>
                  cases children
    | refine hp ih =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .refine (ih _ step)
          | tail children =>
              cases children
    | pack hp ha hq ihp iha ihq =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.pack (ihp _ step) ha.ghost
                (hq.convert (congr2 .app step.conversion (.refl _))))
                (congr1 .refine (.symm step.conversion))
          | tail children =>
              cases children with
            | head step =>
                exact .pack hp.ghost (iha _ step)
                  (hq.convert (congr2 .app (.refl _) step.conversion))
            | tail children =>
                cases children with
              | head step =>
                  exact .pack hp.ghost ha.ghost (ihq _ step)
              | tail children =>
                  cases children
    | witness hs ih =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (.witness hs)
        · cases children with
          | head step =>
              exact .witness (ih _ step)
          | tail children =>
              cases children
    | proof hs ih =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (HasType.proof (ghost := true) hs)
        · cases children with
          | head step =>
              exact .convert (.proof (ih _ step))
                (congr2 .app (.refl _) (congr1 .witness (.symm step.conversion)))
          | tail children =>
              cases children
    | ifLt ha hb hy hn iha ihb ihy ihn =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (.ifLt ha hb hy hn)
        · cases children with
          | head step =>
              exact .ifLt (iha _ step) hb.ghost
                (hy.ghostContextConversion ((Ghost.ContextConversion.refl _).extend
                  (congr2 .lt step.conversion (.refl _)) true)) hn.ghost
          | tail children =>
              cases children with
              | head step =>
                  exact .ifLt ha.ghost (ihb _ step)
                    (hy.ghostContextConversion ((Ghost.ContextConversion.refl _).extend
                      (congr2 .lt (.refl _) step.conversion) true)) hn.ghost
              | tail children =>
                  cases children with
                  | head step => exact .ifLt ha.ghost hb.ghost (ihy _ step) hn.ghost
                  | tail children =>
                      cases children with
                      | head step => exact .ifLt ha.ghost hb.ghost hy.ghost (ihn _ step)
                      | tail children => cases children
    | ifEq ha hb hy hn iha ihb ihy ihn =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (.ifEq ha hb hy hn)
        · cases children with
          | head step =>
              exact .ifEq (iha _ step) hb.ghost
                (hy.ghostContextConversion ((Ghost.ContextConversion.refl _).extend
                  (congr2 .eq step.conversion (.refl _)) true)) hn.ghost
          | tail children =>
              cases children with
              | head step =>
                  exact .ifEq ha.ghost (ihb _ step)
                    (hy.ghostContextConversion ((Ghost.ContextConversion.refl _).extend
                      (congr2 .eq (.refl _) step.conversion) true)) hn.ghost
              | tail children =>
                  cases children with
                  | head step => exact .ifEq ha.ghost hb.ghost (ihy _ step) hn.ghost
                  | tail children =>
                      cases children with
                      | head step => exact .ifEq ha.ghost hb.ghost hy.ghost (ihn _ step)
                      | tail children => cases children
    | absurd hT hp allowed ihT ihp =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.absurd (ihT _ step) hp.ghost (Or.inl rfl)) (.symm step.conversion)
          | tail children =>
              cases children with
              | head step => exact .absurd hT.ghost (ihp _ step) (Or.inl rfl)
              | tail children => cases children
    | convert ht hc ih =>
        first | intro u outer | rename_i u outer
        exact .convert (ih _ outer) hc
  · intro Γ mode t T h
    induction h using HasType.rec
      (motive_1 := fun Γ e A s _ => ∀ A', Step A A' → Binder Γ e A' s) with
    | intro ht allowed ih =>
        first | intro u outer | rename_i u outer
        exact .intro (ih _ outer) (binderAllowed_conversion allowed outer.conversion)
    | var hx allowed =>
        first | intro u outer | rename_i u outer
        cases outer
    | univ bound =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children
    | prop =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children
    | u64 =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children
    | i64 =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children
    | natural bound =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children
    | integer lo hi =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children
    | array hn ih =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .array (ih _ step)
          | tail children =>
              cases children
    | lt ha hb iha ihb =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .lt (iha _ step) hb.ghost
          | tail children =>
              cases children with
            | head step =>
                exact .lt ha.ghost (ihb _ step)
            | tail children =>
                cases children
    | eq ha hb iha ihb =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .eq (iha _ step) hb.ghost
          | tail children =>
              cases children with
            | head step =>
                exact .eq ha.ghost (ihb _ step)
            | tail children =>
                cases children
    | pi hA hB ihA ihB =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .pi (ihA _ step) (hB.ghostContextConversion ((Ghost.ContextConversion.refl _).extend step.conversion _))
          | tail children =>
              cases children with
            | head step =>
                exact .pi hA (ihB _ step)
            | tail children =>
                cases children
    | lam hA hb ihA ihb =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.lam (ihA _ step)
                (hb.ghostContextConversion ((Ghost.ContextConversion.refl _).extend step.conversion _)))
                (congr2 _ (.symm step.conversion) (.refl _))
          | tail children =>
              cases children with
            | head step =>
                exact .lam hA (ihb _ step)
            | tail children =>
                cases children
    | @app Γ mode f e A B a hf ha allowed ihf iha =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (.app hf ha allowed)
        · cases children with
          | head step =>
              exact .app (ihf _ step) (by simpa using ha.ghost) (Or.inl rfl)
          | tail children =>
              cases children with
            | head step =>
                exact .convert (.app hf.ghost (by simpa using iha _ step) (Or.inl rfl))
                  (.symm (Conversion.Conv.instantiate_congr (body := B) step.conversion))
            | tail children =>
                cases children
    | uadd ha hb iha ihb =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (.uadd ha hb)
        · cases children with
          | head step =>
              exact .uadd (iha _ step) hb.ghost
          | tail children =>
              cases children with
            | head step =>
                exact .uadd ha.ghost (ihb _ step)
            | tail children =>
                cases children
    | usub ha hb hp iha ihb ihp =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (.usub ha hb hp)
        · cases children with
          | head step =>
              exact .usub (iha _ step) hb.ghost
                (hp.convert (congr2 .lt (.refl _) (congr2 .uadd step.conversion (.refl _))))
          | tail children =>
              cases children with
            | head step =>
                exact .usub ha.ghost (ihb _ step)
                  (hp.convert (congr2 .lt step.conversion (.refl _)))
            | tail children =>
                cases children with
              | head step =>
                  exact .usub ha.ghost hb.ghost (ihp _ step)
              | tail children =>
                  cases children
    | refl ha ih =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.refl (ih _ step)) (congr2 .eq (.symm step.conversion) (.symm step.conversion))
          | tail children =>
              cases children
    | zeroLe ha ih =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.zeroLe (ih _ step))
                (congr2 .lt (.refl _) (congr2 .uadd (.symm step.conversion) (.refl _)))
          | tail children =>
              cases children
    | decide ha hb hab =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact False.elim step.natural_impossible
          | tail children =>
              cases children with
            | head step =>
                exact False.elim step.natural_impossible
            | tail children =>
                cases children
    | decideConverted ha hb ca cb hm hn hmn iha ihb =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.decideConverted (iha _ step) hb.ghost
                (.trans (.symm step.conversion) ca) cb hm hn hmn)
                (congr2 .lt (.symm step.conversion) (.refl _))
          | tail children =>
              cases children with
            | head step =>
                exact .convert (.decideConverted ha.ghost (ihb _ step)
                  ca (.trans (.symm step.conversion) cb) hm hn hmn)
                  (congr2 .lt (.refl _) (.symm step.conversion))
            | tail children =>
                cases children
    | @elements n xs Γ mode hn hb hs ih =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · have hall : ∀ y ∈ ys, HasType Γ true y .i64 :=
            children.transport (fun x hx => (hs x hx).ghost) (fun x y hx hstep => ih x hx y hstep)
          have typed := HasType.elements (n := n) (by simpa [children.length] using hn)
            (by simpa [children.length] using hb) hall
          simpa only [children.length] using typed
    | index ha hi hp iha ihi ihp =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (.index ha hi hp)
        · cases children with
          | head step =>
              exact .index (iha _ step) hi.ghost hp.ghost
          | tail children =>
              cases children with
            | head step =>
                exact .index ha.ghost (ihi _ step) (hp.convert (congr2 .lt step.conversion (.refl _)))
            | tail children =>
                cases children with
              | head step =>
                  exact .index ha.ghost hi.ghost (ihp _ step)
              | tail children =>
                  cases children
    | arith ha hb iha ihb =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .arith (iha _ step) hb.ghost
          | tail children =>
              cases children with
            | head step =>
                exact .arith ha.ghost (ihb _ step)
            | tail children =>
                cases children
    | strict ha hb iha ihb =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .strict (iha _ step) hb.ghost
          | tail children =>
              cases children with
            | head step =>
                exact .strict ha.ghost (ihb _ step)
            | tail children =>
                cases children
    | ltAdd ha hb hc hp iha ihb ihc ihp =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.ltAdd (iha _ step) hb.ghost hc.ghost
                (hp.convert (congr2 .lt step.conversion (.refl _))))
                (congr2 .lt (congr2 .uadd (.symm step.conversion) (.refl _)) (.refl _))
          | tail children =>
              cases children with
            | head step =>
                exact .convert (.ltAdd ha.ghost (ihb _ step) hc.ghost
                  (hp.convert (congr2 .lt (.refl _) step.conversion)))
                  (congr2 .lt (.refl _) (congr2 .uadd (.symm step.conversion) (.refl _)))
            | tail children =>
                cases children with
              | head step =>
                  exact .convert (.ltAdd ha.ghost hb.ghost (ihc _ step) hp.ghost)
                    (congr2 .lt (congr2 .uadd (.refl _) (.symm step.conversion))
                      (congr2 .uadd (.refl _) (.symm step.conversion)))
              | tail children =>
                  cases children with
                | head step =>
                    exact .ltAdd ha.ghost hb.ghost hc.ghost (ihp _ step)
                | tail children =>
                    cases children
    | ltCancel ha hb hc hp iha ihb ihc ihp =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.ltCancel (iha _ step) hb.ghost hc.ghost
                (hp.convert (congr2 .lt (congr2 .uadd step.conversion (.refl _)) (.refl _))))
                (congr2 .lt (.symm step.conversion) (.refl _))
          | tail children =>
              cases children with
            | head step =>
                exact .convert (.ltCancel ha.ghost (ihb _ step) hc.ghost
                  (hp.convert (congr2 .lt (.refl _) (congr2 .uadd step.conversion (.refl _)))))
                  (congr2 .lt (.refl _) (.symm step.conversion))
            | tail children =>
                cases children with
              | head step =>
                  exact .ltCancel ha.ghost hb.ghost (ihc _ step)
                    (hp.convert (congr2 .lt (congr2 .uadd (.refl _) step.conversion)
                      (congr2 .uadd (.refl _) step.conversion)))
              | tail children =>
                  cases children with
                | head step =>
                    exact .ltCancel ha.ghost hb.ghost hc.ghost (ihp _ step)
                | tail children =>
                    cases children
    | ltLe ha hb hc hp hq iha ihb ihc ihp ihq =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.ltLe (iha _ step) hb.ghost hc.ghost
                (hp.convert (congr2 .lt step.conversion (.refl _))) hq.ghost)
                (congr2 .lt (.symm step.conversion) (.refl _))
          | tail children =>
              cases children with
            | head step =>
                exact .ltLe ha.ghost (ihb _ step) hc.ghost
                  (hp.convert (congr2 .lt (.refl _) step.conversion))
                  (hq.convert (congr2 .lt step.conversion (.refl _)))
            | tail children =>
                cases children with
              | head step =>
                  exact .convert (.ltLe ha.ghost hb.ghost (ihc _ step) hp.ghost
                    (hq.convert (congr2 .lt (.refl _) (congr2 .uadd step.conversion (.refl _)))))
                    (congr2 .lt (.refl _) (.symm step.conversion))
              | tail children =>
                  cases children with
                | head step =>
                    exact .ltLe ha.ghost hb.ghost hc.ghost (ihp _ step) hq.ghost
                | tail children =>
                    cases children with
                  | head step =>
                      exact .ltLe ha.ghost hb.ghost hc.ghost hp.ghost (ihq _ step)
                  | tail children =>
                      cases children
    | transport hf he hp ihf ihe ihp =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (HasType.transport (ghost := true) hf he hp)
        · cases children with
          | head step =>
              exact .convert (.transport (ihf _ step) he.ghost
                (hp.convert (congr2 .app step.conversion (.refl _))))
                (congr2 .app (.symm step.conversion) (.refl _))
          | tail children =>
              cases children with
            | head step =>
                exact .transport hf.ghost (ihe _ step) hp.ghost
            | tail children =>
                cases children with
              | head step =>
                  exact .transport hf.ghost he.ghost (ihp _ step)
              | tail children =>
                  cases children
    | refine hp ih =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .refine (ih _ step)
          | tail children =>
              cases children
    | pack hp ha hq ihp iha ihq =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.pack (ihp _ step) ha.ghost
                (hq.convert (congr2 .app step.conversion (.refl _))))
                (congr1 .refine (.symm step.conversion))
          | tail children =>
              cases children with
            | head step =>
                exact .pack hp.ghost (iha _ step)
                  (hq.convert (congr2 .app (.refl _) step.conversion))
            | tail children =>
                cases children with
              | head step =>
                  exact .pack hp.ghost ha.ghost (ihq _ step)
              | tail children =>
                  cases children
    | witness hs ih =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (.witness hs)
        · cases children with
          | head step =>
              exact .witness (ih _ step)
          | tail children =>
              cases children
    | proof hs ih =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (HasType.proof (ghost := true) hs)
        · cases children with
          | head step =>
              exact .convert (.proof (ih _ step))
                (congr2 .app (.refl _) (congr1 .witness (.symm step.conversion)))
          | tail children =>
              cases children
    | ifLt ha hb hy hn iha ihb ihy ihn =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (.ifLt ha hb hy hn)
        · cases children with
          | head step =>
              exact .ifLt (iha _ step) hb.ghost
                (hy.ghostContextConversion ((Ghost.ContextConversion.refl _).extend
                  (congr2 .lt step.conversion (.refl _)) true)) hn.ghost
          | tail children =>
              cases children with
              | head step =>
                  exact .ifLt ha.ghost (ihb _ step)
                    (hy.ghostContextConversion ((Ghost.ContextConversion.refl _).extend
                      (congr2 .lt (.refl _) step.conversion) true)) hn.ghost
              | tail children =>
                  cases children with
                  | head step => exact .ifLt ha.ghost hb.ghost (ihy _ step) hn.ghost
                  | tail children =>
                      cases children with
                      | head step => exact .ifLt ha.ghost hb.ghost hy.ghost (ihn _ step)
                      | tail children => cases children
    | ifEq ha hb hy hn iha ihb ihy ihn =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · exact root.ghostPreservation (.ifEq ha hb hy hn)
        · cases children with
          | head step =>
              exact .ifEq (iha _ step) hb.ghost
                (hy.ghostContextConversion ((Ghost.ContextConversion.refl _).extend
                  (congr2 .eq step.conversion (.refl _)) true)) hn.ghost
          | tail children =>
              cases children with
              | head step =>
                  exact .ifEq ha.ghost (ihb _ step)
                    (hy.ghostContextConversion ((Ghost.ContextConversion.refl _).extend
                      (congr2 .eq (.refl _) step.conversion) true)) hn.ghost
              | tail children =>
                  cases children with
                  | head step => exact .ifEq ha.ghost hb.ghost (ihy _ step) hn.ghost
                  | tail children =>
                      cases children with
                      | head step => exact .ifEq ha.ghost hb.ghost hy.ghost (ihn _ step)
                      | tail children => cases children
    | absurd hT hp allowed ihT ihp =>
        first | intro u outer | rename_i u outer
        rcases outer.nodeView with root | ⟨ys,rfl,children⟩
        · cases root
        · cases children with
          | head step =>
              exact .convert (.absurd (ihT _ step) hp.ghost (Or.inl rfl)) (.symm step.conversion)
          | tail children =>
              cases children with
              | head step => exact .absurd hT.ghost (ihp _ step) (Or.inl rfl)
              | tail children => cases children
    | convert ht hc ih =>
        first | intro u outer | rename_i u outer
        exact .convert (ih _ outer) hc

/-- Contextual native computation preserves binder formation and its sort. -/
theorem Binder.ghostPreservation {Γ : Context} {e : Bool} {A A' : Term} {s : SortTag}
    (h : Binder Γ e A s) (step : Step A A') : Binder Γ e A' s :=
  preservation_mutual.1 Γ e A s h A' step

/-- Every one-child contextual computation retains the exact original raw type.
The output is ghost mode, including when the input derivation was runtime mode. -/
theorem HasType.ghostPreservation {Γ : Context} {mode : Bool} {t u T : Term}
    (h : HasType Γ mode t T) (step : Step t u) : HasType Γ true u T :=
  preservation_mutual.2 Γ mode t T h u step

theorem Binder.ghostPreservation_steps {Γ : Context} {e : Bool} {A A' : Term} {s : SortTag}
    (h : Binder Γ e A s) (steps : Steps A A') : Binder Γ e A' s := by
  induction steps with
  | refl => exact h
  | next step _ ih => exact ih (h.ghostPreservation step)

theorem HasType.ghostPreservation_steps {Γ : Context} {mode : Bool} {t u T : Term}
    (h : HasType Γ mode t T) (steps : Steps t u) : HasType Γ true u T := by
  induction steps generalizing mode with
  | refl => exact h.ghost
  | next step _ ih => exact ih (h.ghostPreservation step)

/-- The actual bounded full-syntax normalizer preserves the original type,
including reduction beneath annotations, dependent binders and proof fields. -/
theorem HasType.ghostNormalize {Γ : Context} {mode : Bool} {t T : Term}
    (h : HasType Γ mode t T) (fuel : Nat) :
    HasType Γ true (Conversion.normalize fuel t) T :=
  h.ghostPreservation_steps (Conversion.normalize_steps fuel t)

theorem Binder.ghostNormalize {Γ : Context} {e : Bool} {A : Term} {s : SortTag}
    (h : Binder Γ e A s) (fuel : Nat) : Binder Γ e (Conversion.normalize fuel A) s :=
  h.ghostPreservation_steps (Conversion.normalize_steps fuel A)

/-- Term and result-type normalization may use independent budgets. -/
theorem HasType.ghostNormalizeBoth {Γ : Context} {mode : Bool} {t T : Term}
    (h : HasType Γ mode t T) (termFuel typeFuel : Nat) :
    HasType Γ true (Conversion.normalize termFuel t) (Conversion.normalize typeFuel T) :=
  (h.ghostNormalize termFuel).convert (Conversion.normalize_sound typeFuel T)

end Jihoo.NativeKernel
