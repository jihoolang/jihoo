import Jihoo.NativeChecker
import Jihoo.NativeConfluence

/-! Acceptance soundness of the universe-aware data-input native-tree checker.
The mutually inductive declarative rules precede and do not refer to inference.
No derivation, typing certificate or soundness assumption is supplied as input. -/
namespace Jihoo.NativeKernel.Checker

theorem accepts_elim {fuel : Nat} {inferred : Option Term} {expected : Term}
    (h : accepts fuel inferred expected = true) :
    ∃ actual, inferred = some actual ∧ Conversion.Conv actual expected := by
  cases inferred with
  | none => simp [accepts] at h
  | some actual => exact ⟨actual, rfl, Conversion.equal_sound h⟩

theorem expose_elim {fuel : Nat} {inferred : Option Term} {expected : Term}
    (h : expose fuel inferred = some expected) :
    ∃ actual, inferred = some actual ∧ Conversion.Conv actual expected := by
  cases inferred with
  | none => simp [expose] at h
  | some actual =>
      simp only [expose, Option.map_some] at h
      cases h
      exact ⟨actual, rfl, Conversion.normalize_sound fuel actual⟩

theorem binderOK_sound {fuel : Nat} {e : Bool} {A : Term} {s : SortTag}
    (h : binderOK fuel e A s = true) : binderAllowed e A s := by
  cases e with
  | false =>
      change s ≠ .prop
      exact of_decide_eq_true h
  | true =>
      rcases Bool.or_eq_true_iff.mp h with hs | hA
      · exact Or.inl (of_decide_eq_true hs)
      · exact Or.inr (Conversion.equal_sound hA)

theorem applicationOK_sound {fuel : Nat} {ghost : Bool} {A a : Term}
    (h : applicationOK fuel ghost A a = true) : applicationAllowed ghost A a := by
  cases ghost with
  | true => exact Or.inl rfl
  | false =>
      cases hk : kindOf A with
      | false => exact Or.inr (Or.inl hk)
      | true =>
          have hs : firstOrderKind A = true ∧ plain (Conversion.normalize fuel a) = true := by
            simpa [applicationOK, hk] using h
          exact Or.inr (Or.inr ⟨hs.1, _, Conversion.normalize_sound fuel a, hs.2⟩)

/-- A rigid canonical nonfunction head cannot become a Pi by conversion. -/
theorem nonFunctionHead_sound {T : Term} (h : nonFunctionHead T = true) : nonFunction T := by
  intro e A B converted
  fun_cases nonFunctionHead T <;> simp_all only [nonFunctionHead, Bool.false_eq_true]
  all_goals first
    | exact Conversion.Conv.variable_node_separate rfl converted
    | exact Conversion.Conv.rigid_disjoint rfl rfl (by intro same; cases same) converted

theorem nonFunction_of_conversion {A B : Term} (conv : Conversion.Conv A B)
    (h : nonFunction B) : nonFunction A :=
  fun e X Y converted => h e X Y (.trans (.symm conv) converted)

/-- Successful evidence-binder removal proves exact reweakening, including
when the result is a function type with its own binders. -/
theorem branch_type_reweakens {Y B : Term}
    (h : PartialRenaming.shift (-1) 0 Y = some B) : B.rename Nat.succ = Y := by
  have shifted := PartialRenaming.shift_negative_reweakens (delta := -1) (by decide) h
  change B.rename (PartialRenaming.raiseIndex 0 1) = Y at shifted
  have raised : PartialRenaming.raiseIndex 0 1 = Nat.succ := by
    funext x
    simp [PartialRenaming.raiseIndex]
  rw [raised] at shifted
  exact shifted

theorem loopSort_sound {level : Term} {proof : Bool}
    (h : loopSort level = some proof) : level = loopSortTerm proof := by
  unfold loopSort at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · contradiction

theorem loopMotiveOK_sound {fuel : Nat} {ghost proof : Bool} {motive : Term}
    (h : loopMotiveOK fuel proof motive = true) : loopMotiveAllowed ghost proof motive := by
  rcases Bool.or_eq_true_iff.mp h with hp | hm
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr ⟨_, Conversion.normalize_sound fuel motive, hm⟩)

private theorem sound_mutual (fuel : Nat) :
    (∀ ctx ghost t T, infer fuel ctx ghost t = some T → HasType ctx ghost t T) ∧
    (∀ ctx e A s, binder fuel ctx e A = some s → Binder ctx e A s) := by
  induction fuel with
  | zero =>
      constructor
      · intro ctx ghost t T h; simp [infer] at h
      · intro ctx e A s h; simp [binder] at h
  | succ fuel ih =>
      rcases ih with ⟨hi, hbind⟩
      have hc : ∀ ctx ghost t T, accepts fuel (infer fuel ctx ghost t) T = true →
          HasType ctx ghost t T := by
        intro ctx ghost t T h
        obtain ⟨actual, ha, conv⟩ := accepts_elim h
        exact .convert (hi ctx ghost t actual ha) conv
      have he : ∀ ctx ghost t T, expose fuel (infer fuel ctx ghost t) = some T →
          HasType ctx ghost t T := by
        intro ctx ghost t T h
        obtain ⟨actual, ha, conv⟩ := expose_elim h
        exact .convert (hi ctx ghost t actual ha) conv
      constructor
      · intro ctx ghost t T h
        simp only [infer] at h
        split at h
        case h_1 =>
          rename_i x
          split at h
          · rename_i b hb
            split at h
            · rename_i hu
              cases h
              exact .var hb hu
            · contradiction
          · contradiction
        case h_2 =>
          split at h
          · rename_i hn
            cases h
            exact .univ hn
          · contradiction
        case h_3 => cases h; exact .prop
        case h_4 => cases h; exact .u64
        case h_5 => cases h; exact .i64
        case h_6 =>
          split at h
          · rename_i hn
            cases h
            exact .natural hn
          · contradiction
        case h_7 =>
          split at h
          · rename_i hn
            cases h
            exact .integer hn.1 hn.2
          · contradiction
        case h_8 =>
          rename_i n
          split at h
          · rename_i hn
            cases h
            exact .array (hc ctx true n _ hn)
          · contradiction
        case h_9 =>
          rename_i a b
          split at h
          · rename_i hab
            cases h
            exact .lt (hc ctx true a _ hab.1) (hc ctx true b _ hab.2)
          · contradiction
        case h_10 =>
          rename_i a b
          split at h
          · rename_i hab
            cases h
            exact .eq (hc ctx true a _ hab.1) (hc ctx true b _ hab.2)
          · contradiction
        case h_11 =>
          rename_i e A B
          split at h
          · rename_i s hs
            split at h
            · rename_i U hB
              cases hr : SortTag.ofTerm U with
              | none => simp [hr] at h
              | some r =>
                  simp only [hr, Option.map_some] at h
                  cases h
                  have hB' := he (⟨A, e⟩ :: ctx) true B U hB
                  rw [SortTag.ofTerm_sound hr] at hB'
                  exact .pi (hbind ctx e A s hs) hB'
            · contradiction
          · contradiction
        case h_12 =>
          rename_i e A body
          split at h
          · rename_i s hs
            cases hb : infer fuel (⟨A, e⟩ :: ctx) ghost body with
            | none => simp [hb] at h
            | some B =>
                simp only [hb, Option.map_some] at h
                cases h
                exact .lam (hbind ctx e A s hs) (hi _ ghost body B hb)
          · contradiction
        case h_13 =>
          rename_i f a
          split at h
          · rename_i e A B hf
            split at h
            · rename_i ha
              cases h
              exact .app (he ctx ghost f _ hf) (hc ctx (ghost || e) a A ha.1) (applicationOK_sound ha.2.1)
            · contradiction
          · contradiction
        case h_14 =>
          rename_i a b
          split at h
          · rename_i hab
            cases h
            exact .uadd (hc ctx ghost a _ hab.1) (hc ctx ghost b _ hab.2)
          · contradiction
        case h_15 =>
          rename_i a b p
          split at h
          · rename_i habp
            cases h
            exact .usub (hc ctx ghost a _ habp.1) (hc ctx ghost b _ habp.2.1)
              (hc ctx true p _ habp.2.2)
          · contradiction
        case h_16 =>
          rename_i a
          split at h
          · rename_i ha
            cases h
            exact .refl (hc ctx true a _ ha)
          · contradiction
        case h_17 =>
          rename_i a
          split at h
          · rename_i ha
            cases h
            exact .zeroLe (hc ctx true a _ ha)
          · contradiction
        case h_18 =>
          rename_i a b
          split at h
          · rename_i hab
            split at h
            · rename_i m n hm hn
              split at h
              · rename_i bounds
                cases h
                have haConv := Conversion.normalize_sound fuel a
                have hbConv := Conversion.normalize_sound fuel b
                rw [hm] at haConv
                rw [hn] at hbConv
                exact .decideConverted (hc ctx true a _ hab.1) (hc ctx true b _ hab.2)
                  haConv hbConv bounds.1 bounds.2.1 bounds.2.2
              · contradiction
            · contradiction
          · contradiction
        case h_19 =>
          rename_i n xs
          split at h
          · rename_i hxs
            cases h
            exact .elements hxs.1 hxs.2.1 (fun x hx =>
              hc ctx ghost x _ ((List.all_eq_true.mp hxs.2.2) x hx))
          · contradiction
        case h_20 =>
          rename_i a i p
          split at h
          · rename_i n ha
            split at h
            · rename_i hip
              cases h
              exact .index (he ctx ghost a _ ha) (hc ctx ghost i _ hip.1) (hc ctx true p _ hip.2)
            · contradiction
          · contradiction
        case h_21 =>
          rename_i op a b
          split at h
          · rename_i hab
            cases h
            exact .arith (hc ctx ghost a _ hab.1) (hc ctx ghost b _ hab.2)
          · contradiction
        case h_22 =>
          rename_i a b
          split at h
          · rename_i A ha
            exact .strict (he ctx ghost a A ha) (hi ctx ghost b T h)
          · contradiction
        case h_23 =>
          rename_i a b c p
          split at h
          · rename_i hp
            cases h
            exact .ltAdd (hc ctx true a _ hp.1) (hc ctx true b _ hp.2.1)
              (hc ctx true c _ hp.2.2.1) (hc ctx true p _ hp.2.2.2)
          · contradiction
        case h_24 =>
          rename_i a b c p
          split at h
          · rename_i hp
            cases h
            exact .ltCancel (hc ctx true a _ hp.1) (hc ctx true b _ hp.2.1)
              (hc ctx true c _ hp.2.2.1) (hc ctx true p _ hp.2.2.2)
          · contradiction
        case h_25 =>
          rename_i a b c p q
          split at h
          · rename_i hp
            cases h
            exact .ltLe (hc ctx true a _ hp.1) (hc ctx true b _ hp.2.1)
              (hc ctx true c _ hp.2.2.1) (hc ctx true p _ hp.2.2.2.1) (hc ctx true q _ hp.2.2.2.2)
          · contradiction
        case h_26 =>
          rename_i f e p
          split at h
          · rename_i a b hEq
            split at h
            · rename_i hp
              cases h
              exact .transport (hc ctx true f _ hp.1) (he ctx true e _ hEq) (hc ctx true p _ hp.2)
            · contradiction
          · contradiction
        case h_27 =>
          rename_i p
          split at h
          · rename_i hp
            cases h
            exact .refine (hc ctx true p _ hp)
          · contradiction
        case h_28 =>
          rename_i p a q
          split at h
          · rename_i hp
            cases h
            exact .pack (hc ctx true p _ hp.1) (hc ctx ghost a _ hp.2.1) (hc ctx true q _ hp.2.2)
          · contradiction
        case h_29 =>
          rename_i s
          split at h
          · rename_i p hs
            cases h
            exact .witness (he ctx ghost s _ hs)
          · contradiction
        case h_30 =>
          rename_i s
          split at h
          · rename_i p hs
            cases h
            exact .proof (he ctx true s _ hs)
          · contradiction
        case h_31 =>
          rename_i a b yes no
          split at h
          · rename_i hab
            split at h
            · rename_i Y hy
              split at h
              · rename_i B lowered
                split at h
                · rename_i hn
                  cases h
                  have hyes := he (⟨.lt a b, true⟩ :: ctx) ghost yes Y hy
                  rw [← branch_type_reweakens lowered] at hyes
                  exact .ifLt (hc ctx ghost a _ hab.1) (hc ctx ghost b _ hab.2)
                    hyes (hc ctx ghost no _ hn)
                · contradiction
              · contradiction
            · contradiction
          · contradiction
        case h_32 =>
          rename_i a b yes no
          split at h
          · rename_i hab
            split at h
            · rename_i Y hy
              split at h
              · rename_i B lowered
                split at h
                · rename_i hn
                  cases h
                  have hyes := he (⟨.eq a b, true⟩ :: ctx) ghost yes Y hy
                  rw [← branch_type_reweakens lowered] at hyes
                  exact .ifEq (hc ctx ghost a _ hab.1) (hc ctx ghost b _ hab.2)
                    hyes (hc ctx ghost no _ hn)
                · contradiction
              · contradiction
            · contradiction
          · contradiction
        case h_33 =>
          rename_i U p
          split at h
          · rename_i V hU
            split at h
            · rename_i s hs
              split at h
              · rename_i hhead
                split at h
                · rename_i i n hp
                  split at h
                  · rename_i hz
                    cases h
                    have typed := he ctx true T V hU
                    rw [SortTag.ofTerm_sound hs] at typed
                    have evidence := he ctx true p (.lt i n) hp
                    have bound : Conversion.Conv (.lt i n) (.lt i (.natural 0)) :=
                      .node .lt (.cons (.refl _) (.cons (Conversion.equal_sound hz) .nil))
                    exact .absurd typed (evidence.convert bound)
                      (Or.inr (nonFunction_of_conversion (Conversion.normalize_sound fuel T)
                        (nonFunctionHead_sound hhead)))
                  · contradiction
                · contradiction
              · contradiction
            · contradiction
          · contradiction
        case h_34 =>
          rename_i n init body
          split at h
          · rename_i checked
            cases h
            exact .foldI64 (hc ctx ghost n _ checked.1) (hc ctx ghost init _ checked.2.1)
              (hc ctx ghost body _ checked.2.2.1) (Or.inr checked.2.2.2)
          · contradiction
        case h_35 =>
          rename_i n motive init body
          split at h
          · rename_i domain level hm
            split at h
            · rename_i hdomain
              split at h
              · rename_i proof hs
                split at h
                · rename_i hprofile
                  split at h
                  · rename_i checked
                    cases h
                    have typed := he ctx true motive (.pi false domain level) hm
                    rw [loopSort_sound hs] at typed
                    have expected : Conversion.Conv (.pi false domain (loopSortTerm proof))
                        (.pi false .u64 (loopSortTerm proof)) :=
                      .node (.pi false) (.cons (Conversion.equal_sound hdomain) (.cons (.refl _) .nil))
                    exact .loop (typed.convert expected) (loopMotiveOK_sound hprofile)
                      (hc ctx (ghost || proof) n _ checked.1)
                      (hc ctx (ghost || proof) init _ checked.2.1)
                      (hc ctx (ghost || proof) body _ checked.2.2.1)
                      (Or.inr checked.2.2.2)
                  · contradiction
                · contradiction
              · contradiction
            · contradiction
          · contradiction
        case h_36 => contradiction
      · intro ctx e A s h
        simp only [binder] at h
        split at h
        · rename_i T hT
          split at h
          · rename_i r hr
            split at h
            · rename_i ha
              cases h
              have ht := he ctx true A T hT
              rw [SortTag.ofTerm_sound hr] at ht
              exact .intro ht (binderOK_sound ha)
            · contradiction
          · contradiction
        · contradiction

theorem infer_sound {fuel : Nat} {ctx : Context} {ghost : Bool} {t T : Term}
    (h : infer fuel ctx ghost t = some T) : HasType ctx ghost t T :=
  (sound_mutual fuel).1 ctx ghost t T h

theorem binder_sound {fuel : Nat} {ctx : Context} {e : Bool} {A : Term} {s : SortTag}
    (h : binder fuel ctx e A = some s) : Binder ctx e A s :=
  (sound_mutual fuel).2 ctx e A s h

theorem check_sound {fuel : Nat} {ctx : Context} {ghost : Bool} {t T : Term}
    (h : check fuel ctx ghost t T = true) : HasType ctx ghost t T :=
by
  obtain ⟨actual, hi, conv⟩ := accepts_elim h
  exact .convert (infer_sound hi) conv

theorem sort_sound {fuel : Nat} {ctx : Context} {ty : Term} {s : SortTag}
    (h : sort fuel ctx ty = some s) : HasType ctx true ty s.term := by
  unfold sort at h
  cases hi : expose fuel (infer fuel ctx true ty) with
  | none => simp [hi] at h
  | some T =>
      simp only [hi, Option.bind_some] at h
      obtain ⟨actual, ha, conv⟩ := expose_elim hi
      have ht := (infer_sound ha).convert conv
      rw [SortTag.ofTerm_sound h] at ht
      exact ht

theorem isType_sound {fuel : Nat} {ctx : Context} {ty : Term}
    (h : isType fuel ctx ty = true) : ∃ s : SortTag, HasType ctx true ty s.term := by
  unfold isType at h
  cases hs : sort fuel ctx ty with
  | none => simp [hs] at h
  | some s => exact ⟨s, sort_sound hs⟩

end Jihoo.NativeKernel.Checker
