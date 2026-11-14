import Jihoo.NativeEnvironmentTypeUniqueness
import Jihoo.NativeEnvironmentContextConversion

/-! Original-type ghost preservation for the actual ACU computational roots.
Environment closure is used by dependent beta and evidence instantiation. -/
namespace Jihoo.NativeKernel.Environment
/-- Contract a dependent beta redex whose function type may itself have been
converted. Pi injectivity is obtained from the proved Church–Rosser theorem. -/
theorem HasType.ghostBetaContract {Γ : Context} {mode e e' : Bool}
    {A A' body B' a : Term}
    (wf : UnifiedProgram.EnvWellFormed env)
    (hf : HasType env Γ mode (.lam e A body) (.pi e' A' B'))
    (ha : HasType env Γ true a A') :
    HasType env Γ true (body.subst (single a)) (B'.subst (single a)) := by
  obtain ⟨s,B,hA,hbody,hconv⟩ := hf.lamView
  obtain ⟨he,hdom,hcod⟩ := hconv.pi_injective wf.admissible
  exact (hbody.ghostInstantiate wf (ha.convert (.symm hdom))).convert
    (hcod.substitution (single a) wf.closed)

theorem HasType.ghostBeta {Γ : Context} {mode e : Bool} {A body a T : Term}
    (wf : UnifiedProgram.EnvWellFormed env)
    (h : HasType env Γ mode (.app (.lam e A body) a) T) :
    HasType env Γ true (body.subst (single a)) T := by
  obtain ⟨e',A',B',hf,ha,allowed,hconv⟩ := h.appView
  exact (hf.ghostBetaContract wf ha.ghost).convert hconv

theorem HasType.ghostAdd {Γ : Context} {mode : Bool} {a b : Nat} {T : Term}
    (h : HasType env Γ mode (.uadd (.natural a) (.natural b)) T) (bound : a+b < 2^64) :
    HasType env Γ true (.natural (a+b)) T :=
  (HasType.natural bound).convert h.uaddView.2.2

theorem HasType.ghostSub {Γ : Context} {mode : Bool} {a b : Nat} {p T : Term}
    (h : HasType env Γ mode (.usub (.natural a) (.natural b) p) T)
    (bound : a < 2^64) : HasType env Γ true (.natural (a-b)) T :=
  (HasType.natural (Nat.lt_of_le_of_lt (Nat.sub_le a b) bound)).convert h.usubView.2.2.2

theorem HasType.ghostRead {Γ : Context} {mode : Bool} {count k : Nat}
    {xs : List Term} {p v T : Term}
    (wf : UnifiedProgram.EnvWellFormed env)
    (h : HasType env Γ mode (.index (.elements count xs) (.natural k) p) T)
    (selected : xs[k]? = some v) : HasType env Γ true v T := by
  obtain ⟨n,ha,hi,hp,hconv⟩ := h.indexView
  rcases ha with ha | ha
  · have value := ha.elementsView.2.2.1 v (List.mem_of_getElem? selected)
    exact value.ghost.convert hconv
  · have impossible := ha.principalView
    exact False.elim (EnvironmentDelta.Basis.Conv.full_rigid_disjoint (op := .array) (op' := .ref)
      rfl rfl (by intro same; cases same) impossible wf.admissible)

theorem HasType.ghostWitnessPack {Γ : Context} {mode : Bool} {p a q T : Term}
    (h : HasType env Γ mode (.witness (.pack p a q)) T) : HasType env Γ true a T := by
  obtain ⟨pred,packed,hconv⟩ := h.witnessView
  exact packed.packView.2.1.ghost.convert hconv

/-- Projection keeps the original predicate application, even when both the
refinement type and the final result type were independently converted. -/
theorem HasType.ghostProofPack {Γ : Context} {mode : Bool} {p a q T : Term}
    (wf : UnifiedProgram.EnvWellFormed env)
    (h : HasType env Γ mode (.proof (.pack p a q)) T) : HasType env Γ true q T := by
  obtain ⟨pred,packed,hconv⟩ := h.proofView
  obtain ⟨hp,ha,hq,hpred⟩ := packed.packView
  have predicates := hpred.refine_injective wf.admissible
  have application : Conversion.Conv env (.app p a) (.app pred (.witness (.pack p a q))) :=
    .node .app (.cons predicates (.cons (.symm (.legacy (.witnessPack p a q))) .nil))
  exact hq.convert (.trans application hconv)


theorem HasType.ghostIfLtTrue {Γ : Context} {mode : Bool} {m n : Nat} {yes no T : Term}
    (wf : UnifiedProgram.EnvWellFormed env)
    (h : HasType env Γ mode (.ifLt (.natural m) (.natural n) yes no) T) (holds : m < n) :
    HasType env Γ true (yes.subst (single (.decide (.natural m) (.natural n)))) T := by
  obtain ⟨B,ha,hb,hy,hn,hconv⟩ := h.ifLtView
  have evidence : HasType env Γ true (.decide (.natural m) (.natural n)) (.lt (.natural m) (.natural n)) :=
    .decide ha.naturalView.1 hb.naturalView.1 holds
  have instantiated := hy.ghostInstantiate wf evidence
  rw [Term.shift_subst_single] at instantiated
  exact instantiated.convert hconv

theorem HasType.ghostIfLtFalse {Γ : Context} {mode : Bool} {a b yes no T : Term}
    (h : HasType env Γ mode (.ifLt a b yes no) T) : HasType env Γ true no T := by
  obtain ⟨B,ha,hb,hy,hn,hconv⟩ := h.ifLtView
  exact hn.ghost.convert hconv

theorem HasType.ghostIfEqTrue {Γ : Context} {mode : Bool} {m n : Nat} {yes no T : Term}
    (wf : UnifiedProgram.EnvWellFormed env)
    (h : HasType env Γ mode (.ifEq (.natural m) (.natural n) yes no) T) (holds : m = n) :
    HasType env Γ true (yes.subst (single (.refl (.natural m)))) T := by
  subst n
  obtain ⟨B,ha,hb,hy,hn,hconv⟩ := h.ifEqView
  have evidence : HasType env Γ true (.refl (.natural m)) (.eq (.natural m) (.natural m)) :=
    .refl (.natural ha.naturalView.1)
  have instantiated := hy.ghostInstantiate wf evidence
  rw [Term.shift_subst_single] at instantiated
  exact instantiated.convert hconv

theorem HasType.ghostIfEqFalse {Γ : Context} {mode : Bool} {a b yes no T : Term}
    (h : HasType env Γ mode (.ifEq a b yes no) T) : HasType env Γ true no T := by
  obtain ⟨B,ha,hb,hy,hn,hconv⟩ := h.ifEqView
  exact hn.ghost.convert hconv



/-- Equality conversion cannot change a reflexivity proof into unequal indices:
real Eq injectivity supplies conversion between the predicate arguments. -/
theorem HasType.ghostTransportRefl {Γ : Context} {mode : Bool} {f a p T : Term}
    (wf : UnifiedProgram.EnvWellFormed env)
    (h : HasType env Γ mode (.transport f (.refl a) p) T) : HasType env Γ true p T := by
  obtain ⟨u,v,hf,he,hp,hconv⟩ := h.transportView
  obtain ⟨au,av⟩ := he.reflView.2.eq_injective wf.admissible
  have uv : Conversion.Conv env u v := .trans (.symm au) av
  have application : Conversion.Conv env (.app f u) (.app f v) :=
    .node .app (.cons (.refl _) (.cons uv .nil))
  exact hp.convert (.trans application hconv)


theorem HasType.ghostDerefBorrow (wf : UnifiedProgram.EnvWellFormed env) (h : HasType env Γ mode (.deref (.borrow a)) T) :
    HasType env Γ true a T := by
  obtain ⟨n,borrowed,hc⟩ := h.derefView
  obtain ⟨m,original,hd⟩ := borrowed.borrowView
  exact original.convert (.trans (ref_injective wf hd) hc)

theorem HasType.ghostBorrowDeref (h : HasType env Γ mode (.borrow (.deref a)) T) :
    HasType env Γ true a T := by
  obtain ⟨n,dereferenced,hc⟩ := h.borrowView
  obtain ⟨m,original,hd⟩ := dereferenced.derefView
  exact original.convert (.trans (.node .ref (.cons hd .nil)) hc)

theorem compute_ghost_preservation (wf : UnifiedProgram.EnvWellFormed env)
    (step : ACU.Computes t u) (typed : HasType env Γ mode t T) : HasType env Γ true u T := by
  cases step with
  | beta => exact typed.ghostBeta wf
  | sub a b p lower upper => exact typed.ghostSub upper
  | read count xs k p v selected => exact typed.ghostRead wf selected
  | witnessPack => exact typed.ghostWitnessPack
  | proofPack => exact typed.ghostProofPack wf
  | derefBorrow => exact typed.ghostDerefBorrow wf
  | borrowDeref => exact typed.ghostBorrowDeref
  | transportRefl => exact typed.ghostTransportRefl wf
  | ifLtTrue m n yes no holds => exact typed.ghostIfLtTrue wf holds
  | ifLtFalse => exact typed.ghostIfLtFalse
  | ifEqTrue => exact typed.ghostIfEqTrue wf rfl
  | ifEqFalse => exact typed.ghostIfEqFalse

theorem HasType.ghostAddAssocRight
    (h : HasType env Γ mode (.uadd (.uadd a b) c) T) :
    HasType env Γ true (.uadd a (.uadd b c)) T := by
  obtain ⟨left,right,hc⟩ := h.uaddView
  obtain ⟨aType,bType,_⟩ := left.uaddView
  exact (HasType.uadd aType.ghost (.uadd bType.ghost right.ghost)).convert hc

theorem HasType.ghostAddAssocLeft
    (h : HasType env Γ mode (.uadd a (.uadd b c)) T) :
    HasType env Γ true (.uadd (.uadd a b) c) T := by
  obtain ⟨left,right,hc⟩ := h.uaddView
  obtain ⟨bType,cType,_⟩ := right.uaddView
  exact (HasType.uadd (.uadd left.ghost bType.ghost) cType.ghost).convert hc

theorem HasType.ghostAddComm (h : HasType env Γ mode (.uadd a b) T) :
    HasType env Γ true (.uadd b a) T := by
  obtain ⟨left,right,hc⟩ := h.uaddView
  exact (HasType.uadd right.ghost left.ghost).convert hc

theorem HasType.ghostAddZeroRight (h : HasType env Γ mode (.uadd a (.natural 0)) T) :
    HasType env Γ true a T := h.uaddView.1.ghost.convert h.uaddView.2.2

theorem HasType.ghostAddZeroLeft (h : HasType env Γ mode (.uadd (.natural 0) a) T) :
    HasType env Γ true a T := h.uaddView.2.1.ghost.convert h.uaddView.2.2

theorem compact_typed (elements : ∀ x ∈ xs, HasType env Γ true x .u64) :
    HasType env Γ true (ACU.compact xs) .u64 := by
  induction xs with
  | nil => exact .natural (by decide)
  | cons x xs ih =>
    cases xs with
    | nil => exact elements x (by simp)
    | cons y ys =>
      exact .uadd (elements x (by simp)) (ih (by intros z hz; exact elements z (by simp [hz])))

theorem HasType.ghostLiteralSplit (h : HasType env Γ mode (.natural n) T) :
    HasType env Γ true (ACU.compact (List.replicate n (.natural 1))) T := by
  apply (compact_typed ?_).convert h.naturalView.2
  intro x hx
  have same := List.eq_of_mem_replicate hx
  subst x
  exact .natural (by decide)

end Jihoo.NativeKernel.Environment
