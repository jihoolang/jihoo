import Jihoo.NativeInversion
import Jihoo.NativeModeSafety
import Jihoo.NativeNormalization
import Jihoo.NativeConfluence

/-! Fixed-result-type ghost preservation for the executable normalizer's root
contractions. Every typing premise is an independent native-syntax derivation;
the conclusion is obtained through proved inversion/substitution/conversion. -/
namespace Jihoo.NativeKernel

/-- Contract a dependent beta redex whose function type may itself have been
converted. Pi injectivity is obtained from the proved Church–Rosser theorem. -/
theorem HasType.ghostBetaContract {Γ : Context} {mode e e' : Bool}
    {A A' body B' a : Term}
    (hf : HasType Γ mode (.lam e A body) (.pi e' A' B'))
    (ha : HasType Γ true a A') :
    HasType Γ true (body.subst (single a)) (B'.subst (single a)) := by
  obtain ⟨s,B,hA,hbody,hconv⟩ := hf.lamView
  obtain ⟨he,hdom,hcod⟩ := hconv.pi_injective
  exact (hbody.ghostInstantiate (ha.convert (.symm hdom))).convert
    (hcod.substitution (single a))

theorem HasType.ghostBeta {Γ : Context} {mode e : Bool} {A body a T : Term}
    (h : HasType Γ mode (.app (.lam e A body) a) T) :
    HasType Γ true (body.subst (single a)) T := by
  obtain ⟨e',A',B',hf,ha,allowed,hconv⟩ := h.appView
  exact (hf.ghostBetaContract ha.ghost).convert hconv

theorem HasType.ghostAdd {Γ : Context} {mode : Bool} {a b : Nat} {T : Term}
    (h : HasType Γ mode (.uadd (.natural a) (.natural b)) T) (bound : a+b < 2^64) :
    HasType Γ true (.natural (a+b)) T :=
  (HasType.natural bound).convert h.uaddView.2.2

theorem HasType.ghostSub {Γ : Context} {mode : Bool} {a b : Nat} {p T : Term}
    (h : HasType Γ mode (.usub (.natural a) (.natural b) p) T)
    (bound : a < 2^64) : HasType Γ true (.natural (a-b)) T :=
  (HasType.natural (Nat.lt_of_le_of_lt (Nat.sub_le a b) bound)).convert h.usubView.2.2.2

theorem HasType.ghostRead {Γ : Context} {mode : Bool} {count k : Nat}
    {xs : List Term} {p v T : Term}
    (h : HasType Γ mode (.index (.elements count xs) (.natural k) p) T)
    (selected : xs[k]? = some v) : HasType Γ true v T := by
  obtain ⟨n,ha,hi,hp,hconv⟩ := h.indexView
  have value := ha.elementsView.2.2.1 v (List.mem_of_getElem? selected)
  exact value.ghost.convert hconv

theorem HasType.ghostWitnessPack {Γ : Context} {mode : Bool} {p a q T : Term}
    (h : HasType Γ mode (.witness (.pack p a q)) T) : HasType Γ true a T := by
  obtain ⟨pred,packed,hconv⟩ := h.witnessView
  exact packed.packView.2.1.ghost.convert hconv

/-- Projection keeps the original predicate application, even when both the
refinement type and the final result type were independently converted. -/
theorem HasType.ghostProofPack {Γ : Context} {mode : Bool} {p a q T : Term}
    (h : HasType Γ mode (.proof (.pack p a q)) T) : HasType Γ true q T := by
  obtain ⟨pred,packed,hconv⟩ := h.proofView
  obtain ⟨hp,ha,hq,hpred⟩ := packed.packView
  have predicates := hpred.refine_injective
  have application : Conversion.Conv (.app p a) (.app pred (.witness (.pack p a q))) :=
    .node .app (.cons predicates (.cons (.symm (.witnessPack p a q)) .nil))
  exact hq.convert (.trans application hconv)


theorem HasType.ghostIfLtTrue {Γ : Context} {mode : Bool} {m n : Nat} {yes no T : Term}
    (h : HasType Γ mode (.ifLt (.natural m) (.natural n) yes no) T) (holds : m < n) :
    HasType Γ true (yes.subst (single (.decide (.natural m) (.natural n)))) T := by
  obtain ⟨B,ha,hb,hy,hn,hconv⟩ := h.ifLtView
  have evidence : HasType Γ true (.decide (.natural m) (.natural n)) (.lt (.natural m) (.natural n)) :=
    .decide ha.naturalView.1 hb.naturalView.1 holds
  have instantiated := hy.ghostInstantiate evidence
  rw [Term.shift_subst_single] at instantiated
  exact instantiated.convert hconv

theorem HasType.ghostIfLtFalse {Γ : Context} {mode : Bool} {a b yes no T : Term}
    (h : HasType Γ mode (.ifLt a b yes no) T) : HasType Γ true no T := by
  obtain ⟨B,ha,hb,hy,hn,hconv⟩ := h.ifLtView
  exact hn.ghost.convert hconv

theorem HasType.ghostIfEqTrue {Γ : Context} {mode : Bool} {m n : Nat} {yes no T : Term}
    (h : HasType Γ mode (.ifEq (.natural m) (.natural n) yes no) T) (holds : m = n) :
    HasType Γ true (yes.subst (single (.refl (.natural m)))) T := by
  subst n
  obtain ⟨B,ha,hb,hy,hn,hconv⟩ := h.ifEqView
  have evidence : HasType Γ true (.refl (.natural m)) (.eq (.natural m) (.natural m)) :=
    .refl (.natural ha.naturalView.1)
  have instantiated := hy.ghostInstantiate evidence
  rw [Term.shift_subst_single] at instantiated
  exact instantiated.convert hconv

theorem HasType.ghostIfEqFalse {Γ : Context} {mode : Bool} {a b yes no T : Term}
    (h : HasType Γ mode (.ifEq a b yes no) T) : HasType Γ true no T := by
  obtain ⟨B,ha,hb,hy,hn,hconv⟩ := h.ifEqView
  exact hn.ghost.convert hconv



/-- Equality conversion cannot change a reflexivity proof into unequal indices:
real Eq injectivity supplies conversion between the predicate arguments. -/
theorem HasType.ghostTransportRefl {Γ : Context} {mode : Bool} {f a p T : Term}
    (h : HasType Γ mode (.transport f (.refl a) p) T) : HasType Γ true p T := by
  obtain ⟨u,v,hf,he,hp,hconv⟩ := h.transportView
  obtain ⟨au,av⟩ := he.reflView.2.eq_injective
  have uv : Conversion.Conv u v := .trans (.symm au) av
  have application : Conversion.Conv (.app f u) (.app f v) :=
    .node .app (.cons (.refl _) (.cons uv .nil))
  exact hp.convert (.trans application hconv)

namespace Conversion

/-- Every contraction actually returned by the executable full-syntax
normalizer preserves an independently derived original type in ghost mode. -/
theorem contract_ghost_preservation {Γ : Context} {mode : Bool} {t u T : Term}
    (typed : HasType Γ mode t T) (h : contract t = some u) : HasType Γ true u T := by
  fun_cases contract t <;> simp_all [contract]
  all_goals try (split at h <;> simp_all <;> try (exact False.elim (by omega)))
  all_goals try (rcases h with ⟨hbound,h⟩)
  all_goals try subst u
  all_goals first
    | exact typed.ghostBeta
    | exact typed.ghostAdd (by omega)
    | exact typed.ghostSub (by omega)
    | exact typed.ghostRead (by assumption)
    | exact typed.ghostWitnessPack
    | exact typed.ghostProofPack
    | exact typed.ghostIfLtTrue (by omega)
    | exact typed.ghostIfLtFalse
    | exact typed.ghostIfEqTrue (by omega)
    | exact typed.ghostIfEqFalse
    | exact typed.ghostTransportRefl
    | exact False.elim typed.deref_unavailable
    | exact False.elim typed.borrow_unavailable

end Conversion

end Jihoo.NativeKernel
