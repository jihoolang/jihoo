import Jihoo.NativeContextConversion

/-! Outer-rule inversion for the native typing judgment. These views strip an
arbitrary number of result-type conversions, while retaining independently
derived premises and an explicit conversion from the principal result type. -/
namespace Jihoo.NativeKernel

private def TypingView (Γ : Context) (mode : Bool) : Term → Term → Prop
  | .lam e A body, T => ∃ s B, Binder Γ e A s ∧ HasType (⟨A,e⟩ :: Γ) mode body B ∧
      Conversion.Conv (.pi e A B) T
  | .app f a, T => ∃ e A B, HasType Γ mode f (.pi e A B) ∧ HasType Γ (mode || e) a A ∧
      applicationAllowed mode A a ∧ Conversion.Conv (B.subst (single a)) T
  | .elements n xs, T => xs.length = n ∧ xs.length < 2^64 ∧
      (∀ x ∈ xs, HasType Γ mode x .i64) ∧ Conversion.Conv (.array (.natural xs.length)) T
  | .index a i p, T => ∃ n, HasType Γ mode a (.array n) ∧ HasType Γ mode i .u64 ∧
      HasType Γ true p (.lt i n) ∧ Conversion.Conv .i64 T
  | .pack p a q, T => HasType Γ true p (.pi false .u64 .prop) ∧ HasType Γ mode a .u64 ∧
      HasType Γ true q (.app p a) ∧ Conversion.Conv (.refine p) T
  | .witness s, T => ∃ p, HasType Γ mode s (.refine p) ∧ Conversion.Conv .u64 T
  | .proof s, T => ∃ p, HasType Γ true s (.refine p) ∧ Conversion.Conv (.app p (.witness s)) T
  | .uadd a b, T => HasType Γ mode a .u64 ∧ HasType Γ mode b .u64 ∧ Conversion.Conv .u64 T
  | .usub a b p, T => HasType Γ mode a .u64 ∧ HasType Γ mode b .u64 ∧
      HasType Γ true p (.lt b (.uadd a (.natural 1))) ∧ Conversion.Conv .u64 T
  | .refl a, T => HasType Γ true a .u64 ∧ Conversion.Conv (.eq a a) T
  | .natural n, T => n < 2^64 ∧ Conversion.Conv .u64 T
  | .integer n, T => -(2^63 : Int) ≤ n ∧ n < (2^63 : Int) ∧ Conversion.Conv .i64 T
  | .pi e A B, T => ∃ s r, Binder Γ e A s ∧ HasType (⟨A,e⟩ :: Γ) true B r.term ∧
      Conversion.Conv (s.pi r).term T
  | .node .deref _, _ | .node .borrow _, _ => False
  | _, _ => True

private theorem TypingView.convert {Γ : Context} {mode : Bool} {t A B : Term}
    (h : TypingView Γ mode t A) (hc : Conversion.Conv A B) : TypingView Γ mode t B := by
  fun_cases TypingView Γ mode t A <;> simp only [TypingView] at h ⊢
  all_goals first
    | (obtain ⟨s,C,hA,hbody,hconv⟩ := h; exact ⟨s,C,hA,hbody,.trans hconv hc⟩)
    | (obtain ⟨e,C,D,hf,ha,allowed,hconv⟩ := h; exact ⟨e,C,D,hf,ha,allowed,.trans hconv hc⟩)
    | (obtain ⟨h₁,h₂,h₃,hconv⟩ := h; exact ⟨h₁,h₂,h₃,.trans hconv hc⟩)
    | (obtain ⟨n,h₁,h₂,h₃,hconv⟩ := h; exact ⟨n,h₁,h₂,h₃,.trans hconv hc⟩)
    | (obtain ⟨p,hs,hconv⟩ := h; exact ⟨p,hs,.trans hconv hc⟩)
    | (obtain ⟨h₁,h₂,hconv⟩ := h; exact ⟨h₁,h₂,.trans hconv hc⟩)
    | (obtain ⟨h₁,hconv⟩ := h; exact ⟨h₁,.trans hconv hc⟩)
    | exact False.elim h
    | trivial

private theorem HasType.typingView {Γ : Context} {mode : Bool} {t T : Term}
    (h : HasType Γ mode t T) : TypingView Γ mode t T := by
  induction h using HasType.rec (motive_1 := fun _ _ _ _ _ => True)
  all_goals first | trivial | skip
  case pi hA hB _ _ => exact ⟨_,_,hA,hB,.refl _⟩
  case lam hA hb _ _ => exact ⟨_,_,hA,hb,.refl _⟩
  case app hf ha allowed _ _ => exact ⟨_,_,_,hf,ha,allowed,.refl _⟩
  case elements hn hb hs _ => exact ⟨hn,hb,hs,.refl _⟩
  case index ha hi hp _ _ _ => exact ⟨_,ha,hi,hp,.refl _⟩
  case pack hp ha hq _ _ _ => exact ⟨hp,ha,hq,.refl _⟩
  case witness hs _ => exact ⟨_,hs,.refl _⟩
  case proof hs _ => exact ⟨_,hs,.refl _⟩
  case uadd ha hb _ _ => exact ⟨ha,hb,.refl _⟩
  case usub ha hb hp _ _ _ => exact ⟨ha,hb,hp,.refl _⟩
  case refl ha _ => exact ⟨ha,.refl _⟩
  case natural bound => exact ⟨bound,.refl _⟩
  case integer lo hi => exact ⟨lo,hi,.refl _⟩
  case convert ht hc ih => exact ih.convert hc

theorem HasType.lamView {Γ : Context} {mode e : Bool} {A body T : Term}
    (h : HasType Γ mode (.lam e A body) T) :
    ∃ s B, Binder Γ e A s ∧ HasType (⟨A,e⟩ :: Γ) mode body B ∧ Conversion.Conv (.pi e A B) T :=
  h.typingView

theorem HasType.appView {Γ : Context} {mode : Bool} {f a T : Term}
    (h : HasType Γ mode (.app f a) T) :
    ∃ e A B, HasType Γ mode f (.pi e A B) ∧ HasType Γ (mode || e) a A ∧
      applicationAllowed mode A a ∧ Conversion.Conv (B.subst (single a)) T := h.typingView

theorem HasType.elementsView {Γ : Context} {mode : Bool} {n : Nat} {xs : List Term} {T : Term}
    (h : HasType Γ mode (.elements n xs) T) :
    xs.length = n ∧ xs.length < 2^64 ∧ (∀ x ∈ xs, HasType Γ mode x .i64) ∧
      Conversion.Conv (.array (.natural xs.length)) T := h.typingView

theorem HasType.indexView {Γ : Context} {mode : Bool} {a i p T : Term}
    (h : HasType Γ mode (.index a i p) T) :
    ∃ n, HasType Γ mode a (.array n) ∧ HasType Γ mode i .u64 ∧
      HasType Γ true p (.lt i n) ∧ Conversion.Conv .i64 T := h.typingView

theorem HasType.packView {Γ : Context} {mode : Bool} {p a q T : Term}
    (h : HasType Γ mode (.pack p a q) T) :
    HasType Γ true p (.pi false .u64 .prop) ∧ HasType Γ mode a .u64 ∧
      HasType Γ true q (.app p a) ∧ Conversion.Conv (.refine p) T := h.typingView

theorem HasType.witnessView {Γ : Context} {mode : Bool} {s T : Term}
    (h : HasType Γ mode (.witness s) T) :
    ∃ p, HasType Γ mode s (.refine p) ∧ Conversion.Conv .u64 T := h.typingView

theorem HasType.proofView {Γ : Context} {mode : Bool} {s T : Term}
    (h : HasType Γ mode (.proof s) T) :
    ∃ p, HasType Γ true s (.refine p) ∧ Conversion.Conv (.app p (.witness s)) T := h.typingView

theorem HasType.uaddView {Γ : Context} {mode : Bool} {a b T : Term}
    (h : HasType Γ mode (.uadd a b) T) :
    HasType Γ mode a .u64 ∧ HasType Γ mode b .u64 ∧ Conversion.Conv .u64 T := h.typingView

theorem HasType.usubView {Γ : Context} {mode : Bool} {a b p T : Term}
    (h : HasType Γ mode (.usub a b p) T) :
    HasType Γ mode a .u64 ∧ HasType Γ mode b .u64 ∧
      HasType Γ true p (.lt b (.uadd a (.natural 1))) ∧ Conversion.Conv .u64 T := h.typingView

theorem HasType.reflView {Γ : Context} {mode : Bool} {a T : Term}
    (h : HasType Γ mode (.refl a) T) :
    HasType Γ true a .u64 ∧ Conversion.Conv (.eq a a) T := h.typingView

theorem HasType.naturalView {Γ : Context} {mode : Bool} {n : Nat} {T : Term}
    (h : HasType Γ mode (.natural n) T) : n < 2^64 ∧ Conversion.Conv .u64 T := h.typingView

theorem HasType.integerView {Γ : Context} {mode : Bool} {n : Int} {T : Term}
    (h : HasType Γ mode (.integer n) T) :
    -(2^63 : Int) ≤ n ∧ n < (2^63 : Int) ∧ Conversion.Conv .i64 T := h.typingView

theorem HasType.piView {Γ : Context} {mode e : Bool} {A B T : Term}
    (h : HasType Γ mode (.pi e A B) T) :
    ∃ s r, Binder Γ e A s ∧ HasType (⟨A,e⟩ :: Γ) true B r.term ∧
      Conversion.Conv (s.pi r).term T := h.typingView

theorem HasType.deref_unavailable {Γ : Context} {mode : Bool} {args : List Term} {T : Term}
    (h : HasType Γ mode (.node .deref args) T) : False := h.typingView

theorem HasType.borrow_unavailable {Γ : Context} {mode : Bool} {args : List Term} {T : Term}
    (h : HasType Γ mode (.node .borrow args) T) : False := h.typingView

end Jihoo.NativeKernel
