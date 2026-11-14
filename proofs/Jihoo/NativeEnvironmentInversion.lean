import Jihoo.NativeEnvironmentGhostMetatheory
import Jihoo.NativeEnvironmentCheckerSoundness

/-! Principal-type inversion for the same unified environment judgment.
The view retains actual derivations and full ACU conversion evidence. -/
namespace Jihoo.NativeKernel.Environment
open Jihoo.NativeKernel.Environment.Conversion

/-- Both proposition and data elimination compute their actual principal
result from the same independently typed scrutinee indices. -/
def eliminationResult (entry : CheckedFamily) (motive : Term) (indices : List Term) (scrutinee : Term) : Term :=
  if entry.declaration.data then .app (applications motive (indices.drop entry.declaration.params)) scrutinee
  else applications motive indices

def PrincipalView (env : Environment) (Γ : Context) (mode : Bool) : Term → Term → Prop
  | .var x, T => ∃ b, lookup Γ x = some b ∧ Conv b.ty T
  | .univ n, T => Conv (.univ (n+1)) T
  | .prop, T | .u64, T | .i64, T | .array _, T | .refine _, T => Conv (.univ 0) T
  | .lt _ _, T | .eq _ _, T => Conv .prop T
  | .natural _, T | .uadd _ _, T | .usub _ _ _, T | .witness _, T => Conv .u64 T
  | .integer _, T | .index _ _ _, T | .arith _ _ _, T => Conv .i64 T
  | .elements _ xs, T => Conv (.array (.natural xs.length)) T
  | .decide a b, T => Conv (.lt a b) T
  | .refl a, T => Conv (.eq a a) T
  | .zeroLe a, T => Conv (.lt (.natural 0) (.uadd a (.natural 1))) T
  | .ltAdd a b c _, T => Conv (.lt (.uadd a c) (.uadd b c)) T
  | .ltCancel a b _ _, T => Conv (.lt a b) T
  | .ltLe a _ c _ _, T => Conv (.lt a c) T
  | .pack p _ _, T => Conv (.refine p) T
  | .pi e A B, T => ∃ s r : SortTag,
      HasType env Γ true A s.term ∧ HasType env (⟨A,e⟩ :: Γ) true B r.term ∧ Conv (s.pi r).term T
  | .lam e A body, T => ∃ B, HasType env (⟨A,e⟩ :: Γ) mode body B ∧ Conv (.pi e A B) T
  | .app f a, T => ∃ e A B, HasType env Γ mode f (.pi e A B) ∧ Conv (B.subst (single a)) T
  | .strict _ b, T => ∃ B, HasType env Γ mode b B ∧ Conv B T
  | .transport f e _, T => ∃ a b, HasType env Γ true e (.eq a b) ∧ Conv (.app f b) T
  | .proof s, T => ∃ p, HasType env Γ true s (.refine p) ∧ Conv (.app p (.witness s)) T
  | .ifLt _ _ _ no, T | .ifEq _ _ _ no, T => ∃ B, HasType env Γ mode no B ∧ Conv B T
  | .absurd U _, T => Conv U T
  | .fold _ init _, T => ∃ A, HasType env Γ mode init A ∧ Conv A T
  | .loop n motive _ _, T => Conv (.app motive n) T
  | .node (.global g) [], T => ∃ declaration, env.globals[g]? = some declaration ∧
      Conv (declaration.type.rename (fun x => x + Γ.length)) T
  | .node (.ind f _) _, T => ∃ entry, env.families[f]? = some entry ∧
      Conv (if entry.declaration.data then .univ 0 else .prop) T
  | .node (.con f k _) xs, T => ∃ entry signature arity indices,
      env.families[f]? = some entry ∧ entry.signatures[k]? = some signature ∧
      Arguments env Γ mode entry.declaration.data
        ((signatureTerm f signature).rename (fun x => x + Γ.length)) xs
        (.node (.ind f arity) indices) ∧ Conv (.node (.ind f arity) indices) T
  | .node (.elim f count) args, T => ∃ entry motive branches scrutinee indices scrutineeMode,
      env.families[f]? = some entry ∧ count = branches.length ∧
      args = motive :: (branches ++ [scrutinee]) ∧
      HasType env Γ scrutineeMode scrutinee (.node (.ind f entry.declaration.arity) indices) ∧
      Conv (eliminationResult entry motive indices scrutinee) T
  | .buffer _, T | .ref _, T | .back _ _ _, T => Conv (.univ 0) T
  | .alloc n _, T => Conv (.buffer n) T
  | .store b _ _ _, T => ∃ n, HasType env Γ mode b (.buffer n) ∧ Conv (.buffer n) T
  | .free _ rest, T => ∃ R, HasType env Γ mode rest R ∧ Conv R T
  | .borrow b, T => ∃ R, HasType env Γ true b R ∧ Conv (.ref R) T
  | .deref r, T => ∃ R, HasType env Γ true r (.ref R) ∧ Conv R T
  | .give e motive owner _, T => ∃ R, HasType env Γ mode owner R ∧ Conv (.back e R motive) T
  | .load _ _ _ continuation, T | .take _ continuation, T =>
      ∃ A e B C normal outside,
      HasType env Γ mode continuation (.pi false A (.pi e B C)) ∧
      Conv C normal ∧ PartialRenaming.shift (-2) 0 normal = some outside ∧ Conv outside T
  | .node (.caseOf f count) args, T => ∃ entry motive branches scrutinee indices scrutineeMode,
      env.families[f]? = some entry ∧ count = branches.length ∧
      args = motive :: (branches ++ [scrutinee]) ∧
      HasType env Γ scrutineeMode scrutinee (.node (.ind f entry.declaration.arity) indices) ∧
      Conv (eliminationResult entry motive indices scrutinee) T
  | .node (.drop _) [_,rest], T => ∃ R, HasType env Γ mode rest R ∧ Conv R T
  | _, _ => False

theorem PrincipalView.convert (h : PrincipalView env Γ mode t A) (hc : Conv A B) :
    PrincipalView env Γ mode t B := by
  fun_cases PrincipalView env Γ mode t A <;> simp only [PrincipalView] at h ⊢
  all_goals first
    | exact False.elim h
    | exact .trans h hc
    | (obtain ⟨a,b,c,d,e,f,g,h,i,j,k⟩ := h; exact ⟨a,b,c,d,e,f,g,h,i,j,.trans k hc⟩)
    | (obtain ⟨a,b,c,d,e,f,g,h,i,j⟩ := h; exact ⟨a,b,c,d,e,f,g,h,i,.trans j hc⟩)
    | (obtain ⟨a,b,c,d,e,f,g,h,i⟩ := h; exact ⟨a,b,c,d,e,f,g,h,.trans i hc⟩)
    | (obtain ⟨a,b,c,d,e,f,g,h⟩ := h; exact ⟨a,b,c,d,e,f,g,.trans h hc⟩)
    | (obtain ⟨a,b,c,d,e,f,g⟩ := h; exact ⟨a,b,c,d,e,f,.trans g hc⟩)
    | (obtain ⟨a,b,c,d,e,f⟩ := h; exact ⟨a,b,c,d,e,.trans f hc⟩)
    | (obtain ⟨a,b,c,d,e⟩ := h; exact ⟨a,b,c,d,.trans e hc⟩)
    | (obtain ⟨a,b,c,d⟩ := h; exact ⟨a,b,c,.trans d hc⟩)
    | (obtain ⟨a,b,c⟩ := h; exact ⟨a,b,.trans c hc⟩)

theorem HasType.principalView (h : HasType env Γ mode t T) : PrincipalView env Γ mode t T := by
  apply HasType.rec (t := h) (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun ctx ghost term type _ => PrincipalView env ctx ghost term type)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ _ => True) (motive_5 := fun _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | exact ACU.Conv.refl _ | skip
  case var hx readable => exact ⟨_, hx, .refl _⟩
  case pi hA hB _ _ =>
    cases hA with
    | intro typed allowed => exact ⟨_,_,typed,hB,.refl _⟩
  case lam hA hb _ _ => exact ⟨_,hb,.refl _⟩
  case app hf ha allowed _ _ => exact ⟨_,_,_,hf,.refl _⟩
  case strict ha hb _ _ => exact ⟨_,hb,.refl _⟩
  case transport hf he hp _ _ _ => exact ⟨_,_,he,.refl _⟩
  case proof hs _ => exact ⟨_,hs,.refl _⟩
  case ifLt ha hb hy hn _ _ _ _ => exact ⟨_,hn,.refl _⟩
  case ifEq ha hb hy hn _ _ _ _ => exact ⟨_,hn,.refl _⟩
  case convert ht conv ih => exact ih.convert conv

  case foldI64 n init body allowed _ _ _ => exact ⟨_,init,.refl _⟩
  case global found => exact ⟨_,found,.refl _⟩
  case ind found arity size typed ih => exact ⟨_,found,.refl _⟩
  case con found sigFound size typed ih => exact ⟨_,_,_,_,found,sigFound,typed,.refl _⟩
  case propElim found prop motive branches scrutinee _ _ _ =>
    exact ⟨_,_,_,_,_,_,found,rfl,rfl,scrutinee,by simpa only [eliminationResult,prop,Bool.false_eq_true,↓reduceIte] using ACU.Conv.refl _⟩
  case foldOwned count init owned body allowed _ _ _ => exact ⟨_,init,.refl _⟩
  case ghostBorrowOwned owner owned _ => exact ⟨_,owner,.refl _⟩
  case ghostDerefOwned reference _ => exact ⟨_,reference,.refl _⟩
  case drop found boxed owner rest _ _ => exact ⟨_,rest,.refl _⟩
  case dataElim found isData boxed size motive scrutinee generated branches allowed ihm ihs ihb =>
    rename_i family entry analysis ctx motiveTerm proof ghost scrutineeTerm indices types caseTerms
    cases analysis <;>
      exact ⟨_,_,_,_,_,_,found,rfl,rfl,scrutinee,by simpa only [eliminationResult,isData,↓reduceIte] using ACU.Conv.refl _⟩
  case store buffer index value proof _ _ _ _ => exact ⟨_,buffer,.refl _⟩
  case load buffer index proof continuation value owner result lowered allowed _ _ _ _ =>
    exact ⟨_,_,_,_,_,_,continuation,result,lowered,.refl _⟩
  case free buffer rest _ _ => exact ⟨_,rest,.refl _⟩
  case ghostBorrow buffer _ => exact ⟨_,buffer,.refl _⟩
  case ghostDeref reference _ => exact ⟨_,reference,.refl _⟩
  case give owner owned motive repr result _ _ _ => exact ⟨_,owner,.refl _⟩
  case take value continuation owner result normalized lowered allowed _ _ =>
    exact ⟨_,_,_,_,_,_,continuation,normalized,lowered,.refl _⟩

def TypingView (env : Environment) (Γ : Context) (mode : Bool) : Term → Term → Prop
  | .lam e A body, T => ∃ s B, Binder env Γ e A s ∧ HasType env (⟨A,e⟩ :: Γ) mode body B ∧
      Conversion.Conv (.pi e A B) T
  | .app f a, T => ∃ e A B, HasType env Γ mode f (.pi e A B) ∧ HasType env Γ (mode || e) a A ∧
      applicationAllowed env mode A a ∧ Conversion.Conv (B.subst (single a)) T
  | .elements n xs, T => xs.length = n ∧ xs.length < 2^64 ∧
      (∀ x ∈ xs, HasType env Γ mode x .i64) ∧ Conversion.Conv (.array (.natural xs.length)) T
  | .index a i p, T => ∃ n, (HasType env Γ mode a (.array n) ∨ HasType env Γ mode a (.ref (.buffer n))) ∧ HasType env Γ mode i .u64 ∧
      HasType env Γ true p (.lt i n) ∧ Conversion.Conv .i64 T
  | .pack p a q, T => HasType env Γ true p (.pi false .u64 .prop) ∧ HasType env Γ mode a .u64 ∧
      HasType env Γ true q (.app p a) ∧ Conversion.Conv (.refine p) T
  | .witness s, T => ∃ p, HasType env Γ mode s (.refine p) ∧ Conversion.Conv .u64 T
  | .proof s, T => ∃ p, HasType env Γ true s (.refine p) ∧ Conversion.Conv (.app p (.witness s)) T
  | .uadd a b, T => HasType env Γ mode a .u64 ∧ HasType env Γ mode b .u64 ∧ Conversion.Conv .u64 T
  | .usub a b p, T => HasType env Γ mode a .u64 ∧ HasType env Γ mode b .u64 ∧
      HasType env Γ true p (.lt b (.uadd a (.natural 1))) ∧ Conversion.Conv .u64 T
  | .refl a, T => HasType env Γ true a .u64 ∧ Conversion.Conv (.eq a a) T
  | .natural n, T => n < 2^64 ∧ Conversion.Conv .u64 T
  | .integer n, T => -(2^63 : Int) ≤ n ∧ n < (2^63 : Int) ∧ Conversion.Conv .i64 T
  | .pi e A B, T => ∃ s r, Binder env Γ e A s ∧ HasType env (⟨A,e⟩ :: Γ) true B r.term ∧
      Conversion.Conv (s.pi r).term T
  | .transport f e p, T => ∃ a b, HasType env Γ true f (.pi false .u64 .prop) ∧
      HasType env Γ true e (.eq a b) ∧ HasType env Γ true p (.app f a) ∧ Conversion.Conv (.app f b) T
  | .ifLt a b yes no, T => ∃ B, HasType env Γ mode a .u64 ∧ HasType env Γ mode b .u64 ∧
      HasType env (⟨.lt a b,true⟩ :: Γ) mode yes (B.rename Nat.succ) ∧ HasType env Γ mode no B ∧ Conversion.Conv B T
  | .ifEq a b yes no, T => ∃ B, HasType env Γ mode a .u64 ∧ HasType env Γ mode b .u64 ∧
      HasType env (⟨.eq a b,true⟩ :: Γ) mode yes (B.rename Nat.succ) ∧ HasType env Γ mode no B ∧ Conversion.Conv B T
  | .absurd A p, T => ∃ (s : SortTag) (i : Term), HasType env Γ true A s.term ∧ HasType env Γ true p (.lt i (.natural 0)) ∧
      absurdAllowed mode A ∧ Conversion.Conv A T
  | .fold n init _, T => ∃ A, HasType env Γ mode n .u64 ∧ HasType env Γ mode init A ∧ Conversion.Conv A T
  | .loop n m init body, T => ∃ (proof : Bool), HasType env Γ true m (.pi false .u64 (loopSortTerm proof)) ∧
      IterationMotiveAllowed env mode proof m ∧ HasType env Γ (mode || proof) n .u64 ∧
      HasType env Γ (mode || proof) init (.app m (.natural 0)) ∧
      HasType env Γ (mode || proof) body (loopBodyType n m proof) ∧ IterationBodyAllowed env (mode || proof) body ∧
      Conversion.Conv (.app m n) T
  | .buffer n, T => HasType env Γ true n .u64 ∧ Conversion.Conv (.univ 0) T
  | .borrow b, T => ∃ R, HasType env Γ true b R ∧ Conversion.Conv (.ref R) T
  | .deref r, T => ∃ R, HasType env Γ true r (.ref R) ∧ Conversion.Conv R T
  | _, _ => True

theorem TypingView.convert {Γ : Context} {mode : Bool} {t A B : Term}
    (h : TypingView env Γ mode t A) (hc : Conversion.Conv A B) : TypingView env Γ mode t B := by
  fun_cases TypingView env Γ mode t A <;> simp only [TypingView] at h ⊢
  all_goals first
    | (obtain ⟨s,C,hA,hbody,hconv⟩ := h; exact ⟨s,C,hA,hbody,.trans hconv hc⟩)
    | (obtain ⟨e,C,D,hf,ha,allowed,hconv⟩ := h; exact ⟨e,C,D,hf,ha,allowed,.trans hconv hc⟩)
    | (obtain ⟨x₁,x₂,x₃,x₄,x₅,hconv⟩ := h; exact ⟨x₁,x₂,x₃,x₄,x₅,.trans hconv hc⟩)
    | (obtain ⟨x₁,x₂,x₃,x₄,x₅,x₆,x₇,hconv⟩ := h;
        exact ⟨x₁,x₂,x₃,x₄,x₅,x₆,x₇,.trans hconv hc⟩)
    | (obtain ⟨h₁,h₂,h₃,hconv⟩ := h; exact ⟨h₁,h₂,h₃,.trans hconv hc⟩)
    | (obtain ⟨n,h₁,h₂,h₃,hconv⟩ := h; exact ⟨n,h₁,h₂,h₃,.trans hconv hc⟩)
    | (obtain ⟨p,hs,hconv⟩ := h; exact ⟨p,hs,.trans hconv hc⟩)
    | (obtain ⟨h₁,h₂,hconv⟩ := h; exact ⟨h₁,h₂,.trans hconv hc⟩)
    | (obtain ⟨h₁,hconv⟩ := h; exact ⟨h₁,.trans hconv hc⟩)
    | exact False.elim h
    | trivial

theorem HasType.typingView {Γ : Context} {mode : Bool} {t T : Term}
    (h : HasType env Γ mode t T) : TypingView env Γ mode t T := by
  apply HasType.rec (t := h) (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun ctx mode term type _ => TypingView env ctx mode term type)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ _ => True) (motive_5 := fun _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case pi hA hB _ _ => exact ⟨_,_,hA,hB,.refl _⟩
  case lam hA hb _ _ => exact ⟨_,_,hA,hb,.refl _⟩
  case app hf ha allowed _ _ => exact ⟨_,_,_,hf,ha,allowed,.refl _⟩
  case elements hn hb hs _ => exact ⟨hn,hb,hs,.refl _⟩
  case index ha hi hp _ _ _ => exact ⟨_,Or.inl ha,hi,hp,.refl _⟩
  case borrowedIndex ha hi hp _ _ _ => exact ⟨_,Or.inr ha,hi,hp,.refl _⟩
  case buffer n _ => exact ⟨n,.refl _⟩
  case ghostBorrowOwned b owned _ => exact ⟨_,b,.refl _⟩
  case ghostDerefOwned r _ => exact ⟨_,r,.refl _⟩
  case ghostBorrow b _ => exact ⟨_,b,.refl _⟩
  case ghostDeref r _ => exact ⟨_,r,.refl _⟩
  case pack hp ha hq _ _ _ => exact ⟨hp,ha,hq,.refl _⟩
  case witness hs _ => exact ⟨_,hs,.refl _⟩
  case proof hs _ => exact ⟨_,hs,.refl _⟩
  case uadd ha hb _ _ => exact ⟨ha,hb,.refl _⟩
  case usub ha hb hp _ _ _ => exact ⟨ha,hb,hp,.refl _⟩
  case refl ha _ => exact ⟨ha,.refl _⟩
  case natural bound => exact ⟨bound,.refl _⟩
  case integer lo hi => exact ⟨lo,hi,.refl _⟩
  case transport hf he hp _ _ _ => exact ⟨_,_,hf,he,hp,.refl _⟩
  case ifLt ha hb hy hn _ _ _ _ => exact ⟨_,ha,hb,hy,hn,.refl _⟩
  case ifEq ha hb hy hn _ _ _ _ => exact ⟨_,ha,hb,hy,hn,.refl _⟩
  case absurd hT hp allowed _ _ => exact ⟨_,_,hT,hp,allowed,.refl _⟩
  case foldI64 hn hi hb allowed _ _ _ => exact ⟨_,hn,hi,.refl _⟩
  case foldOwned hn hi owned hb allowed _ _ _ => exact ⟨_,hn,hi,.refl _⟩
  case loop hm motivePolicy hn hi hb bodyPolicy _ _ _ _ => exact ⟨_,hm,motivePolicy,hn,hi,hb,bodyPolicy,.refl _⟩
  case dataElim found isData boxed size motive scrutinee generated branches allowed ihm ihs ihb =>
    rename_i family entry analysis ctx motiveTerm proof ghost scrutineeTerm indices types caseTerms
    cases analysis <;> trivial
  case convert ht hc ih => exact ih.convert hc

theorem HasType.lamView {Γ : Context} {mode e : Bool} {A body T : Term}
    (h : HasType env Γ mode (.lam e A body) T) :
    ∃ s B, Binder env Γ e A s ∧ HasType env (⟨A,e⟩ :: Γ) mode body B ∧ Conversion.Conv (.pi e A B) T :=
  h.typingView

theorem HasType.appView {Γ : Context} {mode : Bool} {f a T : Term}
    (h : HasType env Γ mode (.app f a) T) :
    ∃ e A B, HasType env Γ mode f (.pi e A B) ∧ HasType env Γ (mode || e) a A ∧
      applicationAllowed env mode A a ∧ Conversion.Conv (B.subst (single a)) T := h.typingView

theorem HasType.elementsView {Γ : Context} {mode : Bool} {n : Nat} {xs : List Term} {T : Term}
    (h : HasType env Γ mode (.elements n xs) T) :
    xs.length = n ∧ xs.length < 2^64 ∧ (∀ x ∈ xs, HasType env Γ mode x .i64) ∧
      Conversion.Conv (.array (.natural xs.length)) T := h.typingView

theorem HasType.indexView {Γ : Context} {mode : Bool} {a i p T : Term}
    (h : HasType env Γ mode (.index a i p) T) :
    ∃ n, (HasType env Γ mode a (.array n) ∨ HasType env Γ mode a (.ref (.buffer n))) ∧ HasType env Γ mode i .u64 ∧
      HasType env Γ true p (.lt i n) ∧ Conversion.Conv .i64 T := h.typingView

theorem HasType.packView {Γ : Context} {mode : Bool} {p a q T : Term}
    (h : HasType env Γ mode (.pack p a q) T) :
    HasType env Γ true p (.pi false .u64 .prop) ∧ HasType env Γ mode a .u64 ∧
      HasType env Γ true q (.app p a) ∧ Conversion.Conv (.refine p) T := h.typingView

theorem HasType.witnessView {Γ : Context} {mode : Bool} {s T : Term}
    (h : HasType env Γ mode (.witness s) T) :
    ∃ p, HasType env Γ mode s (.refine p) ∧ Conversion.Conv .u64 T := h.typingView

theorem HasType.proofView {Γ : Context} {mode : Bool} {s T : Term}
    (h : HasType env Γ mode (.proof s) T) :
    ∃ p, HasType env Γ true s (.refine p) ∧ Conversion.Conv (.app p (.witness s)) T := h.typingView

theorem HasType.uaddView {Γ : Context} {mode : Bool} {a b T : Term}
    (h : HasType env Γ mode (.uadd a b) T) :
    HasType env Γ mode a .u64 ∧ HasType env Γ mode b .u64 ∧ Conversion.Conv .u64 T := h.typingView

theorem HasType.usubView {Γ : Context} {mode : Bool} {a b p T : Term}
    (h : HasType env Γ mode (.usub a b p) T) :
    HasType env Γ mode a .u64 ∧ HasType env Γ mode b .u64 ∧
      HasType env Γ true p (.lt b (.uadd a (.natural 1))) ∧ Conversion.Conv .u64 T := h.typingView

theorem HasType.reflView {Γ : Context} {mode : Bool} {a T : Term}
    (h : HasType env Γ mode (.refl a) T) :
    HasType env Γ true a .u64 ∧ Conversion.Conv (.eq a a) T := h.typingView

theorem HasType.naturalView {Γ : Context} {mode : Bool} {n : Nat} {T : Term}
    (h : HasType env Γ mode (.natural n) T) : n < 2^64 ∧ Conversion.Conv .u64 T := h.typingView

theorem HasType.integerView {Γ : Context} {mode : Bool} {n : Int} {T : Term}
    (h : HasType env Γ mode (.integer n) T) :
    -(2^63 : Int) ≤ n ∧ n < (2^63 : Int) ∧ Conversion.Conv .i64 T := h.typingView

theorem HasType.piView {Γ : Context} {mode e : Bool} {A B T : Term}
    (h : HasType env Γ mode (.pi e A B) T) :
    ∃ s r, Binder env Γ e A s ∧ HasType env (⟨A,e⟩ :: Γ) true B r.term ∧
      Conversion.Conv (s.pi r).term T := h.typingView



theorem HasType.transportView {Γ : Context} {mode : Bool} {f e p T : Term}
    (h : HasType env Γ mode (.transport f e p) T) :
    ∃ a b, HasType env Γ true f (.pi false .u64 .prop) ∧ HasType env Γ true e (.eq a b) ∧
      HasType env Γ true p (.app f a) ∧ Conversion.Conv (.app f b) T := h.typingView

theorem HasType.ifLtView {Γ : Context} {mode : Bool} {a b yes no T : Term}
    (h : HasType env Γ mode (.ifLt a b yes no) T) :
    ∃ B, HasType env Γ mode a .u64 ∧ HasType env Γ mode b .u64 ∧
      HasType env (⟨.lt a b,true⟩ :: Γ) mode yes (B.rename Nat.succ) ∧
      HasType env Γ mode no B ∧ Conversion.Conv B T := h.typingView

theorem HasType.ifEqView {Γ : Context} {mode : Bool} {a b yes no T : Term}
    (h : HasType env Γ mode (.ifEq a b yes no) T) :
    ∃ B, HasType env Γ mode a .u64 ∧ HasType env Γ mode b .u64 ∧
      HasType env (⟨.eq a b,true⟩ :: Γ) mode yes (B.rename Nat.succ) ∧
      HasType env Γ mode no B ∧ Conversion.Conv B T := h.typingView

theorem HasType.absurdView {Γ : Context} {mode : Bool} {A p T : Term}
    (h : HasType env Γ mode (.absurd A p) T) :
    ∃ (s : SortTag) (i : Term), HasType env Γ true A s.term ∧ HasType env Γ true p (.lt i (.natural 0)) ∧
      absurdAllowed mode A ∧ Conversion.Conv A T := h.typingView


theorem HasType.foldView (h : HasType env Γ mode (.fold n init body) T) :
    ∃ A, HasType env Γ mode n .u64 ∧ HasType env Γ mode init A ∧ Conversion.Conv A T := h.typingView

theorem HasType.loopView {Γ : Context} {mode : Bool} {n m init body T : Term}
    (h : HasType env Γ mode (.loop n m init body) T) :
    ∃ (proof : Bool), HasType env Γ true m (.pi false .u64 (loopSortTerm proof)) ∧
      IterationMotiveAllowed env mode proof m ∧ HasType env Γ (mode || proof) n .u64 ∧
      HasType env Γ (mode || proof) init (.app m (.natural 0)) ∧
      HasType env Γ (mode || proof) body (loopBodyType n m proof) ∧ IterationBodyAllowed env (mode || proof) body ∧
      Conversion.Conv (.app m n) T := h.typingView

theorem HasType.borrowView (h : HasType env Γ mode (.borrow b) T) :
    ∃ R, HasType env Γ true b R ∧ Conversion.Conv (.ref R) T := h.typingView

theorem HasType.derefView (h : HasType env Γ mode (.deref r) T) :
    ∃ R, HasType env Γ true r (.ref R) ∧ Conversion.Conv R T := h.typingView

theorem HasType.bufferView (h : HasType env Γ mode (.buffer n) T) :
    HasType env Γ true n .u64 ∧ Conversion.Conv (.univ 0) T := h.typingView

end Jihoo.NativeKernel.Environment
