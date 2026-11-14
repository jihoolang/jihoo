import Jihoo.NativeConversion

/-! An independent universe-aware typing judgment on the complete native Term
syntax. The rules below cover the pure dependent fragment; unsupported native
operators have syntax but acquire no typing rule through an implicit default.
Contexts store annotations in pre-binder scope, newest first. -/
namespace Jihoo.NativeKernel

namespace Term
@[match_pattern] abbrev univ (n : Nat) : Term := .node (.universe n) []
@[match_pattern] abbrev prop : Term := .node .prop []
@[match_pattern] abbrev u64 : Term := .node .u64 []
@[match_pattern] abbrev i64 : Term := .node .i64 []
@[match_pattern] abbrev natural (n : Nat) : Term := .node (.natural n) []
@[match_pattern] abbrev integer (n : Int) : Term := .node (.integer n) []
@[match_pattern] abbrev array (n : Term) : Term := .node .array [n]
@[match_pattern] abbrev lt (a b : Term) : Term := .node .lt [a, b]
@[match_pattern] abbrev eq (a b : Term) : Term := .node .eq [a, b]
@[match_pattern] abbrev pi (e : Bool) (A B : Term) : Term := .node (.pi e) [A, B]
@[match_pattern] abbrev lam (e : Bool) (A b : Term) : Term := .node (.lam e) [A, b]
@[match_pattern] abbrev app (f a : Term) : Term := .node .app [f, a]
@[match_pattern] abbrev uadd (a b : Term) : Term := .node .uadd [a, b]
@[match_pattern] abbrev usub (a b p : Term) : Term := .node .usub [a, b, p]
@[match_pattern] abbrev refl (a : Term) : Term := .node .refl [a]
@[match_pattern] abbrev zeroLe (a : Term) : Term := .node .zeroLe [a]
@[match_pattern] abbrev decide (a b : Term) : Term := .node .decide [a, b]
@[match_pattern] abbrev elements (n : Nat) (xs : List Term) : Term := .node (.elements n) xs
@[match_pattern] abbrev index (a i p : Term) : Term := .node .index [a, i, p]
@[match_pattern] abbrev arith (op : Arith) (a b : Term) : Term := .node (.arith op) [a, b]
@[match_pattern] abbrev strict (a b : Term) : Term := .node .strict [a, b]
@[match_pattern] abbrev ltAdd (a b c p : Term) : Term := .node .ltAdd [a, b, c, p]
@[match_pattern] abbrev ltCancel (a b c p : Term) : Term := .node .ltCancel [a, b, c, p]
@[match_pattern] abbrev ltLe (a b c p q : Term) : Term := .node .ltLe [a, b, c, p, q]
@[match_pattern] abbrev transport (f e p : Term) : Term := .node .transport [f, e, p]
@[match_pattern] abbrev refine (p : Term) : Term := .node .refine [p]
@[match_pattern] abbrev pack (p a q : Term) : Term := .node .pack [p, a, q]
@[match_pattern] abbrev witness (s : Term) : Term := .node .witness [s]
@[match_pattern] abbrev proof (s : Term) : Term := .node .proof [s]
@[match_pattern] abbrev ifLt (a b yes no : Term) : Term := .node .ifLt [a, b, yes, no]
@[match_pattern] abbrev ifEq (a b yes no : Term) : Term := .node .ifEq [a, b, yes, no]
@[match_pattern] abbrev absurd (T p : Term) : Term := .node .absurd [T, p]
@[match_pattern] abbrev fold (n init body : Term) : Term := .node .fold [n, init, body]
@[match_pattern] abbrev loop (n motive init body : Term) : Term := .node .loop [n, motive, init, body]
end Term

inductive SortTag where
  | prop
  | type (level : Nat)
  deriving DecidableEq, Repr

def SortTag.term : SortTag → Term
  | .prop => .prop
  | .type n => .univ n

def SortTag.ofTerm : Term → Option SortTag
  | .prop => some .prop
  | .univ n => some (.type n)
  | _ => none

theorem SortTag.ofTerm_sound {t : Term} {s : SortTag} (h : ofTerm t = some s) : t = s.term := by
  unfold ofTerm at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · contradiction

/-- Prop codomains are impredicative. Other Pi sorts use the native maximum. -/
def SortTag.pi : SortTag → SortTag → SortTag
  | _, .prop => .prop
  | .prop, .type n => .type n
  | .type m, .type n => .type (max m n)

structure Binding where
  ty : Term
  erased : Bool
  deriving Repr

abbrev Context := List Binding

def lookup : Context → Nat → Option Binding
  | [], _ => none
  | b :: _, 0 => some ⟨b.ty.rename Nat.succ, b.erased⟩
  | _ :: ctx, n + 1 => (lookup ctx n).map fun b => ⟨b.ty.rename Nat.succ, b.erased⟩

/-- Pure binder policy from Core.binder. Erased data binders need the later
checked-family environment; erased U64 indices and proof binders are supported. -/
def binderAllowed (erased : Bool) (domain : Term) (sort : SortTag) : Prop :=
  if erased then sort = .prop ∨ Conversion.Conv domain .u64 else sort ≠ .prop

/-- Whether a native type's inhabitants are types or type families. -/
def kindOf : Term → Bool
  | .univ _ => true
  | .pi _ _ B => kindOf B
  | _ => false

/-- Runtime type families may abstract over U64 indices only. -/
def firstOrderKind : Term → Bool
  | .univ _ => true
  | .pi _ .u64 B => firstOrderKind B
  | _ => false

/- Native plain traversal. Family nodes conservatively reject until the
checked-family environment can distinguish boxed from flat data. -/
mutual
  def plain : Term → Bool
    | .var _ => true
    | .node op args =>
        match op with
        | .buffer | .ref | .pi _ | .back _ | .ind _ _ => false
        | .lam _ => match args with
            | [_, body] => plain body
            | _ => false
        | _ => plainArgs args
    termination_by t => sizeOf t

  def plainArgs : List Term → Bool
    | [] => true
    | a :: args => plain a && plainArgs args
    termination_by args => sizeOf args
end

/-- A code type argument must have a first-order kind and a convertible plain
representation. Ghost applications retain unrestricted type computation. -/
def applicationAllowed (ghost : Bool) (domain argument : Term) : Prop :=
  ghost = true ∨ kindOf domain = false ∨
    (firstOrderKind domain = true ∧
      ∃ normal, Conversion.Conv argument normal ∧ plain normal = true)

/-- No conversion of this type is a function type. Code-mode absurd
elimination retains this native representation restriction. -/
def nonFunction (T : Term) : Prop :=
  ∀ (e : Bool) (A B : Term), ¬ Conversion.Conv T (.pi e A B)

/-- Ghost elimination is closed under arbitrary type substitution. Executable
code retains the native nonfunction result restriction. -/
def absurdAllowed (ghost : Bool) (T : Term) : Prop := ghost = true ∨ nonFunction T

/-- A conservative executable nonfunction certificate from a rigid known type
head. Neutral and computed heads outside this list reject. -/
def nonFunctionHead : Term → Bool
  | .var _ => true
  | .univ _ | .prop | .u64 | .i64 | .array _ | .lt _ _ | .eq _ _ | .refine _ => true
  | _ => false

/-- Exact native scalar Fold telescope. The count is weakened beneath i. -/
def foldBodyType (n : Term) : Term :=
  .pi false .u64 (.pi true (.lt (.var 0) (n.rename Nat.succ)) (.pi false .i64 .i64))

/-- The proof bit distinguishes Prop induction from Type0 scalar iteration. -/
def loopSortTerm (proof : Bool) : Term := if proof then .prop else .univ 0

/-- Exact loop_body_type telescope from the native kernel: under i/p/acc,
i occurs at indices 0/1/2 respectively. The accumulator is erased in Prop. -/
def loopBodyType (n motive : Term) (proof : Bool) : Term :=
  .pi false .u64 (.pi true (.lt (.var 0) (n.rename Nat.succ))
    (.pi proof (.app (motive.rename (fun x => x + 2)) (.var 1))
      (.app (motive.rename (fun x => x + 3)) (.uadd (.var 2) (.natural 1)))))

/-- Code iteration has one scalar/refinement representation at every index.
Owned accumulators await a quantity-aware judgment and are excluded here. -/
def scalarLoopMotive : Term → Bool
  | .lam _ _ .u64 | .lam _ _ .i64 | .lam _ _ (.refine _) => true
  | _ => false

mutual
  /-- Conservative pure profile: explicit memory/ownership/family operations
  reject even under three lambdas. This is stronger than native's repetition
  gate and avoids admitting owned behavior before quantity preservation. -/
  def repeatPure : Term → Bool
    | .var _ => true
    | .node op args =>
        match op with
        | .alloc | .load | .store | .free | .drop _ | .buffer | .ref | .lend |
            .back _ | .give _ | .take | .borrow | .deref | .ind _ _ | .con _ _ _ |
            .elim _ _ | .caseOf _ _ | .view _ _ _ => false
        | _ => repeatPureArgs args
    termination_by t => sizeOf t

  def repeatPureArgs : List Term → Bool
    | [] => true
    | t :: ts => repeatPure t && repeatPureArgs ts
    termination_by ts => sizeOf ts
end

/-- Ghost substitution can replace pure annotations by arbitrary typed terms;
code admission retains the explicit repetition policy. -/
def loopBodyAllowed (ghost : Bool) (body : Term) : Prop := ghost = true ∨ repeatPure body = true

/-- Prop induction has no runtime accumulator. Code data iteration certifies a
convertible scalar/refinement motive with a fixed representation. -/
def loopMotiveAllowed (ghost proof : Bool) (motive : Term) : Prop :=
  ghost = true ∨ proof = true ∨
    ∃ normal, Conversion.Conv motive normal ∧ scalarLoopMotive normal = true

mutual
  /-- A domain must actually infer a sort; arbitrary annotations are not assumed
  to be types. This definition is independent of the executable checker. -/
  inductive Binder : Context → Bool → Term → SortTag → Prop where
    | intro : HasType ctx true A s.term → binderAllowed e A s → Binder ctx e A s

  inductive HasType : Context → Bool → Term → Term → Prop where
    | var : lookup ctx x = some b → (ghost = true ∨ b.erased = false) →
        HasType ctx ghost (.var x) b.ty
    | univ : n < 32 → HasType ctx ghost (.univ n) (.univ (n + 1))
    | prop : HasType ctx ghost .prop (.univ 0)
    | u64 : HasType ctx ghost .u64 (.univ 0)
    | i64 : HasType ctx ghost .i64 (.univ 0)
    | natural : n < 2^64 → HasType ctx ghost (.natural n) .u64
    | integer : -(2^63 : Int) ≤ n → n < (2^63 : Int) → HasType ctx ghost (.integer n) .i64
    | array : HasType ctx true n .u64 → HasType ctx ghost (.array n) (.univ 0)
    | lt : HasType ctx true a .u64 → HasType ctx true b .u64 → HasType ctx ghost (.lt a b) .prop
    | eq : HasType ctx true a .u64 → HasType ctx true b .u64 → HasType ctx ghost (.eq a b) .prop
    | pi : Binder ctx e A s → HasType (⟨A, e⟩ :: ctx) true B r.term →
        HasType ctx ghost (.pi e A B) (s.pi r).term
    | lam : Binder ctx e A s → HasType (⟨A, e⟩ :: ctx) ghost b B →
        HasType ctx ghost (.lam e A b) (.pi e A B)
    | app : HasType ctx ghost f (.pi e A B) → HasType ctx (ghost || e) a A →
        applicationAllowed ghost A a →
        HasType ctx ghost (.app f a) (B.subst (fun | 0 => a | n + 1 => .var n))
    | uadd : HasType ctx ghost a .u64 → HasType ctx ghost b .u64 →
        HasType ctx ghost (.uadd a b) .u64
    | usub : HasType ctx ghost a .u64 → HasType ctx ghost b .u64 →
        HasType ctx true p (.lt b (.uadd a (.natural 1))) → HasType ctx ghost (.usub a b p) .u64
    | refl : HasType ctx true a .u64 → HasType ctx ghost (.refl a) (.eq a a)
    | zeroLe : HasType ctx true a .u64 →
        HasType ctx ghost (.zeroLe a) (.lt (.natural 0) (.uadd a (.natural 1)))
    | decide : a < 2^64 → b < 2^64 → a < b →
        HasType ctx ghost (.decide (.natural a) (.natural b)) (.lt (.natural a) (.natural b))
    | decideConverted : HasType ctx true a .u64 → HasType ctx true b .u64 →
        Conversion.Conv a (.natural m) → Conversion.Conv b (.natural n) →
        m < 2^64 → n < 2^64 → m < n →
        HasType ctx ghost (.decide a b) (.lt a b)
    | elements : xs.length = n → xs.length < 2^64 →
        (∀ x ∈ xs, HasType ctx ghost x .i64) →
        HasType ctx ghost (.elements n xs) (.array (.natural xs.length))
    | index : HasType ctx ghost a (.array n) → HasType ctx ghost i .u64 →
        HasType ctx true p (.lt i n) → HasType ctx ghost (.index a i p) .i64
    | arith : HasType ctx ghost a .i64 → HasType ctx ghost b .i64 →
        HasType ctx ghost (.arith op a b) .i64
    | strict : HasType ctx ghost a A → HasType ctx ghost b B → HasType ctx ghost (.strict a b) B
    | ltAdd : HasType ctx true a .u64 → HasType ctx true b .u64 → HasType ctx true c .u64 →
        HasType ctx true p (.lt a b) → HasType ctx ghost (.ltAdd a b c p) (.lt (.uadd a c) (.uadd b c))
    | ltCancel : HasType ctx true a .u64 → HasType ctx true b .u64 → HasType ctx true c .u64 →
        HasType ctx true p (.lt (.uadd a c) (.uadd b c)) → HasType ctx ghost (.ltCancel a b c p) (.lt a b)
    | ltLe : HasType ctx true a .u64 → HasType ctx true b .u64 → HasType ctx true c .u64 →
        HasType ctx true p (.lt a b) → HasType ctx true q (.lt b (.uadd c (.natural 1))) →
        HasType ctx ghost (.ltLe a b c p q) (.lt a c)
    | transport : HasType ctx true f (.pi false .u64 .prop) → HasType ctx true e (.eq a b) →
        HasType ctx true p (.app f a) → HasType ctx ghost (.transport f e p) (.app f b)
    | refine : HasType ctx true p (.pi false .u64 .prop) → HasType ctx ghost (.refine p) (.univ 0)
    | pack : HasType ctx true p (.pi false .u64 .prop) → HasType ctx ghost a .u64 →
        HasType ctx true q (.app p a) → HasType ctx ghost (.pack p a q) (.refine p)
    | witness : HasType ctx ghost s (.refine p) → HasType ctx ghost (.witness s) .u64
    | proof : HasType ctx true s (.refine p) → HasType ctx ghost (.proof s) (.app p (.witness s))
    | ifLt : HasType ctx ghost a .u64 → HasType ctx ghost b .u64 →
        HasType (⟨.lt a b, true⟩ :: ctx) ghost yes (B.rename Nat.succ) →
        HasType ctx ghost no B → HasType ctx ghost (.ifLt a b yes no) B
    | ifEq : HasType ctx ghost a .u64 → HasType ctx ghost b .u64 →
        HasType (⟨.eq a b, true⟩ :: ctx) ghost yes (B.rename Nat.succ) →
        HasType ctx ghost no B → HasType ctx ghost (.ifEq a b yes no) B
    | absurd {s : SortTag} : HasType ctx true T s.term → HasType ctx true p (.lt i (.natural 0)) →
        absurdAllowed ghost T → HasType ctx ghost (.absurd T p) T
    | foldI64 : HasType ctx ghost n .u64 → HasType ctx ghost init .i64 →
        HasType ctx ghost body (foldBodyType n) → loopBodyAllowed ghost body →
        HasType ctx ghost (.fold n init body) .i64
    | loop : HasType ctx true motive (.pi false .u64 (loopSortTerm proof)) →
        loopMotiveAllowed ghost proof motive →
        HasType ctx (ghost || proof) n .u64 →
        HasType ctx (ghost || proof) init (.app motive (.natural 0)) →
        HasType ctx (ghost || proof) body (loopBodyType n motive proof) →
        loopBodyAllowed (ghost || proof) body →
        HasType ctx ghost (.loop n motive init body) (.app motive n)
    | convert : HasType ctx ghost t A → Conversion.Conv A B → HasType ctx ghost t B
end

end Jihoo.NativeKernel
