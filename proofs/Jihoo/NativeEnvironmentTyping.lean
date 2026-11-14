import Jihoo.NativeTyping
import Jihoo.NativeKernelEnvironment
import Jihoo.NativeResourceSyntax
import Jihoo.NativeBackSyntax
import Jihoo.NativeIterationMemory
import Jihoo.NativeDataSyntax
import Jihoo.NativeViewSyntax
import Jihoo.NativeEnvironmentConversion

/-! Environment-indexed native typing. All pure rules recurse through this
judgment, so global and family terms are usable beneath every pure constructor.
The raw environment is data; admission is established separately. -/
namespace Jihoo.NativeKernel.Environment

/-- Data-valued erased binders are recognized through the checked family table. -/
def dataBinderAllowed (env : Environment) (domain : Term) : Prop :=
  ∃ family count indices entry, env.families[family]? = some entry ∧
    entry.declaration.data = true ∧ Conversion.Conv env domain (.node (.ind family count) indices)

def binderAllowed (env : Environment) (erased : Bool) (domain : Term) (sort : SortTag) : Prop :=
  pureBinderAllowed env erased domain sort ∨
    (erased = true ∧ dataBinderAllowed env domain)

mutual
  /-- Native plain traversal with derived flat/boxed family classification. -/
  def familyPlain (env : Environment) : Term → Bool
    | .var _ => true
    | .node op args =>
        match op with
        | .buffer | .ref | .pi _ | .back _ => false
        | .ind family _ => (env.families[family]?).any (fun entry => !entry.boxed) && familyPlainArgs env args
        | .lam _ => match args with
            | [_, body] => familyPlain env body
            | _ => false
        | _ => familyPlainArgs env args
    termination_by t => sizeOf t
  def familyPlainArgs (env : Environment) : List Term → Bool
    | [] => true
    | a :: args => familyPlain env a && familyPlainArgs env args
    termination_by args => sizeOf args
end

/-- Retain the established pure certificate and admit checked flat families. -/
def plain (env : Environment) (term : Term) : Bool :=
  globalFree term && (Jihoo.NativeKernel.plain term || familyPlain env term)

def applicationAllowed (env : Environment) (ghost : Bool) (domain argument : Term) : Prop :=
  ghost = true ∨ ∃ domainNormal, Conversion.Conv env domain domainNormal ∧ globalFree domainNormal = true ∧
    (kindOf domainNormal = false ∨
      (firstOrderKind domainNormal = true ∧
        ∃ argumentNormal, Conversion.Conv env argument argumentNormal ∧ plain env argumentNormal = true))

theorem binderAllowed_ofPure (h : Jihoo.NativeKernel.binderAllowed erased domain sort) :
    binderAllowed env erased domain sort := Or.inl (pureBinderAllowed_ofLegacy h)

theorem applicationAllowed_ofPure (_h : Jihoo.NativeKernel.applicationAllowed ghost domain argument) :
    applicationAllowed env true domain argument := Or.inl rfl

/-- Ghost substitution may expose a function behind a neutral type variable.
Code checking keeps the native nonfunction gate; ghost checking is unrestricted. -/
def continuationAllowed (env : Environment) (ghost : Bool) (result : Term) : Prop :=
  ghost = true ∨ nonFunction env result

/-- Ownership comes from a buffer head or the actual boxed-family metadata. -/
inductive Owned (env : Environment) : Term → Prop where
  | buffer : Conversion.Conv env T (.buffer n) → Owned env T
  | family : env.families[family]? = some entry → entry.boxed = true →
      Conversion.Conv env T (.node (.ind family count) indices) → Owned env T

/-- Runtime results given back have one fixed representation and hold no borrow.
Family representation is read from the same environment as term typing. -/
def fixedRepresentation (env : Environment) : Term → Bool
  | .u64 | .i64 | .refine _ | .buffer _ | .back _ _ _ => true
  | .node (.ind family _) _ => (env.families[family]?).any fun entry => entry.boxed
  | _ => false

/-- Runtime admission keeps Core.back_motive's fixed representation check.
Ghost derivations may substitute arbitrary typed computations into a motive. -/
def BackRepresentation (env : Environment) (ghost erased : Bool) (motive : Term) : Prop :=
  ghost = true ∨ erased = true ∨
    ∃ flag domain body, Conversion.Conv env motive (.lam flag domain body) ∧
      fixedRepresentation env body = true

/-- A repeated expression is either a full native callback telescope or
certifiably memory-free. Ghost substitution has no runtime repetition duties. -/
def IterationBodyAllowed (env : Environment) (ghost : Bool) (body : Term) : Prop :=
  ghost = true ∨ hasLeadingLambdas 3 body = true ∨ iterationMemoryFree env body = true

/-- Runtime motives have a scalar/refinement or an owned representation at
every index. Proposition induction and ghost derivations remain unrestricted. -/
def IterationMotiveAllowed (env : Environment) (ghost proof : Bool) (motive : Term) : Prop :=
  ghost = true ∨ proof = true ∨
    (∃ normal, Conversion.Conv env motive normal ∧ scalarLoopMotive normal = true) ∨
    ∃ flag domain body, Conversion.Conv env motive (.lam flag domain body) ∧ Owned env body

/-- The native dependent-view result has one fixed runtime representation.
Ghost derivations are closed under arbitrary typed motive substitution. -/
def ViewMotiveAllowed (env : Environment) (ghost dependent : Bool) (motive : Term) : Prop :=
  ghost = true ∨ dependent = false ∨
    ∃ erased domain body,Conversion.Conv env motive (.lam erased domain body) ∧
      viewRepresentation 128 1 body = true

/-- The exact U64-indexed, proposition-valued native induction motive. -/
def propMotiveType : Nat → Term
  | 0 => .prop
  | n + 1 => .pi false .u64 (propMotiveType n)

/-- Core.case_type: fields, erased recursive hypotheses, then P(result).
Every shift is relative to the field/hypothesis scope of the stored signature. -/
def propCaseType (signature : Signature) (motive : Term) : Term := Id.run do
  let m := signature.fields.length
  let recursive := recursiveFields signature.fields
  let r := recursive.length
  let mut result := applications (motive.rename (fun x => x + m + r))
    (signature.result.map fun t => t.rename (fun x => x + r))
  for ((position, indices), q) in recursive.zipIdx.reverse do
    let ih := applications (motive.rename (fun x => x + m + q))
      (indices.map fun t => t.rename (fun x => x + (m + q - position)))
    result := .pi true ih result
  return signature.fields.foldr (fun field rest => .pi field.erased field.domain rest) result

mutual
  /-- A domain must actually infer a sort; arbitrary annotations are not assumed
  to be types. This definition is independent of the executable checker. -/
  inductive Binder (env : Environment) : Context → Bool → Term → SortTag → Prop where
    | intro : HasType env ctx true A s.term → binderAllowed env e A s → Binder env ctx e A s

  inductive HasType (env : Environment) : Context → Bool → Term → Term → Prop where
    | var : lookup ctx x = some b → (ghost = true ∨ b.erased = false) →
        HasType env ctx ghost (.var x) b.ty
    | univ : n < 32 → HasType env ctx ghost (.univ n) (.univ (n + 1))
    | prop : HasType env ctx ghost .prop (.univ 0)
    | u64 : HasType env ctx ghost .u64 (.univ 0)
    | i64 : HasType env ctx ghost .i64 (.univ 0)
    | natural : n < 2^64 → HasType env ctx ghost (.natural n) .u64
    | integer : -(2^63 : Int) ≤ n → n < (2^63 : Int) → HasType env ctx ghost (.integer n) .i64
    | array : HasType env ctx true n .u64 → HasType env ctx ghost (.array n) (.univ 0)
    | lt : HasType env ctx true a .u64 → HasType env ctx true b .u64 → HasType env ctx ghost (.lt a b) .prop
    | eq : HasType env ctx true a .u64 → HasType env ctx true b .u64 → HasType env ctx ghost (.eq a b) .prop
    | pi : Binder env ctx e A s → HasType env (⟨A, e⟩ :: ctx) true B r.term →
        HasType env ctx ghost (.pi e A B) (s.pi r).term
    | lam : Binder env ctx e A s → HasType env (⟨A, e⟩ :: ctx) ghost b B →
        HasType env ctx ghost (.lam e A b) (.pi e A B)
    | app : HasType env ctx ghost f (.pi e A B) → HasType env ctx (ghost || e) a A →
        applicationAllowed env ghost A a →
        HasType env ctx ghost (.app f a) (B.subst (fun | 0 => a | n + 1 => .var n))
    | uadd : HasType env ctx ghost a .u64 → HasType env ctx ghost b .u64 →
        HasType env ctx ghost (.uadd a b) .u64
    | usub : HasType env ctx ghost a .u64 → HasType env ctx ghost b .u64 →
        HasType env ctx true p (.lt b (.uadd a (.natural 1))) → HasType env ctx ghost (.usub a b p) .u64
    | refl : HasType env ctx true a .u64 → HasType env ctx ghost (.refl a) (.eq a a)
    | zeroLe : HasType env ctx true a .u64 →
        HasType env ctx ghost (.zeroLe a) (.lt (.natural 0) (.uadd a (.natural 1)))
    | decide : a < 2^64 → b < 2^64 → a < b →
        HasType env ctx ghost (.decide (.natural a) (.natural b)) (.lt (.natural a) (.natural b))
    | decideConverted : HasType env ctx true a .u64 → HasType env ctx true b .u64 →
        Conversion.Conv env a (.natural m) → Conversion.Conv env b (.natural n) →
        m < 2^64 → n < 2^64 → m < n →
        HasType env ctx ghost (.decide a b) (.lt a b)
    | elements : xs.length = n → xs.length < 2^64 →
        (∀ x ∈ xs, HasType env ctx ghost x .i64) →
        HasType env ctx ghost (.elements n xs) (.array (.natural xs.length))
    | index : HasType env ctx ghost a (.array n) → HasType env ctx ghost i .u64 →
        HasType env ctx true p (.lt i n) → HasType env ctx ghost (.index a i p) .i64
    | arith : HasType env ctx ghost a .i64 → HasType env ctx ghost b .i64 →
        HasType env ctx ghost (.arith op a b) .i64
    | strict : HasType env ctx ghost a A → HasType env ctx ghost b B → HasType env ctx ghost (.strict a b) B
    | ltAdd : HasType env ctx true a .u64 → HasType env ctx true b .u64 → HasType env ctx true c .u64 →
        HasType env ctx true p (.lt a b) → HasType env ctx ghost (.ltAdd a b c p) (.lt (.uadd a c) (.uadd b c))
    | ltCancel : HasType env ctx true a .u64 → HasType env ctx true b .u64 → HasType env ctx true c .u64 →
        HasType env ctx true p (.lt (.uadd a c) (.uadd b c)) → HasType env ctx ghost (.ltCancel a b c p) (.lt a b)
    | ltLe : HasType env ctx true a .u64 → HasType env ctx true b .u64 → HasType env ctx true c .u64 →
        HasType env ctx true p (.lt a b) → HasType env ctx true q (.lt b (.uadd c (.natural 1))) →
        HasType env ctx ghost (.ltLe a b c p q) (.lt a c)
    | transport : HasType env ctx true f (.pi false .u64 .prop) → HasType env ctx true e (.eq a b) →
        HasType env ctx true p (.app f a) → HasType env ctx ghost (.transport f e p) (.app f b)
    | refine : HasType env ctx true p (.pi false .u64 .prop) → HasType env ctx ghost (.refine p) (.univ 0)
    | pack : HasType env ctx true p (.pi false .u64 .prop) → HasType env ctx ghost a .u64 →
        HasType env ctx true q (.app p a) → HasType env ctx ghost (.pack p a q) (.refine p)
    | witness : HasType env ctx ghost s (.refine p) → HasType env ctx ghost (.witness s) .u64
    | proof : HasType env ctx true s (.refine p) → HasType env ctx ghost (.proof s) (.app p (.witness s))
    | ifLt : HasType env ctx ghost a .u64 → HasType env ctx ghost b .u64 →
        HasType env (⟨.lt a b, true⟩ :: ctx) ghost yes (B.rename Nat.succ) →
        HasType env ctx ghost no B → HasType env ctx ghost (.ifLt a b yes no) B
    | ifEq : HasType env ctx ghost a .u64 → HasType env ctx ghost b .u64 →
        HasType env (⟨.eq a b, true⟩ :: ctx) ghost yes (B.rename Nat.succ) →
        HasType env ctx ghost no B → HasType env ctx ghost (.ifEq a b yes no) B
    | absurd {s : SortTag} : HasType env ctx true T s.term → HasType env ctx true p (.lt i (.natural 0)) →
        absurdAllowed env ghost T → HasType env ctx ghost (.absurd T p) T
    | foldI64 : HasType env ctx ghost n .u64 → HasType env ctx ghost init .i64 →
        HasType env ctx ghost body (foldBodyType n) → IterationBodyAllowed env ghost body →
        HasType env ctx ghost (.fold n init body) .i64
    | foldOwned : HasType env ctx ghost n .u64 → HasType env ctx ghost init accumulator →
        Owned env accumulator → HasType env ctx ghost body (foldAccumulatorBodyType n accumulator) →
        IterationBodyAllowed env ghost body →
        HasType env ctx ghost (.fold n init body) accumulator
    | loop : HasType env ctx true motive (.pi false .u64 (loopSortTerm proof)) →
        IterationMotiveAllowed env ghost proof motive →
        HasType env ctx (ghost || proof) n .u64 →
        HasType env ctx (ghost || proof) init (.app motive (.natural 0)) →
        HasType env ctx (ghost || proof) body (loopBodyType n motive proof) →
        IterationBodyAllowed env (ghost || proof) body →
        HasType env ctx ghost (.loop n motive init body) (.app motive n)
    | global : env.globals[g]? = some declaration →
        HasType env ctx ghost (.node (.global g) [])
          (declaration.type.rename (fun x => x + ctx.length))
    | ind : env.families[f]? = some entry → count = entry.declaration.arity →
        xs.length = count → (∀ x ∈ xs, HasType env ctx true x .u64) →
        HasType env ctx ghost (.node (.ind f count) xs)
          (if entry.declaration.data then .univ 0 else .prop)
    | con : env.families[f]? = some entry → entry.signatures[k]? = some signature →
        count = xs.length →
        Arguments env ctx ghost entry.declaration.data
          ((signatureTerm f signature).rename (fun x => x + ctx.length)) xs
          (.node (.ind f arity) indices) →
        HasType env ctx ghost (.node (.con f k count) xs) (.node (.ind f arity) indices)
    | propElim : env.families[f]? = some entry → entry.declaration.data = false →
        HasType env ctx true motive (propMotiveType entry.declaration.arity) →
        Cases env ctx motive entry.signatures cases →
        HasType env ctx true scrutinee (.node (.ind f entry.declaration.arity) indices) →
        HasType env ctx ghost (.node (.elim f cases.length) (motive :: (cases ++ [scrutinee])))
          (applications motive indices)
    | buffer : HasType env ctx true n .u64 → HasType env ctx ghost (.buffer n) (.univ 0)
    | alloc : HasType env ctx ghost n .u64 → HasType env ctx ghost value .i64 →
        HasType env ctx ghost (.alloc n value) (.buffer n)
    | store : HasType env ctx ghost buffer (.buffer n) → HasType env ctx ghost index .u64 →
        HasType env ctx ghost value .i64 → HasType env ctx true proof (.lt index n) →
        HasType env ctx ghost (.store buffer index value proof) (.buffer n)
    | load : HasType env ctx ghost buffer (.buffer n) → HasType env ctx ghost index .u64 →
        HasType env ctx true proof (.lt index n) →
        HasType env ctx ghost continuation (.pi false valueDomain (.pi false ownerDomain result)) →
        Conversion.Conv env valueDomain .i64 → Conversion.Conv env ownerDomain (.buffer (n.rename Nat.succ)) →
        Conversion.Conv env result normal → PartialRenaming.shift (-2) 0 normal = some outside →
        continuationAllowed env ghost outside → HasType env ctx ghost (.load buffer index proof continuation) outside
    | free : HasType env ctx ghost buffer (.buffer n) → HasType env ctx ghost rest T →
        HasType env ctx ghost (.free buffer rest) T
    | refBuffer : HasType env ctx true n .u64 →
        HasType env ctx ghost (.ref (.buffer n)) (.univ 0)
    | ghostBorrow : HasType env ctx true buffer (.buffer n) →
        HasType env ctx true (.borrow buffer) (.ref (.buffer n))
    | ghostDeref : HasType env ctx true reference (.ref (.buffer n)) →
        HasType env ctx true (.deref reference) (.buffer n)
    | borrowedIndex : HasType env ctx ghost reference (.ref (.buffer n)) →
        HasType env ctx ghost index .u64 → HasType env ctx true proof (.lt index n) →
        HasType env ctx ghost (.index reference index proof) .i64
    | back : HasType env ctx true owner (.univ 0) → Owned env owner →
        HasType env ctx true motive (.pi false owner (loopSortTerm erased)) →
        BackRepresentation env ghost erased motive →
        HasType env ctx ghost (.back erased owner motive) (.univ 0)
    | give : HasType env ctx ghost owner T → Owned env T →
        HasType env ctx true motive (.pi false T (loopSortTerm erased)) →
        BackRepresentation env ghost erased motive →
        HasType env ctx (ghost || erased) result (.app motive owner) →
        HasType env ctx ghost (.give erased motive owner result) (.back erased T motive)
    | take : HasType env ctx ghost value (.back erased owner motive) →
        HasType env ctx ghost (.lam false declaredOwner (.lam erased declaredResult body))
          (.pi false inferredOwner (.pi inferredErased inferredResult result)) →
        Conversion.Conv env declaredOwner owner → Conversion.Conv env declaredResult (takeResultType motive) →
        Conversion.Conv env result normal → PartialRenaming.shift (-2) 0 normal = some outside →
        continuationAllowed env ghost outside →
        HasType env ctx ghost (.take value (.lam false declaredOwner (.lam erased declaredResult body))) outside
    | dataElim : env.families[family]? = some entry → entry.declaration.data = true →
        (analysis = true → entry.boxed = true) →
        indices.length = entry.declaration.arity →
        HasType env ctx true motive (dataMotiveType family entry.declaration.params
          entry.declaration.arity (indices.take entry.declaration.params) proof) →
        HasType env ctx (ghost || proof) scrutinee
          (.node (.ind family entry.declaration.arity) indices) →
        dataCaseTypes family entry.declaration.params ctx.length entry.signatures
          (indices.take entry.declaration.params) motive (entry.boxed && !analysis) proof = some types →
        BranchTypes env ctx (ghost || proof) types cases →
        continuationAllowed env (ghost || proof)
          (.app (applications motive (indices.drop entry.declaration.params)) scrutinee) →
        HasType env ctx ghost
          (.node (if analysis then .caseOf family cases.length else .elim family cases.length)
            (motive :: (cases ++ [scrutinee])))
          (.app (applications motive (indices.drop entry.declaration.params)) scrutinee)
    | drop : env.families[family]? = some entry → entry.boxed = true →
        HasType env ctx ghost owner (.node (.ind family count) indices) →
        HasType env ctx ghost rest T →
        HasType env ctx ghost (.node (.drop family) [owner, rest]) T
    | refOwned : HasType env ctx true owner (.univ 0) → Owned env owner →
        HasType env ctx ghost (.ref owner) (.univ 0)
    | ghostBorrowOwned : HasType env ctx true owner T → Owned env T →
        HasType env ctx true (.borrow owner) (.ref T)
    | ghostDerefOwned : HasType env ctx true reference (.ref T) →
        HasType env ctx true (.deref reference) T
    | view : env.families[family]? = some entry → entry.declaration.data = true → entry.boxed = true →
        entry.declaration.arity = entry.declaration.params → indices.length = entry.declaration.params →
        HasType env ctx ghost scrutinee (.ref (.node (.ind family entry.declaration.arity) indices)) →
        HasType env ctx true motive
          (viewMotiveType dependent (.node (.ind family entry.declaration.arity) indices)) →
        ViewMotiveAllowed env ghost dependent motive →
        viewCaseTypes env family entry.declaration.params ctx.length entry.signatures indices motive recursion dependent = some types →
        BranchTypes env ctx ghost types cases →
        HasType env ctx ghost (.node (.view recursion family cases.length) (motive :: (cases ++ [scrutinee])))
          (viewResult dependent motive scrutinee)
    | convert : HasType env ctx ghost t A → Conversion.Conv env A B → HasType env ctx ghost t B

  /-- Constructor fields instantiate an actual dependent Pi telescope. -/
  inductive Arguments (env : Environment) : Context → Bool → Bool →
      Term → List Term → Term → Prop where
    | nil : Conversion.Conv env telescope result → Arguments env ctx ghost data telescope [] result
    | cons : Conversion.Conv env telescope (.pi erased domain rest) →
        HasType env ctx (ghost || !(data && !erased)) argument domain →
        Arguments env ctx ghost data
          (rest.subst (fun | 0 => argument | n + 1 => .var n)) arguments result →
        Arguments env ctx ghost data telescope (argument :: arguments) result

  /-- There is exactly one checked branch for each checked constructor signature. -/
  inductive Cases (env : Environment) : Context → Term →
      List Signature → List Term → Prop where
    | nil : Cases env ctx motive [] []
    | cons : HasType env ctx true branch (propCaseType signature motive) →
        Cases env ctx motive signatures branches →
        Cases env ctx motive (signature :: signatures) (branch :: branches)
  /-- Branch terms are checked against the concrete generated telescope list. -/
  inductive BranchTypes (env : Environment) : Context → Bool → List Term → List Term → Prop where
    | nil : BranchTypes env ctx ghost [] []
    | cons : HasType env ctx ghost branch type → BranchTypes env ctx ghost types branches →
        BranchTypes env ctx ghost (type :: types) (branch :: branches)

end

/-- Every legacy pure derivation has a constructive ghost embedding. Runtime
nonfunction certificates are not cast from the smaller legacy conversion. -/
theorem ofPure (h : Jihoo.NativeKernel.HasType ctx ghost t T) : HasType env ctx true t T := by
  induction h using Jihoo.NativeKernel.HasType.rec
    (motive_1 := fun ctx e A s _ => Binder env ctx e A s)
  all_goals first
    | contradiction
    | trivial
    | solve | apply Binder.intro <;> first | assumption | exact binderAllowed_ofPure (by assumption)
    | solve | apply HasType.var <;> first | assumption | exact Or.inl rfl
    | solve | apply HasType.univ <;> assumption
    | solve | apply HasType.prop <;> assumption
    | solve | apply HasType.u64 <;> assumption
    | solve | apply HasType.i64 <;> assumption
    | solve | apply HasType.natural <;> assumption
    | solve | apply HasType.integer <;> assumption
    | solve | apply HasType.array <;> assumption
    | solve | apply HasType.lt <;> assumption
    | solve | apply HasType.eq <;> assumption
    | solve | apply HasType.pi <;> assumption
    | solve | apply HasType.lam <;> assumption
    | solve | apply HasType.app <;> first | assumption | exact Or.inl rfl
    | solve | apply HasType.uadd <;> assumption
    | solve | apply HasType.usub <;> assumption
    | solve | apply HasType.refl <;> assumption
    | solve | apply HasType.zeroLe <;> assumption
    | solve | apply HasType.decide <;> assumption
    | solve | apply HasType.decideConverted <;> first | assumption | exact .legacy (by assumption)
    | solve | apply HasType.elements <;> assumption
    | solve | apply HasType.index <;> assumption
    | solve | apply HasType.arith <;> assumption
    | solve | apply HasType.strict <;> assumption
    | solve | apply HasType.ltAdd <;> assumption
    | solve | apply HasType.ltCancel <;> assumption
    | solve | apply HasType.ltLe <;> assumption
    | solve | apply HasType.transport <;> assumption
    | solve | apply HasType.refine <;> assumption
    | solve | apply HasType.pack <;> assumption
    | solve | apply HasType.witness <;> assumption
    | solve | apply HasType.proof <;> assumption
    | solve | apply HasType.ifLt <;> assumption
    | solve | apply HasType.ifEq <;> assumption
    | solve | apply HasType.absurd <;> first | assumption | exact Or.inl rfl
    | solve | apply HasType.foldI64 <;> first | assumption | exact Or.inl rfl
    | solve | apply HasType.loop <;> first | assumption | exact Or.inl rfl
    | solve | apply HasType.convert <;> first | assumption | exact .legacy (by assumption)

end Jihoo.NativeKernel.Environment
