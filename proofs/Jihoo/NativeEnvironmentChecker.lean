import Jihoo.NativeEnvironmentTyping
import Jihoo.NativePartialRenaming
import Jihoo.NativeChecker

/-! Data-input executable checking on the complete native constructor syntax.
Type comparison uses verified bounded conversion. Global/family
environments and ownership rules are not silently
assumed: operators without a rule below reject. -/
namespace Jihoo.NativeKernel.Environment.Checker

/-- Verified conversion of an actual inferred type to an expected type. -/
def accepts (fuel : Nat) (inferred : Option Term) (expected : Term) : Bool :=
  match inferred with
  | some actual => Conversion.equal fuel actual expected
  | none => false

/-- Normalize an inferred type before inspecting its head constructor. -/
def expose (fuel : Nat) (inferred : Option Term) : Option Term :=
  inferred.bind (Conversion.normalize? fuel)

def dataBinderOK (env : Environment) : Term → Bool
  | .node (.ind family _) _ => (env.families[family]?).any fun entry => entry.declaration.data
  | _ => false

/-- Native erased-data policy uses metadata from the actual environment. -/
def pureBinderOK (fuel : Nat) (erased : Bool) (A : Term) (s : SortTag) : Bool :=
  if erased then decide (s = .prop) || Conversion.equal fuel A .u64 else decide (s ≠ .prop)

def binderOK (fuel : Nat) (env : Environment) (erased : Bool) (A : Term) (s : SortTag) : Bool :=
  pureBinderOK fuel erased A s ||
    (erased && dataBinderOK env (Conversion.normalize fuel A))

/-- Executable native first-order gate after verified normalization. -/
def applicationOK (fuel : Nat) (env : Environment) (ghost : Bool) (domain argument : Term) : Bool :=
  ghost || (globalFree domain && (!kindOf domain ||
    (firstOrderKind domain && plain env (Conversion.normalize fuel argument))))

/-- Read the exact native loop motive sort: Prop or Type0 only. -/
def loopSort : Term → Option Bool
  | .prop => some true
  | .univ 0 => some false
  | _ => none

def loopMotiveOK (fuel : Nat) (proof : Bool) (motive : Term) : Bool :=
  proof || scalarLoopMotive (Conversion.normalize fuel motive)

/-- Resolve an owned head against actual family storage metadata. -/
def ownedHead (env : Environment) : Term → Bool
  | .buffer _ => true
  | .node (.ind family _) _ => (env.families[family]?).any fun entry => entry.boxed
  | _ => false

/-- Exact native representation gate. Erased motive results are propositions;
other motives normalize to lambdas with a fixed known runtime representation. -/
def backMotiveOK (fuel : Nat) (env : Environment) (erased : Bool) (motive : Term) : Bool :=
  erased || match Conversion.normalize fuel motive with
    | .lam _ _ body => fixedRepresentation env body
    | _ => false

/-- Additional rigid ownership heads can never be function types. -/
def resourceNonFunctionHead : Term → Bool
  | .buffer _ | .ref _ | .back _ _ _ | .node (.ind _ _) _ => true
  | _ => false

def takeNonFunctionHead (result : Term) : Bool := nonFunctionHead result || resourceNonFunctionHead result

/-- Native binders(body,3) permits memory operations beneath the callback. -/
def iterationBodyOK (env : Environment) (body : Term) : Bool :=
  hasLeadingLambdas 3 body || iterationMemoryFree env body

def ownedLoopMotiveOK (fuel : Nat) (env : Environment) (motive : Term) : Bool :=
  match Conversion.normalize fuel motive with
  | .lam _ _ body => ownedHead env body
  | _ => false

def iterationMotiveOK (fuel : Nat) (env : Environment) (proof : Bool) (motive : Term) : Bool :=
  loopMotiveOK fuel proof motive || ownedLoopMotiveOK fuel env motive

/-- Instantiate all constructor fields using only concrete recursive inference. -/
def instantiate (inferField : Bool → Term → Option Term) (fuel : Nat) (ghost data : Bool) :
    Term → List Term → Option Term
  | telescope, [] => some (Conversion.normalize fuel telescope)
  | telescope, argument :: arguments =>
      match Conversion.normalize fuel telescope with
      | .pi erased domain rest =>
          if accepts fuel (inferField (ghost || !(data && !erased)) argument) domain then
            instantiate inferField fuel ghost data
              (rest.subst (fun | 0 => argument | n + 1 => .var n)) arguments
          else none
      | _ => none

/-- Infer each proposition branch against its derived dependent case telescope. -/
def branches (inferBranch : Term → Option Term) (fuel : Nat) (motive : Term) :
    List Signature → List Term → Bool
  | [], [] => true
  | signature :: signatures, branch :: rest =>
      accepts fuel (inferBranch branch) (propCaseType signature motive) &&
        branches inferBranch fuel motive signatures rest
  | _, _ => false

/-- Decode the exact native motive/cases/scrutinee child layout. -/
def splitCases : Nat → List Term → Option (List Term × Term)
  | 0, [scrutinee] => some ([], scrutinee)
  | n + 1, branch :: children => do
      let (branches, scrutinee) ← splitCases n children
      pure (branch :: branches, scrutinee)
  | _, _ => none

/-- Check a list of computed branch types; no signature callback is accepted. -/
def branchesAgainst (inferBranch : Term → Option Term) (fuel : Nat) :
    List Term → List Term → Bool
  | [], [] => true
  | type :: types, branch :: branches =>
      accepts fuel (inferBranch branch) type && branchesAgainst inferBranch fuel types branches
  | _, _ => false

def dataMotiveProof (inferred : Option Term) (fuel family params arity : Nat) (ps : List Term) : Option Bool :=
  if accepts fuel inferred (dataMotiveType family params arity ps true) then some true
  else if accepts fuel inferred (dataMotiveType family params arity ps false) then some false
  else none

/-- Concrete data elimination. The recursive inference argument is always the
smaller-fuel call of infer; soundness discharges it from that induction. -/
def dataEliminate (inferSub : Bool → Term → Option Term) (fuel : Nat)
    (env : Environment) (ctx : Context) (ghost analysis : Bool)
    (family count : Nat) (motive : Term) (children : List Term) : Option Term := do
  let entry ← env.families[family]?
  if entry.declaration.data = true ∧ (analysis = false ∨ entry.boxed = true) then
    let (cases, scrutinee) ← splitCases count children
    let .node (.ind g arity) indices ← expose fuel (inferSub true scrutinee) | none
    if g = family ∧ arity = entry.declaration.arity ∧ indices.length = entry.declaration.arity then
      let ps := indices.take entry.declaration.params
      let proof ← dataMotiveProof (inferSub true motive) fuel family
        entry.declaration.params entry.declaration.arity ps
      let types ← dataCaseTypes family entry.declaration.params ctx.length entry.signatures ps motive
        (entry.boxed && !analysis) proof
      let result := Term.app (applications motive (indices.drop entry.declaration.params)) scrutinee
      if accepts fuel (inferSub (ghost || proof) scrutinee) (.node (.ind family arity) indices) = true ∧
          branchesAgainst (inferSub (ghost || proof)) fuel types cases = true ∧
          ((ghost || proof) || takeNonFunctionHead (Conversion.normalize fuel result)) = true
      then some result else none
    else none
  else none

mutual
  def infer : Nat → Environment → Context → Bool → Term → Option Term
    | 0, _, _, _, _ => none
    | fuel + 1, env, ctx, ghost, term =>
      match term with
      | .var x =>
          match lookup ctx x with
          | some b => if ghost = true ∨ b.erased = false then some b.ty else none
          | none => none
      | .univ n => if n < 32 then some (.univ (n + 1)) else none
      | .prop | .u64 | .i64 => some (.univ 0)
      | .natural n => if n < 2^64 then some .u64 else none
      | .integer n => if -(2^63 : Int) ≤ n ∧ n < (2^63 : Int) then some .i64 else none
      | .array n => if accepts fuel (infer fuel env ctx true n) .u64 = true then some (.univ 0) else none
      | .lt a b | .eq a b =>
          if accepts fuel (infer fuel env ctx true a) .u64 = true ∧ accepts fuel (infer fuel env ctx true b) .u64 = true
          then some .prop else none
      | .pi e A B =>
          match binder fuel env ctx e A with
          | some s =>
              match expose fuel (infer fuel env (⟨A, e⟩ :: ctx) true B) with
              | some T => (SortTag.ofTerm T).map fun r => (s.pi r).term
              | none => none
          | none => none
      | .lam e A body =>
          match binder fuel env ctx e A with
          | some _ => (infer fuel env (⟨A, e⟩ :: ctx) ghost body).map (Term.pi e A)
          | none => none
      | .app f a =>
          match expose fuel (infer fuel env ctx ghost f) with
          | some (.pi e A B) =>
              if accepts fuel (infer fuel env ctx (ghost || e) a) A = true ∧ applicationOK fuel env ghost A a = true ∧ Conversion.substitutionSafe B a = true
              then some (B.subst (fun | 0 => a | n + 1 => .var n)) else none
          | _ => none
      | .uadd a b =>
          if accepts fuel (infer fuel env ctx ghost a) .u64 = true ∧ accepts fuel (infer fuel env ctx ghost b) .u64 = true
          then some .u64 else none
      | .usub a b p =>
          if accepts fuel (infer fuel env ctx ghost a) .u64 = true ∧ accepts fuel (infer fuel env ctx ghost b) .u64 = true ∧
              accepts fuel (infer fuel env ctx true p) (.lt b (.uadd a (.natural 1))) = true
          then some .u64 else none
      | .refl a => if accepts fuel (infer fuel env ctx true a) .u64 = true then some (.eq a a) else none
      | .zeroLe a => if accepts fuel (infer fuel env ctx true a) .u64 = true
          then some (.lt (.natural 0) (.uadd a (.natural 1))) else none
      | .decide a b =>
          if accepts fuel (infer fuel env ctx true a) .u64 = true ∧
              accepts fuel (infer fuel env ctx true b) .u64 = true then
            match Conversion.normalize fuel a, Conversion.normalize fuel b with
            | .natural m, .natural n =>
                if m < 2^64 ∧ n < 2^64 ∧ m < n then some (.lt a b) else none
            | _, _ => none
          else none
      | .elements n xs =>
          if xs.length = n ∧ xs.length < 2^64 ∧
              xs.all (fun x => accepts fuel (infer fuel env ctx ghost x) .i64) = true
          then some (.array (.natural xs.length)) else none
      | .index a i p =>
          match expose fuel (infer fuel env ctx ghost a) with
          | some (.array n) =>
              if accepts fuel (infer fuel env ctx ghost i) .u64 = true ∧ accepts fuel (infer fuel env ctx true p) (.lt i n) = true
              then some .i64 else none
          | some (.ref (.buffer n)) =>
              if accepts fuel (infer fuel env ctx ghost i) .u64 = true ∧ accepts fuel (infer fuel env ctx true p) (.lt i n) = true
              then some .i64 else none
          | _ => none
      | .arith _op a b =>
          if accepts fuel (infer fuel env ctx ghost a) .i64 = true ∧ accepts fuel (infer fuel env ctx ghost b) .i64 = true
          then some .i64 else none
      | .strict a b =>
          match expose fuel (infer fuel env ctx ghost a) with
          | some _ => infer fuel env ctx ghost b
          | none => none
      | .ltAdd a b c p =>
          if accepts fuel (infer fuel env ctx true a) .u64 = true ∧ accepts fuel (infer fuel env ctx true b) .u64 = true ∧
              accepts fuel (infer fuel env ctx true c) .u64 = true ∧ accepts fuel (infer fuel env ctx true p) (.lt a b) = true
          then some (.lt (.uadd a c) (.uadd b c)) else none
      | .ltCancel a b c p =>
          if accepts fuel (infer fuel env ctx true a) .u64 = true ∧ accepts fuel (infer fuel env ctx true b) .u64 = true ∧
              accepts fuel (infer fuel env ctx true c) .u64 = true ∧
              accepts fuel (infer fuel env ctx true p) (.lt (.uadd a c) (.uadd b c)) = true
          then some (.lt a b) else none
      | .ltLe a b c p q =>
          if accepts fuel (infer fuel env ctx true a) .u64 = true ∧ accepts fuel (infer fuel env ctx true b) .u64 = true ∧
              accepts fuel (infer fuel env ctx true c) .u64 = true ∧ accepts fuel (infer fuel env ctx true p) (.lt a b) = true ∧
              accepts fuel (infer fuel env ctx true q) (.lt b (.uadd c (.natural 1))) = true
          then some (.lt a c) else none
      | .transport f e p =>
          match expose fuel (infer fuel env ctx true e) with
          | some (.eq a b) =>
              if accepts fuel (infer fuel env ctx true f) (.pi false .u64 .prop) = true ∧
                  accepts fuel (infer fuel env ctx true p) (.app f a) = true
              then some (.app f b) else none
          | _ => none
      | .refine p => if accepts fuel (infer fuel env ctx true p) (.pi false .u64 .prop) = true
          then some (.univ 0) else none
      | .pack p a q =>
          if accepts fuel (infer fuel env ctx true p) (.pi false .u64 .prop) = true ∧
              accepts fuel (infer fuel env ctx ghost a) .u64 = true ∧ accepts fuel (infer fuel env ctx true q) (.app p a) = true
          then some (.refine p) else none
      | .witness s =>
          match expose fuel (infer fuel env ctx ghost s) with
          | some (.refine _p) => some .u64
          | _ => none
      | .proof s =>
          match expose fuel (infer fuel env ctx true s) with
          | some (.refine p) => some (.app p (.witness s))
          | _ => none
      | .ifLt a b yes no =>
          if accepts fuel (infer fuel env ctx ghost a) .u64 = true ∧
              accepts fuel (infer fuel env ctx ghost b) .u64 = true then
            match expose fuel (infer fuel env (⟨.lt a b, true⟩ :: ctx) ghost yes) with
            | some Y =>
                match PartialRenaming.shift (-1) 0 Y with
                | some B => if accepts fuel (infer fuel env ctx ghost no) B then some B else none
                | none => none
            | none => none
          else none
      | .ifEq a b yes no =>
          if accepts fuel (infer fuel env ctx ghost a) .u64 = true ∧
              accepts fuel (infer fuel env ctx ghost b) .u64 = true then
            match expose fuel (infer fuel env (⟨.eq a b, true⟩ :: ctx) ghost yes) with
            | some Y =>
                match PartialRenaming.shift (-1) 0 Y with
                | some B => if accepts fuel (infer fuel env ctx ghost no) B then some B else none
                | none => none
            | none => none
          else none
      | .absurd T p =>
          match expose fuel (infer fuel env ctx true T) with
          | some U =>
              match SortTag.ofTerm U with
              | some _ =>
                  if ghost || nonFunctionHead (Conversion.normalize fuel T) then
                    match expose fuel (infer fuel env ctx true p) with
                    | some (.lt _i n) =>
                        if Conversion.equal fuel n (.natural 0) then some T else none
                    | _ => none
                  else none
              | none => none
          | none => none
      | .fold n init body =>
          if accepts fuel (infer fuel env ctx ghost n) .u64 = true then
            match expose fuel (infer fuel env ctx ghost init) with
            | some .i64 =>
                if accepts fuel (infer fuel env ctx ghost body) (foldBodyType n) = true ∧
                    iterationBodyOK env body = true then some .i64 else none
            | some accumulator =>
                if ownedHead env accumulator = true ∧
                    accepts fuel (infer fuel env ctx ghost body) (foldAccumulatorBodyType n accumulator) = true ∧
                    iterationBodyOK env body = true then some accumulator else none
            | none => none
          else none
      | .loop n motive init body =>
          match expose fuel (infer fuel env ctx true motive) with
          | some (.pi false domain level) =>
              if Conversion.equal fuel domain .u64 then
                match loopSort level with
                | some proof =>
                    if iterationMotiveOK fuel env proof motive then
                      if accepts fuel (infer fuel env ctx (ghost || proof) n) .u64 = true ∧
                          accepts fuel (infer fuel env ctx (ghost || proof) init) (.app motive (.natural 0)) = true ∧
                          accepts fuel (infer fuel env ctx (ghost || proof) body) (loopBodyType n motive proof) = true ∧
                          iterationBodyOK env body = true
                      then some (.app motive n) else none
                    else none
                | none => none
              else none
          | _ => none
      | .node (.global g) [] =>
          (env.globals[g]?).map fun declaration =>
            declaration.type.rename (fun x => x + ctx.length)
      | .node (.ind f count) xs =>
          match env.families[f]? with
          | some entry =>
              if count = entry.declaration.arity ∧ xs.length = count ∧
                  xs.all (fun x => accepts fuel (infer fuel env ctx true x) .u64) = true
              then some (if entry.declaration.data then .univ 0 else .prop) else none
          | none => none
      | .node (.con f k count) xs =>
          match env.families[f]? with
          | some entry =>
              match entry.signatures[k]? with
              | some signature =>
                  if count = xs.length then
                    match instantiate (infer fuel env ctx) fuel ghost entry.declaration.data
                        ((signatureTerm f signature).rename (fun x => x + ctx.length)) xs with
                    | some (.node (.ind g arity) indices) =>
                        if g = f then some (.node (.ind f arity) indices) else none
                    | _ => none
                  else none
              | none => none
          | none => none
      | .node (.elim f count) (motive :: children) =>
          match env.families[f]? with
          | some entry =>
              if entry.declaration.data = false then
                match splitCases count children with
                | some (cases, scrutinee) =>
                    if accepts fuel (infer fuel env ctx true motive) (propMotiveType entry.declaration.arity) = true ∧
                        branches (infer fuel env ctx true) fuel motive entry.signatures cases = true then
                      match expose fuel (infer fuel env ctx true scrutinee) with
                      | some (.node (.ind g arity) indices) =>
                          if g = f ∧ arity = entry.declaration.arity then some (applications motive indices)
                          else none
                      | _ => none
                    else none
                | none => none
              else dataEliminate (infer fuel env ctx) fuel env ctx ghost false f count motive children
          | none => none
      | .buffer n =>
          if accepts fuel (infer fuel env ctx true n) .u64 then some (.univ 0) else none
      | .alloc n value =>
          if accepts fuel (infer fuel env ctx ghost n) .u64 = true ∧
              accepts fuel (infer fuel env ctx ghost value) .i64 = true
          then some (.buffer n) else none
      | .store buffer index value proof =>
          match expose fuel (infer fuel env ctx ghost buffer) with
          | some (.buffer n) =>
              if accepts fuel (infer fuel env ctx ghost index) .u64 = true ∧
                  accepts fuel (infer fuel env ctx ghost value) .i64 = true ∧
                  accepts fuel (infer fuel env ctx true proof) (.lt index n) = true
              then some (.buffer n) else none
          | _ => none
      | .load buffer index proof continuation =>
          match expose fuel (infer fuel env ctx ghost buffer) with
          | some (.buffer n) =>
              if accepts fuel (infer fuel env ctx ghost index) .u64 = true ∧
                  accepts fuel (infer fuel env ctx true proof) (.lt index n) = true then
                match expose fuel (infer fuel env ctx ghost continuation) with
                | some (.pi false valueDomain (.pi false ownerDomain result)) =>
                    if Conversion.equal fuel valueDomain .i64 = true ∧
                        Conversion.equal fuel ownerDomain (.buffer (n.rename Nat.succ)) = true then
                      match PartialRenaming.shift (-2) 0 (Conversion.normalize fuel result) with
                      | some outside =>
                          if ghost || nonFunctionHead (Conversion.normalize fuel outside) then some outside else none
                      | none => none
                    else none
                | _ => none
              else none
          | _ => none
      | .free buffer rest =>
          match expose fuel (infer fuel env ctx ghost buffer) with
          | some (.buffer _) => infer fuel env ctx ghost rest
          | _ => none
      | .ref (.buffer n) =>
          if accepts fuel (infer fuel env ctx true n) .u64 then some (.univ 0) else none
      | .borrow owner =>
          if ghost = true then
            match expose fuel (infer fuel env ctx true owner) with
            | some T => if ownedHead env T then some (.ref T) else none
            | _ => none
          else none
      | .deref reference =>
          if ghost = true then
            match expose fuel (infer fuel env ctx true reference) with
            | some (.ref T) => some T
            | _ => none
          else none
      | .back erased owner motive =>
          if accepts fuel (infer fuel env ctx true owner) (.univ 0) = true ∧
              ownedHead env (Conversion.normalize fuel owner) = true ∧
              accepts fuel (infer fuel env ctx true motive) (.pi false owner (loopSortTerm erased)) = true ∧
              backMotiveOK fuel env erased motive = true
          then some (.univ 0) else none
      | .give erased motive owner result =>
          match infer fuel env ctx ghost owner with
          | some T =>
              if ownedHead env (Conversion.normalize fuel T) = true ∧
                  accepts fuel (infer fuel env ctx true motive) (.pi false T (loopSortTerm erased)) = true ∧
                  backMotiveOK fuel env erased motive = true ∧
                  accepts fuel (infer fuel env ctx (ghost || erased) result) (.app motive owner) = true
              then some (.back erased T motive) else none
          | none => none
      | .take value continuation =>
          match expose fuel (infer fuel env ctx ghost value) with
          | some (.back erased owner motive) =>
              match continuation with
              | .lam false declaredOwner (.lam flag declaredResult _body) =>
                  if flag = erased ∧ Conversion.equal fuel declaredOwner owner = true ∧
                      Conversion.equal fuel declaredResult (takeResultType motive) = true then
                    match expose fuel (infer fuel env ctx ghost continuation) with
                    | some (.pi false _inferredOwner (.pi _inferredErased _inferredResult result)) =>
                        match PartialRenaming.shift (-2) 0 (Conversion.normalize fuel result) with
                        | some outside =>
                            if ghost || takeNonFunctionHead (Conversion.normalize fuel outside)
                            then some outside else none
                        | none => none
                    | _ => none
                  else none
              | _ => none
          | _ => none
      | .node (.drop family) [owner, rest] =>
          match env.families[family]? with
          | some entry =>
              if entry.boxed then
                match expose fuel (infer fuel env ctx ghost owner) with
                | some (.node (.ind g _) _) => if g = family then infer fuel env ctx ghost rest else none
                | _ => none
              else none
          | _ => none
      | .ref owner =>
          if accepts fuel (infer fuel env ctx true owner) (.univ 0) = true ∧
              ownedHead env (Conversion.normalize fuel owner) = true
          then some (.univ 0) else none
      | .node (.caseOf family count) (motive :: children) =>
          dataEliminate (infer fuel env ctx) fuel env ctx ghost true family count motive children
      | _ => none

  /-- Infer the domain sort and enforce Core.binder's pure binder policy. -/
  def binder : Nat → Environment → Context → Bool → Term → Option SortTag
    | 0, _, _, _, _ => none
    | fuel + 1, env, ctx, erased, domain =>
      match expose fuel (infer fuel env ctx true domain) with
      | some T =>
          match SortTag.ofTerm T with
          | some s => if binderOK fuel env erased domain s then some s else none
          | none => none
      | none => none
end

/-- Native require with verified conversion; no derivation input. -/
def check (fuel : Nat) (env : Environment) (ctx : Context) (ghost : Bool) (term expected : Term) : Bool :=
  accepts fuel (infer fuel env ctx ghost term) expected

def sort (fuel : Nat) (env : Environment) (ctx : Context) (ty : Term) : Option SortTag :=
  (expose fuel (infer fuel env ctx true ty)).bind SortTag.ofTerm

def isType (fuel : Nat) (env : Environment) (ctx : Context) (ty : Term) : Bool := (sort fuel env ctx ty).isSome

@[simp] theorem infer_zero (ctx : Context) (ghost : Bool) (term : Term) :
    infer 0 env ctx ghost term = none := rfl
@[simp] theorem binder_zero (ctx : Context) (erased : Bool) (domain : Term) :
    binder 0 env ctx erased domain = none := rfl

end Jihoo.NativeKernel.Environment.Checker
