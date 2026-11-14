import Jihoo.NativeTyping
import Jihoo.NativePartialRenaming

/-! Data-input executable checking on the complete native constructor syntax.
Type comparison uses verified bounded conversion. Global/family
environments and ownership rules are not silently
assumed: operators without a rule below reject. -/
namespace Jihoo.NativeKernel.Checker

/-- Verified conversion of an actual inferred type to an expected type. -/
def accepts (fuel : Nat) (inferred : Option Term) (expected : Term) : Bool :=
  match inferred with
  | some actual => Conversion.equal fuel actual expected
  | none => false

/-- Normalize an inferred type before inspecting its head constructor. -/
def expose (fuel : Nat) (inferred : Option Term) : Option Term :=
  inferred.map (Conversion.normalize fuel)

/-- The executable binder policy proves the independent declarative policy. -/
def binderOK (fuel : Nat) (erased : Bool) (A : Term) (s : SortTag) : Bool :=
  if erased then decide (s = .prop) || Conversion.equal fuel A .u64
  else decide (s ≠ .prop)

/-- Executable native first-order gate after verified normalization. -/
def applicationOK (fuel : Nat) (ghost : Bool) (domain argument : Term) : Bool :=
  ghost || !kindOf domain ||
    (firstOrderKind domain && plain (Conversion.normalize fuel argument))

/-- Read the exact native loop motive sort: Prop or Type0 only. -/
def loopSort : Term → Option Bool
  | .prop => some true
  | .univ 0 => some false
  | _ => none

def loopMotiveOK (fuel : Nat) (proof : Bool) (motive : Term) : Bool :=
  proof || scalarLoopMotive (Conversion.normalize fuel motive)

mutual
  def infer : Nat → Context → Bool → Term → Option Term
    | 0, _, _, _ => none
    | fuel + 1, ctx, ghost, term =>
      match term with
      | .var x =>
          match lookup ctx x with
          | some b => if ghost = true ∨ b.erased = false then some b.ty else none
          | none => none
      | .univ n => if n < 32 then some (.univ (n + 1)) else none
      | .prop | .u64 | .i64 => some (.univ 0)
      | .natural n => if n < 2^64 then some .u64 else none
      | .integer n => if -(2^63 : Int) ≤ n ∧ n < (2^63 : Int) then some .i64 else none
      | .array n => if accepts fuel (infer fuel ctx true n) .u64 = true then some (.univ 0) else none
      | .lt a b | .eq a b =>
          if accepts fuel (infer fuel ctx true a) .u64 = true ∧ accepts fuel (infer fuel ctx true b) .u64 = true
          then some .prop else none
      | .pi e A B =>
          match binder fuel ctx e A with
          | some s =>
              match expose fuel (infer fuel (⟨A, e⟩ :: ctx) true B) with
              | some T => (SortTag.ofTerm T).map fun r => (s.pi r).term
              | none => none
          | none => none
      | .lam e A body =>
          match binder fuel ctx e A with
          | some _ => (infer fuel (⟨A, e⟩ :: ctx) ghost body).map (Term.pi e A)
          | none => none
      | .app f a =>
          match expose fuel (infer fuel ctx ghost f) with
          | some (.pi e A B) =>
              if accepts fuel (infer fuel ctx (ghost || e) a) A = true ∧ applicationOK fuel ghost A a = true ∧ Conversion.substitutionSafe B a = true
              then some (B.subst (fun | 0 => a | n + 1 => .var n)) else none
          | _ => none
      | .uadd a b =>
          if accepts fuel (infer fuel ctx ghost a) .u64 = true ∧ accepts fuel (infer fuel ctx ghost b) .u64 = true
          then some .u64 else none
      | .usub a b p =>
          if accepts fuel (infer fuel ctx ghost a) .u64 = true ∧ accepts fuel (infer fuel ctx ghost b) .u64 = true ∧
              accepts fuel (infer fuel ctx true p) (.lt b (.uadd a (.natural 1))) = true
          then some .u64 else none
      | .refl a => if accepts fuel (infer fuel ctx true a) .u64 = true then some (.eq a a) else none
      | .zeroLe a => if accepts fuel (infer fuel ctx true a) .u64 = true
          then some (.lt (.natural 0) (.uadd a (.natural 1))) else none
      | .decide a b =>
          if accepts fuel (infer fuel ctx true a) .u64 = true ∧
              accepts fuel (infer fuel ctx true b) .u64 = true then
            match Conversion.normalize fuel a, Conversion.normalize fuel b with
            | .natural m, .natural n =>
                if m < 2^64 ∧ n < 2^64 ∧ m < n then some (.lt a b) else none
            | _, _ => none
          else none
      | .elements n xs =>
          if xs.length = n ∧ xs.length < 2^64 ∧
              xs.all (fun x => accepts fuel (infer fuel ctx ghost x) .i64) = true
          then some (.array (.natural xs.length)) else none
      | .index a i p =>
          match expose fuel (infer fuel ctx ghost a) with
          | some (.array n) =>
              if accepts fuel (infer fuel ctx ghost i) .u64 = true ∧ accepts fuel (infer fuel ctx true p) (.lt i n) = true
              then some .i64 else none
          | _ => none
      | .arith _op a b =>
          if accepts fuel (infer fuel ctx ghost a) .i64 = true ∧ accepts fuel (infer fuel ctx ghost b) .i64 = true
          then some .i64 else none
      | .strict a b =>
          match expose fuel (infer fuel ctx ghost a) with
          | some _ => infer fuel ctx ghost b
          | none => none
      | .ltAdd a b c p =>
          if accepts fuel (infer fuel ctx true a) .u64 = true ∧ accepts fuel (infer fuel ctx true b) .u64 = true ∧
              accepts fuel (infer fuel ctx true c) .u64 = true ∧ accepts fuel (infer fuel ctx true p) (.lt a b) = true
          then some (.lt (.uadd a c) (.uadd b c)) else none
      | .ltCancel a b c p =>
          if accepts fuel (infer fuel ctx true a) .u64 = true ∧ accepts fuel (infer fuel ctx true b) .u64 = true ∧
              accepts fuel (infer fuel ctx true c) .u64 = true ∧
              accepts fuel (infer fuel ctx true p) (.lt (.uadd a c) (.uadd b c)) = true
          then some (.lt a b) else none
      | .ltLe a b c p q =>
          if accepts fuel (infer fuel ctx true a) .u64 = true ∧ accepts fuel (infer fuel ctx true b) .u64 = true ∧
              accepts fuel (infer fuel ctx true c) .u64 = true ∧ accepts fuel (infer fuel ctx true p) (.lt a b) = true ∧
              accepts fuel (infer fuel ctx true q) (.lt b (.uadd c (.natural 1))) = true
          then some (.lt a c) else none
      | .transport f e p =>
          match expose fuel (infer fuel ctx true e) with
          | some (.eq a b) =>
              if accepts fuel (infer fuel ctx true f) (.pi false .u64 .prop) = true ∧
                  accepts fuel (infer fuel ctx true p) (.app f a) = true
              then some (.app f b) else none
          | _ => none
      | .refine p => if accepts fuel (infer fuel ctx true p) (.pi false .u64 .prop) = true
          then some (.univ 0) else none
      | .pack p a q =>
          if accepts fuel (infer fuel ctx true p) (.pi false .u64 .prop) = true ∧
              accepts fuel (infer fuel ctx ghost a) .u64 = true ∧ accepts fuel (infer fuel ctx true q) (.app p a) = true
          then some (.refine p) else none
      | .witness s =>
          match expose fuel (infer fuel ctx ghost s) with
          | some (.refine _p) => some .u64
          | _ => none
      | .proof s =>
          match expose fuel (infer fuel ctx true s) with
          | some (.refine p) => some (.app p (.witness s))
          | _ => none
      | .ifLt a b yes no =>
          if accepts fuel (infer fuel ctx ghost a) .u64 = true ∧
              accepts fuel (infer fuel ctx ghost b) .u64 = true then
            match expose fuel (infer fuel (⟨.lt a b, true⟩ :: ctx) ghost yes) with
            | some Y =>
                match PartialRenaming.shift (-1) 0 Y with
                | some B => if accepts fuel (infer fuel ctx ghost no) B then some B else none
                | none => none
            | none => none
          else none
      | .ifEq a b yes no =>
          if accepts fuel (infer fuel ctx ghost a) .u64 = true ∧
              accepts fuel (infer fuel ctx ghost b) .u64 = true then
            match expose fuel (infer fuel (⟨.eq a b, true⟩ :: ctx) ghost yes) with
            | some Y =>
                match PartialRenaming.shift (-1) 0 Y with
                | some B => if accepts fuel (infer fuel ctx ghost no) B then some B else none
                | none => none
            | none => none
          else none
      | .absurd T p =>
          match expose fuel (infer fuel ctx true T) with
          | some U =>
              match SortTag.ofTerm U with
              | some _ =>
                  if nonFunctionHead (Conversion.normalize fuel T) then
                    match expose fuel (infer fuel ctx true p) with
                    | some (.lt _i n) =>
                        if Conversion.equal fuel n (.natural 0) then some T else none
                    | _ => none
                  else none
              | none => none
          | none => none
      | .fold n init body =>
          if accepts fuel (infer fuel ctx ghost n) .u64 = true ∧
              accepts fuel (infer fuel ctx ghost init) .i64 = true ∧
              accepts fuel (infer fuel ctx ghost body) (foldBodyType n) = true ∧
              repeatPure body = true
          then some .i64 else none
      | .loop n motive init body =>
          match expose fuel (infer fuel ctx true motive) with
          | some (.pi false domain level) =>
              if Conversion.equal fuel domain .u64 then
                match loopSort level with
                | some proof =>
                    if loopMotiveOK fuel proof motive then
                      if accepts fuel (infer fuel ctx (ghost || proof) n) .u64 = true ∧
                          accepts fuel (infer fuel ctx (ghost || proof) init) (.app motive (.natural 0)) = true ∧
                          accepts fuel (infer fuel ctx (ghost || proof) body) (loopBodyType n motive proof) = true ∧
                          repeatPure body = true
                      then some (.app motive n) else none
                    else none
                | none => none
              else none
          | _ => none
      | _ => none

  /-- Infer the domain sort and enforce Core.binder's pure binder policy. -/
  def binder : Nat → Context → Bool → Term → Option SortTag
    | 0, _, _, _ => none
    | fuel + 1, ctx, erased, domain =>
      match expose fuel (infer fuel ctx true domain) with
      | some T =>
          match SortTag.ofTerm T with
          | some s => if binderOK fuel erased domain s then some s else none
          | none => none
      | none => none
end

/-- Native require with verified conversion; no derivation input. -/
def check (fuel : Nat) (ctx : Context) (ghost : Bool) (term expected : Term) : Bool :=
  accepts fuel (infer fuel ctx ghost term) expected

def sort (fuel : Nat) (ctx : Context) (ty : Term) : Option SortTag :=
  (expose fuel (infer fuel ctx true ty)).bind SortTag.ofTerm

def isType (fuel : Nat) (ctx : Context) (ty : Term) : Bool := (sort fuel ctx ty).isSome

@[simp] theorem infer_zero (ctx : Context) (ghost : Bool) (term : Term) :
    infer 0 ctx ghost term = none := rfl
@[simp] theorem binder_zero (ctx : Context) (erased : Bool) (domain : Term) :
    binder 0 ctx erased domain = none := rfl

end Jihoo.NativeKernel.Checker
