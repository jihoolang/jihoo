import Jihoo.NativeDataSyntax
import Jihoo.NativeEnvironmentConversion

/-! Borrowed data telescopes derived from the same checked canonical signature.
The plan is compiled before parameter substitution: its ownership decisions do
not inspect arbitrary substituted terms. All external family decisions require
an actual lookup; unresolved aliases and families fail explicitly. -/
namespace Jihoo.NativeKernel.Environment

structure ViewFieldPlan where
  field : Field
  borrowed : Bool
  self : Bool
  deriving Repr

/-- Core's heap classification on canonical admitted field domains. Erased
fields are retained without a runtime borrow or recursive result. -/
def viewFieldPlan (env : Environment) (family : Nat) (field : Field) : Option ViewFieldPlan :=
  if field.erased then some ⟨field,false,false⟩ else
  match field.domain with
  | .buffer _ => some ⟨field,true,false⟩
  | .node (.ind g _) _ =>
      if g = family then some ⟨field,true,true⟩ else
        (env.families[g]?).map fun entry => ⟨field,entry.boxed,false⟩
  | .u64 | .i64 | .refine _ => some ⟨field,false,false⟩
  | _ => none

def viewPlan (env : Environment) (family : Nat) (fields : List Field) : Option (List ViewFieldPlan) :=
  fields.mapM (viewFieldPlan env family)

/-- Preserve all binders while reading any previous borrowed field through
Deref. The list is in declaration order, opposite de Bruijn variable order. -/
def viewReadAt (borrowed : List Bool) (x : Nat) : Term :=
  if x < borrowed.length ∧ borrowed[borrowed.length - 1 - x]?.getD false = true
  then .deref (.var x) else .var x

def viewRead (borrowed : List Bool) (term : Term) : Term := term.subst (viewReadAt borrowed)

def viewInstFields (depth : Nat) (ps : List Term) :
    List Bool → List ViewFieldPlan → List (Bool × Term)
  | _, [] => []
  | previous, plan :: plans =>
      let domain := viewRead previous
        (plan.field.domain.subst (parameterAt depth previous.length ps))
      (if plan.borrowed then false else plan.field.erased,
        if plan.borrowed then Term.ref domain else domain) ::
      viewInstFields depth ps (previous ++ [plan.borrowed]) plans

def viewPositions (plans : List ViewFieldPlan) : List Nat :=
  plans.zipIdx.filterMap fun (plan, position) => if plan.self then some position else none

/-- A dependent view is applied to the borrow of the reconstructed constructor.
Its borrowed fields are read through Deref in that reconstructed value. -/
def viewCaseResult (family constructor fields hypotheses : Nat) (ps : List Term)
    (motive : Term) (borrowed : List Bool) (dependent : Bool) : Term :=
  let result := motive.rename (fun x => x + fields + hypotheses)
  if dependent then
    let values := ps.map (Term.rename (fun x => x + fields + hypotheses)) ++
      (List.range fields).map (fun j =>
        let field := Term.var (fields - 1 - j + hypotheses)
        if borrowed[j]?.getD false then Term.deref field else field)
    .app result (.borrow (.node (.con family constructor values.length) values))
  else result

def viewHypothesisType (fields : Nat) (motive : Term) (dependent : Bool) (position q : Nat) : Term :=
  let result := motive.rename (fun x => x + fields + q)
  if dependent then .app result (.var (fields + q - 1 - position)) else result

def viewHypothesisTelescope (fields offset : Nat) (positions : List Nat)
    (motive : Term) (dependent : Bool) (body : Term) : Term :=
  (positions.zipIdx offset).foldr (fun (position,q) result =>
    .pi false (viewHypothesisType fields motive dependent position q) result) body

/-- Core.view_case_type with parameter substitution, preserved field scopes,
borrowed heap fields, and runtime hypotheses for recursive self fields. -/
def viewCaseType (env : Environment) (family constructor params depth : Nat)
    (signature : Signature) (ps : List Term) (motive : Term)
    (recursion dependent : Bool) : Option Term := do
  if ps.length != params || params > signature.fields.length then none else
  let plans ← viewPlan env family (signature.fields.drop params)
  let fields := plans.length
  let positions := if recursion then viewPositions plans else []
  let result := viewCaseResult family constructor fields positions.length ps motive
    (plans.map ViewFieldPlan.borrowed) dependent
  some (closeDataFields (viewInstFields depth ps [] plans)
    (viewHypothesisTelescope fields 0 positions motive dependent result))

def viewCaseTypes (env : Environment) (family params depth : Nat) (signatures : List Signature)
    (ps : List Term) (motive : Term) (recursion dependent : Bool) : Option (List Term) :=
  signatures.zipIdx.mapM fun (signature,constructor) =>
    viewCaseType env family constructor params depth signature ps motive recursion dependent

def viewMotiveType (dependent : Bool) (owner : Term) : Term :=
  if dependent then .pi false (.ref owner) (.univ 0) else .univ 0

def viewResult (dependent : Bool) (motive scrutinee : Term) : Term :=
  if dependent then .app motive scrutinee else motive

/-- The motive binder and any returned Pi binders are all removed when
checking an array length's fixed representation. -/
def viewRepresentation : Nat → Nat → Term → Bool
  | 0, _, _ => false
  | fuel + 1, binders, .pi _ _ rest => viewRepresentation fuel (binders + 1) rest
  | _ + 1, binders, .array length => (PartialRenaming.shift (-(Int.ofNat binders)) 0 length).isSome
  | _ + 1, _, .i64 | _ + 1, _, .u64 | _ + 1, _, .refine _ |
      _ + 1, _, .buffer _ | _ + 1, _, .node (.ind _ _) _ => true
  | _ + 1, _, _ => false

end Jihoo.NativeKernel.Environment
