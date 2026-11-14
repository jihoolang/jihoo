import Jihoo.NativeSyntax

/-! Syntax-only shared global and inductive-family records. Admission evidence
belongs to later modules; constructing these records does not validate them. -/
namespace Jihoo.NativeKernel
namespace Environment
structure GlobalDeclaration where
  type : Term
  value : Term
  deriving Repr
structure FamilyDeclaration where
  data : Bool
  params : Nat
  arity : Nat
  constructors : List Term
  globals : Nat
  deriving Repr
structure Field where
  erased : Bool
  domain : Term
  recursive : Option (List Term)
  deriving Repr
structure Signature where
  fields : List Field
  result : List Term
  deriving Repr
structure CheckedFamily where
  declaration : FamilyDeclaration
  signatures : List Signature
  boxed : Bool
  deriving Repr
end Environment
structure Environment where
  globals : Array Environment.GlobalDeclaration
  families : Array Environment.CheckedFamily
  deriving Repr
namespace Environment
def empty : Environment := ⟨#[], #[]⟩
end Environment
end Jihoo.NativeKernel
