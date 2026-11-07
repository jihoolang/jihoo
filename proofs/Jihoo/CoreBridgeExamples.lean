import Jihoo.CoreBridgeLayout

namespace Jihoo.CoreBridge

private def zero : Index := .lit ⟨0, by decide⟩
private def one : Index := .lit ⟨1, by decide⟩
private def three : Signed := ⟨3, by decide⟩
private def seven : Signed := ⟨7, by decide⟩

def identityProof : Term := .lam (.refl (.var 0))
def mixedProof : Term :=
  .lam (.letValue (.eq (.var 0) (.var 0)) (.refl (.var 0)) (.lam (.var 0)))
def nestedValues : Term := .letValue .i64 (.integer seven)
  (.letValue .i64 (.integer three) (.var 1))
def arrayRead : Term := .letValue (.array one) (.elements [three])
  (.index (.var 0) zero (.decide ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)))

example : identityProof.Scoped 0 0 := by simp [identityProof, Term.Scoped, Index.Scoped]
example : mixedProof.Scoped 0 0 := by simp [mixedProof, Term.Scoped, Ty.Scoped, Index.Scoped]
example : nestedValues.Scoped 0 0 := by simp [nestedValues, Term.Scoped, Ty.Scoped]
example : arrayRead.Scoped 0 0 := by simp [arrayRead, Term.Scoped, Ty.Scoped, Index.Scoped, zero, one]

-- The bridge input also has an explicit connection to the proved calculus.
-- The typed bridge and its independent target theorem are in CoreBridgeTyping.
example : Indexed.ScopedTyping 0 [] mixedProof.erase
    (.pi (.pi (.eq (.var 1) (.var 1)))) := by
  refine ⟨by simp, ?_, ?_, .lam (.letValue (.refl _ _) (.lam (.param _ _)))⟩
  · simp [mixedProof, Term.erase, Index.erase, Indexed.Term.Scoped, Arithmetic.Expr.Scoped]
  · simp [Indexed.Ty.Scoped, Arithmetic.Expr.Scoped]

-- The evidence variable is behind a new index binder in the unified context.
example : mixedProof.encode id id =
    .lam false .u64 (.app (.lam true (.eq (.var 0) (.var 0))
      (.lam false .u64 (.var 1))) (.refl (.var 0))) := rfl

example : nestedValues.encode id id =
    .app (.lam false .i64 (.app (.lam false .i64 (.var 1)) (.integer 3))) (.integer 7) := rfl

example : slot .index 0 [.value, .index, .value] = 1 := rfl
example : slot .value 0 [.value, .index, .value] = 0 := rfl
example : slot .value 1 [.value, .index, .value] = 2 := rfl
example : slot .index 0 [.value, .index] ≠ slot .value 0 [.value, .index] :=
  slots_disjoint (by decide) (by decide)

example : Index.ofExpr (.lit wordBound) = none := by decide
example : word? wordBound = none := by decide
example : word? (wordBound - 1) = some ⟨wordBound - 1, by decide⟩ := by decide
example : Index.ofExpr (.sub (.var 0) (.lit 1)) = none := rfl
example : Index.ofExpr (.sub (.lit 0) (.lit 1)) = none := by decide
-- The maximum left operand would need an unrepresentable Decide endpoint.
example : Index.ofExpr (.sub (.lit (wordBound - 1)) (.lit 0)) = none := by decide
example : (Index.closedSub 10 3 (by decide) (by decide)).encode id =
    .usub (.natural 10) (.natural 3) (.decide (.natural 3) (.natural 11)) := rfl

private def form (head : String) (args : List String) : String :=
  "(" ++ head ++ (if args.isEmpty then "" else " " ++ String.intercalate " " args) ++ ")"

/-- A bounded, fallible textual serializer. Its agreement with the actual
parser is tested by the generated fixture, not proved in Lean. -/
def Raw.render : Nat → List String → Raw → Option String
  | 0, _, _ => none
  | fuel + 1, names, term =>
    let render := Raw.render fuel names
    match term with
    | .var n => names[n]?
    | .natural n => some (toString n)
    | .integer n => some (form "int" [toString n])
    | .u64 => some "U64"
    | .i64 => some "I64"
    | .array a => do return form "Array" [← render a]
    | .lt a b => do return form "Lt" [← render a, ← render b]
    | .eq a b => do return form "Eq" [← render a, ← render b]
    | .pi erased A B => do
        let name := "x" ++ toString names.length
        return form (if erased then "pi0" else "pi")
          [name, ← render A, ← Raw.render fuel (name :: names) B]
    | .lam erased A body => do
        let name := "x" ++ toString names.length
        return form (if erased then "lam0" else "lam")
          [name, ← render A, ← Raw.render fuel (name :: names) body]
    | .app f a => do return form "app" [← render f, ← render a]
    | .elements xs => do return form "array" (← xs.mapM render)
    | .index a i p => do return form "index" [← render a, ← render i, ← render p]
    | .refl a => do return form "refl" [← render a]
    | .zeroLe a => do return form "zero-le" [← render a]
    | .decide a b => do return form "decide-lt" [← render a, ← render b]
    | .uadd a b => do return form "uadd" [← render a, ← render b]
    | .usub a b p => do return form "usub" [← render a, ← render b, ← render p]

def examples : List (String × Ty × Term) := [
  ("bridge_identity", .pi (.eq (.var 0) (.var 0)), identityProof),
  ("bridge_mixed", .pi (.pi (.eq (.var 1) (.var 1))), mixedProof),
  ("bridge_nested_values", .i64, nestedValues),
  ("bridge_dependent_application", .eq (.lit ⟨7, by decide⟩) (.lit ⟨7, by decide⟩),
    .app identityProof (.lit ⟨7, by decide⟩)),
  ("bridge_nested_dependent_application", .pi (.eq (.lit ⟨7, by decide⟩) (.lit ⟨7, by decide⟩)),
    .app mixedProof (.lit ⟨7, by decide⟩)),
  ("bridge_array_read", .i64, arrayRead),
  ("bridge_subtraction", .u64, .natural (.closedSub 10 3 (by decide) (by decide))),
  ("bridge_maximum", .u64, .natural (.lit ⟨wordBound - 1, by decide⟩)),
  ("bridge_add_overflow", .u64, .natural (.add (.lit ⟨wordBound - 1, by decide⟩) one)),
  ("bridge_last_endpoint", .u64,
    .natural (.closedSub (wordBound - 2) (wordBound - 2) (by decide) (by decide))),
  ("bridge_signed_minimum", .i64, .integer ⟨-signedBound, by decide⟩),
  ("bridge_signed_maximum", .i64, .integer ⟨signedBound - 1, by decide⟩)]

def generatedProgram : Option String := do
  let declarations ← examples.mapM fun (name, A, t) => do
    return form "def" [name, ← (A.encode id).render 1024 [], ← (t.encode id id).render 1024 []]
  return "; Generated by proofs/EmitCore.lean. Do not edit by hand.\n" ++
    "; Typed declarative bridge fixture: no executable-checker refinement theorem.\n" ++
    String.intercalate "\n" declarations ++ "\n"

end Jihoo.CoreBridge
