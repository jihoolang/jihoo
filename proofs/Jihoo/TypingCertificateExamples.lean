import Jihoo.TypingCertificateCodec

/-! Closed dependent application and explicit beta/arithmetic conversion.
These are regression data, not compiler-refinement assumptions. -/
namespace Jihoo.GraphCertificates.Typing

private def dependentApplication : Certificate := {
  graph := #[.u64, .var 0, .array 1, .var 1, .array 3,
    .lam false 2 1, .lam false 0 5, .pi false 2 4, .pi false 0 7,
    .natural 1, .array 9, .pi false 10 10, .app 6 9]
  termRoot := 12
  typeRoot := 11
  typingStep := 9
  formationStep := 13
  steps := [
    ⟨0, [], 0, 0, []⟩,
    ⟨10, [0], 1, 0, []⟩,
    ⟨2, [0], 2, 2, [1]⟩,
    ⟨10, [2, 0], 3, 0, []⟩,
    ⟨2, [2, 0], 4, 4, [3]⟩,
    ⟨10, [2, 0], 1, 4, []⟩,
    ⟨19, [0], 5, 7, [2, 5]⟩,
    ⟨19, [], 6, 8, [0, 6]⟩,
    ⟨11, [], 9, 0, []⟩,
    ⟨20, [], 12, 11, [7, 8]⟩,
    ⟨2, [], 10, 10, [8]⟩,
    ⟨11, [10], 9, 0, []⟩,
    ⟨2, [10], 10, 10, [11]⟩,
    ⟨5, [], 11, 11, [10, 12]⟩] }

/-- `[7] : Array (0 + ((λ n : U64 => n) 1))`, certified using explicit
beta, structural congruence, bounded addition, symmetry and transitivity. -/
private def betaArithmetic : Certificate := {
  graph := #[.i64, .integer 7, .elements [1], .natural 1, .array 3,
    .u64, .var 0, .lam false 5 6, .app 7 3, .array 8,
    .pi false 5 5, .natural 0, .uadd 11 8, .uadd 11 3, .array 12]
  termRoot := 2
  typeRoot := 14
  typingStep := 9
  formationStep := 17
  steps := [
    ⟨12, [], 1, 0, []⟩,
    ⟨15, [], 2, 4, [0]⟩,
    ⟨33, [], 8, 3, []⟩,
    ⟨30, [], 11, 11, []⟩,
    ⟨46, [], 12, 13, [3, 2]⟩,
    ⟨34, [], 13, 3, []⟩,
    ⟨32, [], 12, 3, [4, 5]⟩,
    ⟨31, [], 3, 12, [6]⟩,
    ⟨35, [], 4, 14, [7]⟩,
    ⟨21, [], 2, 14, [1, 8]⟩,
    ⟨0, [], 5, 5, []⟩,
    ⟨10, [5], 6, 5, []⟩,
    ⟨19, [], 7, 10, [10, 11]⟩,
    ⟨11, [], 3, 5, []⟩,
    ⟨20, [], 8, 5, [12, 13]⟩,
    ⟨11, [], 11, 5, []⟩,
    ⟨13, [], 12, 5, [15, 14]⟩,
    ⟨2, [], 14, 14, [16]⟩] }

private def literal : Certificate := {
  graph := #[.u64, .natural 7], termRoot := 1, typeRoot := 0,
  typingStep := 1, formationStep := 0,
  steps := [⟨0, [], 0, 0, []⟩, ⟨11, [], 1, 0, []⟩] }

-- Kernel reduction, not `native_decide`, establishes nonvacuity.
theorem literal_accepted : validate literal = true := by decide +kernel
theorem literal_sound : Sound literal := validate_sound (by decide +kernel)
theorem wrong_root_rejected : validate { literal with termRoot := 0 } = false := by decide +kernel
theorem literal_roundtrip : Wire.decode (Wire.encode literal) = some literal := Wire.decode_encode _
theorem snapshot_literal_accepted : Wire.validateAgainstBytes
    (Wire.encodeSnapshot ⟨1, 0, literal.graph⟩) (Wire.encode literal) = true := by decide +kernel

#eval show IO Unit from do
  for c in [dependentApplication, betaArithmetic] do
    unless validate c do throw (IO.userError "valid closed derivation rejected")
    unless Wire.decode (Wire.encode c) == some c do
      throw (IO.userError "typing wire round trip failed")
    let snapshot : Wire.Snapshot := ⟨c.termRoot, c.typeRoot, c.graph⟩
    unless Wire.validateAgainstBytes (Wire.encodeSnapshot snapshot) (Wire.encode c) do
      throw (IO.userError "matching snapshot rejected")
    if Wire.validateAgainst { snapshot with termRoot := c.typeRoot } c then
      throw (IO.userError "wrong snapshot term root accepted")
    if Wire.validateAgainst { snapshot with graph := snapshot.graph.push .prop } c then
      throw (IO.userError "unused snapshot graph mutation accepted")
    if validate { c with typingStep := c.formationStep } then
      throw (IO.userError "formation claim used as typing")
    if validate { c with formationStep := c.typingStep } then
      throw (IO.userError "typing claim used as formation")
    if validate { c with termRoot := c.typeRoot } then
      throw (IO.userError "wrong selected term accepted")
    if validate { c with steps := [] } then
      throw (IO.userError "missing derivation accepted")
    let duplicate := c.steps.headD ⟨0, [], 0, 0, []⟩
    if validate { c with steps := { duplicate with premises := [0] } :: c.steps.tail } then
      throw (IO.userError "forward/self reference or wrong rule arity accepted")
    if Wire.decode ((Wire.encode c).push 10) |>.isSome then
      throw (IO.userError "trailing bytes accepted")
  let closedVar : Certificate := {
    graph := #[.var 0, .u64], termRoot := 0, typeRoot := 1,
    typingStep := 1, formationStep := 0,
    steps := [⟨0, [], 1, 1, []⟩, ⟨10, [], 0, 1, []⟩] }
  if validate closedVar then throw (IO.userError "unbound closed variable accepted")
  let erased := { dependentApplication with
    graph := dependentApplication.graph.set! 6 (.lam true 0 5) }
  if validate erased then throw (IO.userError "erased U64 binder accepted")
  let wrongContext := { dependentApplication with
    steps := dependentApplication.steps.set 5 ⟨10, [0, 2], 1, 4, []⟩ }
  if validate wrongContext then throw (IO.userError "wrong telescope order accepted")
  let shared : Graph := #[.var 0] ++
    ((List.range 16).map (fun n => Node.uadd n n)).toArray
  let repeated : Certificate := {
    graph := shared, termRoot := 16, typeRoot := 16,
    typingStep := 0, formationStep := 0,
    steps := List.replicate 16 ⟨30, [], 16, 16, []⟩ }
  unless graphValid shared do throw (IO.userError "aggregate fixture graph invalid")
  if workSafe repeated then throw (IO.userError "aggregate expansion guard failed")
  if substitutionSafe (.uadd (.var 0) (.var 0))
      (CoreBridge.Raw.elements (List.replicate 100000 (.natural 0))) then
    throw (IO.userError "substitution product guard failed")

end Jihoo.GraphCertificates.Typing
