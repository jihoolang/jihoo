import Jihoo.TypedBetaReplayCodec

namespace Jihoo.GraphCertificates.TypedBeta.Examples
open CoreBridge CoreBridge.Raw Typing.Wire

private def typing : Typing.Certificate := {
  graph := #[.u64, .var 0, .lam false 0 1, .natural 7, .app 2 3, .pi false 0 0]
  termRoot := 4, typeRoot := 0, typingStep := 4, formationStep := 0
  steps := [⟨0, [], 0, 0, []⟩, ⟨10, [0], 1, 0, []⟩,
    ⟨19, [], 2, 5, [0, 1]⟩, ⟨11, [], 3, 0, []⟩, ⟨20, [], 4, 0, [2, 3]⟩] }
private def before : Snapshot := ⟨4, 0, typing.graph⟩
private def after : Snapshot := ⟨3, 0, typing.graph⟩
private def replay : Certificate := ⟨before, after, []⟩

theorem head_contract :
    (contract [] (.app (.lam false .u64 (.var 0)) (.natural 7))).isSome = true := by
  simp [contract, Typing.substitutionSafe, Typing.rawSize, Typing.rawDepth,
    treeLimit, depthLimit]

theorem no_redex : (contract [] (.natural 7)).isSome = false := by decide +kernel

theorem output_typed (h : validate before after typing [] replay = true) :
    Sound before after [] := (validate_sound h).2

theorem wrong_path_rejected :
    validate before after typing [1] replay = false := by decide +kernel

theorem replay_roundtrip : Wire.decode (Wire.encode replay) = some replay :=
  Wire.decode_encode _

private def redex : Raw := .app (.lam false .u64 (.var 0)) (.natural 7)

#eval show IO Unit from do
  unless Wire.validateBytes (encodeSnapshot before) (encodeSnapshot after)
      (Typing.Wire.encode typing) (Wire.encode replay) [] do
    throw (IO.userError "closed typed beta replay rejected")
  if validate before before typing [] ⟨before, before, []⟩ then
    throw (IO.userError "convertible non-step accepted")
  -- Every contextual Step constructor has an executable path case. These
  -- structural tests deliberately do not assert typing for every raw context.
  let contexts : List (Raw × List Nat) := [
    (.array redex, [0]),
    (.lt redex redex, [0]),
    (.lt redex redex, [1]),
    (.eq redex redex, [0]),
    (.eq redex redex, [1]),
    (.pi false redex redex, [0]),
    (.pi false redex redex, [1]),
    (.lam false redex redex, [0]),
    (.lam false redex redex, [1]),
    (.app redex redex, [0]),
    (.app redex redex, [1]),
    (.index redex redex redex, [0]),
    (.index redex redex redex, [1]),
    (.index redex redex redex, [2]),
    (.refl redex, [0]),
    (.zeroLe redex, [0]),
    (.decide redex redex, [0]),
    (.decide redex redex, [1]),
    (.uadd redex redex, [0]),
    (.uadd redex redex, [1]),
    (.usub redex redex redex, [0]),
    (.usub redex redex redex, [1]),
    (.usub redex redex redex, [2]),
    (.elements [.integer 0, redex, .integer 2], [1])]
  for (t, path) in contexts do
    unless (contract path t).isSome do throw (IO.userError "contextual constructor rejected")
  if (contract [3] (.elements [redex])).isSome then
    throw (IO.userError "out-of-range element accepted")
  if (contract [] (.natural 7)).isSome then throw (IO.userError "non-redex accepted")
  let huge := Raw.elements (List.replicate 100000 (.natural 0))
  if (contract [] (.app (.lam false .u64 (.uadd (.var 0) (.var 0))) huge)).isSome then
    throw (IO.userError "expanding substitution accepted")
  let shared : Graph := #[.natural 7] ++
    ((List.range 18).map (fun n => Node.uadd n n)).toArray
  if graphValid shared then throw (IO.userError "repeated DAG expansion accepted")

end Jihoo.GraphCertificates.TypedBeta.Examples
