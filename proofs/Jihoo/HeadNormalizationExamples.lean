import Jihoo.HeadNormalizationCodec

namespace Jihoo.GraphCertificates.HeadNormalization.Examples
open CoreBridge CoreBridge.Raw Typing.Wire

private def typing : Typing.Certificate := {
  graph := #[.u64, .natural 7], termRoot := 1, typeRoot := 0,
  typingStep := 1, formationStep := 0,
  steps := [⟨0, [], 0, 0, []⟩, ⟨11, [], 1, 0, []⟩] }
private def snapshot : Snapshot := ⟨1, 0, typing.graph⟩

private def redex : Raw := .app (.lam false .u64 (.var 0)) (.natural 7)

theorem root_path : headPath redex = some [] := rfl
theorem function_path : headPath (.app redex (.natural 0)) = some [0] := rfl
theorem arguments_not_searched : headPath (.app (.var 0) redex) = none := rfl
theorem bodies_not_searched : headPath (.lam false .u64 redex) = none := rfl

theorem false_bound_rejected : validateLiteral before after c cs (.less n n) = false :=
  false_literal_rejected (Nat.lt_irrefl n)

#eval show IO Unit from do
  unless validate snapshot snapshot typing [] do
    throw (IO.userError "already normal empty witness rejected")
  unless Wire.validateBytes (encodeSnapshot snapshot) (encodeSnapshot snapshot)
      (Typing.Wire.encode typing) (Wire.encode []) do
    throw (IO.userError "empty witness byte roundtrip rejected")
  let dummy : TypedBeta.Certificate := ⟨snapshot, snapshot, []⟩
  if budget snapshot snapshot (List.replicate 65 dummy) then
    throw (IO.userError "step limit ignored")
  let large : Snapshot := ⟨1, 0, typing.graph ++ (List.replicate 4094 Node.prop).toArray⟩
  unless graphValid large.graph do throw (IO.userError "aggregate node fixture invalid")
  if budget snapshot snapshot (List.replicate 5 ⟨large, large, []⟩) then
    throw (IO.userError "repeated graph node budget ignored")
  let shared : Graph := #[.natural 0] ++
    ((List.range 14).map (fun n => Node.uadd n n)).toArray ++ #[.u64]
  let big : Snapshot := ⟨14, 15, shared⟩
  unless graphValid shared do throw (IO.userError "shared DAG fixture invalid")
  unless budget snapshot snapshot [⟨big, big, []⟩] do
    throw (IO.userError "small aggregate budget control rejected")
  if budget snapshot snapshot (List.replicate 9 ⟨big, big, []⟩) then
    throw (IO.userError "repeated expanded roots undercharged")

end Jihoo.GraphCertificates.HeadNormalization.Examples
