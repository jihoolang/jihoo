import Jihoo.TypeIndexNormalizationCodec

namespace Jihoo.GraphCertificates.TypeIndexNormalization.Examples
open CoreBridge CoreBridge.Raw Typing.Wire
private def redex : Raw := .app (.lam false .u64 (.var 0)) (.natural 7)
theorem left_first : indexPath (.eq redex redex) = some [0] := rfl
theorem right_next : indexPath (.eq (.natural 7) redex) = some [1] := rfl
theorem no_arithmetic : indexPath (.eq (.uadd (.natural 3) (.natural 4)) (.natural 7)) = none := rfl

#eval show IO Unit from do
  let tiny : Snapshot := ⟨0, 1, #[.natural 7, .u64]⟩
  let large : Snapshot := ⟨0, 1, tiny.graph ++ (List.replicate 4094 Node.prop).toArray⟩
  let phase := List.replicate 3 (TypedBeta.Certificate.mk large large [])
  unless HeadNormalization.budget tiny tiny phase do
    throw (IO.userError "separate node-budget control rejected")
  if HeadNormalization.budget tiny tiny (phase ++ phase) then
    throw (IO.userError "combined phase node budget ignored")
  let shared : Graph := #[.natural 0] ++
    ((List.range 14).map (fun n => Node.uadd n n)).toArray ++ #[.u64]
  let big : Snapshot := ⟨14, 15, shared⟩
  let phase := List.replicate 4 (TypedBeta.Certificate.mk big big [])
  unless HeadNormalization.budget tiny tiny phase do
    throw (IO.userError "separate expanded-work control rejected")
  if HeadNormalization.budget tiny tiny (phase ++ phase) then
    throw (IO.userError "combined phase expanded work ignored")

end Jihoo.GraphCertificates.TypeIndexNormalization.Examples
