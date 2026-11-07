import Jihoo.CheckedCoreNormalizationCodec

namespace Jihoo.GraphCertificates.CoreNormal.Examples
open CoreBridge CoreBridge.Raw Typing.Wire

private def sum : Raw := .uadd (.natural 3) (.natural 4)

theorem literal_add_step : Computation.Step sum (.natural 7) := .add 3 4 (by decide)

theorem evidence_original_type : Beta.HasType (fun _ => none) (.refl (.natural 7)) (.eq sum sum) := by
  have h : Beta.HasType (fun _ => none) (.refl sum) (.eq sum sum) :=
    .refl (.uadd (.natural (by decide)) (.natural (by decide)))
  exact Computation.preservation h (.reflTerm literal_add_step)

theorem overflowing_add_rejected (h : ¬ m + n < wordBound) :
    ¬ Computation.Step (.uadd (.natural m) (.natural n)) u := by
  intro hs
  cases hs with
  | add _ _ hn => exact h hn
  | uaddLeft hs => cases hs
  | uaddRight hs => cases hs

#eval show IO Unit from do
  let some result := run 1 sum | throw (IO.userError "literal addition rejected")
  unless result.val == .natural 7 do throw (IO.userError "literal addition result")
  if (run 0 sum).isSome then throw (IO.userError "total contraction fuel ignored")
  unless (run 0 (.natural 7)).isSome do throw (IO.userError "normal zero-fuel control")
  if (run 64 (.uadd (.var 0) (.natural 1))).isSome then
    throw (IO.userError "symbolic addition admitted")
  if (run 64 (.uadd (.natural (wordBound - 1)) (.natural 1))).isSome then
    throw (IO.userError "overflow admitted")
  let nested := Raw.uadd sum sum
  unless (run 3 nested).isSome do throw (IO.userError "nested addition control rejected")
  if (run 2 nested).isSome then throw (IO.userError "fuel was counted per branch")
  let mut large : Raw := .var 0
  for _ in [:7] do large := .app large large
  let beta := Raw.app (.lam false .u64 large) large
  -- Each side is small and shallow, but substitution expansion exceeds 8192.
  unless Typing.rawSize beta < termLimit do throw (IO.userError "substitution fixture already large")
  if (next beta).isSome then throw (IO.userError "substitution product guard ignored")
  let small := Raw.app (.lam false .u64 (.var 0)) (.natural 7)
  unless (next small).isSome do throw (IO.userError "small beta control rejected")
  let increment := Raw.lam false .u64 (.uadd (.var 0) (.natural 1))
  let closed := Raw.app increment (.natural 6)
  let some closedResult := run 2 closed | throw (IO.userError "closed symbolic lambda rejected")
  unless closedResult.val == .natural 7 do throw (IO.userError "closed increment result")
  if (run 1 closed).isSome then throw (IO.userError "beta/add total fuel ignored")
  -- This is a beta step, not an overflowing addition step: unused input is erased.
  let discard := Raw.app (.lam false .u64 (.natural 7))
    (.uadd (.natural (wordBound - 1)) (.natural 1))
  let some discarded := run 1 discard | throw (IO.userError "discarded argument rejected")
  unless discarded.val == .natural 7 do throw (IO.userError "discarded argument result")
  -- A surviving symbolic body still cannot be certified normal.
  if (run 64 increment).isSome then throw (IO.userError "symbolic lambda admitted")
  let curried := Raw.app
    (.app (.lam false .u64 (.lam false .u64 (.uadd (.var 1) (.var 0)))) (.natural 3))
    (.natural 4)
  let some curriedResult := run 3 curried | throw (IO.userError "curried addition rejected")
  unless curriedResult.val == .natural 7 do throw (IO.userError "capture during curried substitution")
  if (run 2 curried).isSome then throw (IO.userError "curried beta/add fuel ignored")
  -- Root beta must preserve the product guard even if the unexpanded body is
  -- unsupported: changing traversal order must not bypass expansion accounting.
  let hugeBody := Raw.uadd large large
  if (next (.app (.lam false .u64 hugeBody) large)).isSome then
    throw (IO.userError "beta-first symbolic substitution product guard ignored")
  let graph : Graph := #[.u64, .natural 0] ++
    ((List.range 14).map (fun n => Node.uadd (n+1) (n+1))).toArray
  unless graphValid graph do throw (IO.userError "shared graph fixture invalid")
  let some raw := decode graph 15 | throw (IO.userError "shared graph decode control")
  if (run 64 raw).isSome then throw (IO.userError "expanded tree limit ignored")
  let snap : Snapshot := ⟨1, 0, #[.u64, .natural 7]⟩
  let c : Certificate := ⟨snap, snap, 128, 0⟩
  unless Wire.decode (Wire.encode c) == some c do throw (IO.userError "record roundtrip")

end Jihoo.GraphCertificates.CoreNormal.Examples
