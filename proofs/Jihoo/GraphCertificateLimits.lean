import Jihoo.GraphCertificates

/-! Defensive runtime preflight tests, deliberately not kernel theorems about
complexity. Each graph is individually valid; combined substitution is refused. -/
namespace Jihoo.GraphCertificates

private def sharedTree : Graph :=
  #[.var 0, .uadd 0 0, .uadd 1 1, .uadd 2 2, .uadd 3 3,
    .uadd 4 4, .uadd 5 5, .uadd 6 6, .uadd 7 7]

private def deepTree : Graph :=
  #[.var 0] ++ ((List.range 69).map Node.array).toArray

#eval show IO Unit from do
  unless graphValid sharedTree do
    throw (IO.userError "product-guard graph must pass individual limits")
  if substitutionSafe ⟨sharedTree, sharedTree, 8, 8, .substitute 8⟩ 8 then
    throw (IO.userError "substitution product guard did not reject")
  unless graphValid deepTree do
    throw (IO.userError "depth-guard graph must pass individual limits")
  if substitutionSafe ⟨deepTree, deepTree, 69, 69, .substitute 69⟩ 69 then
    throw (IO.userError "substitution depth-sum guard did not reject")

end Jihoo.GraphCertificates
