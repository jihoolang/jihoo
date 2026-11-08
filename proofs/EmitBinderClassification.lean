import Jihoo.QuantityBinderProjection
open Jihoo.Quantity.Binders

def main : IO Unit := do
  for erased in [false, true] do
    for (domain, tag) in domains.zipIdx do
      let e := if erased then 1 else 0
      match classify erased domain with
      | none => IO.println s!"{e} {tag} -1 0"
      | some capability =>
        let lend := if capability.lendable then 1 else 0
        IO.println s!"{e} {tag} {modeCode capability.mode} {lend}"
