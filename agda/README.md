# Verifier soundness proofs

`nix build .#checks.x86_64-linux.adequacy` runs `check.sh`: from the current
source it generates the theory (`Theory.agda`), the certificate
`lib/proof/refine.jh` produces that `compiler/linear.jh`'s `check` is sound,
and that certificate's Agda export (`CheckCertificate.agda`, written by
Horn's `schematic-kernel --agda`), then checks `Certified.agda` with Agda's
`--safe` mode. The theorem it proves has no premise: when `check` returns
`Ok`, no integer point satisfies the facts and the negated claim.

- `CheckCertificate.agda`: Agda decodes the certificate and runs Horn's
  checker for implicational certificates (Horn's
  `agda/ImplicationCheck.agda`) on it, by evaluation, once
  (`accepted = refl`). That checker is proved sound in every model of the
  rules, so `theorem` holds in each. The exporter is untrusted: whatever it
  writes must still be accepted for the stated goal.
- `Adequacy.agda`: the theory's model in an ordered commutative ring, and
  `sound`, which turns `Valid goalH goalJ` there into the statement about
  `check`.
- `Certified.agda`: `theorem` in that model gives `Valid goalH goalJ`.
  The certificate's signature gives sorts to all of its variables,
  Adequacy's to the goal's five; Horn's `Transfer` moves the model across
  because the two agree on every symbol and on the goal's variables. The
  rules and the goal are the same terms in both, which Agda checks by
  conversion. `InIntegers` is the theorem for `Integers.agda`'s ring.

What remains trusted here: Agda, Horn's Agda development, and the
translation of MIR into the rules (`compiler/horn.jh`) with `std`'s `Vec`
as the rules' lists. jihoo's own Horn checker (`lib/proof/schematic.jh`)
and the Rust one are not: the certificate is checked by Agda.

`nix build .#checks.x86_64-linux.certificate` keeps the theory, goals,
certificate and Agda export for other consumers, and checks the
certificate with the pinned Horn Rust checker as well. The output
directory holds:

- `check.horn`: the rules generated from MIR;
- `check.theory`: the complete theory, including the proof's helper rules;
- `check.goals`: the expected soundness statement;
- `check.proof`: the actual certificate produced by `proof.refine`;
- `CheckCertificate.agda`: its Agda export;
- `checked.txt`: the Rust checker's acceptance report;
- `missing-rejected.txt` and `wrong-rejected.txt`: rejection reports for
  removing the result and replacing its reference with the wrong fact.

Use the matching system attribute on aarch64. Both checks are part of
`nix flake check`. To run `check.sh` by hand, put Horn's `schematic-kernel`
on `PATH` (or set `SCHEMATIC_KERNEL`) and Horn's checkout in `HORN`.

The execution-to-Horn and verification-condition-generation proofs remain
separate release requirements in the [roadmap](../docs/internals/roadmap.md).
