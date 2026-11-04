# Verifier soundness proofs

`nix build .#checks.x86_64-linux.adequacy` runs `check.sh`: from the current
source it generates the theory (`Theory.agda`), the certificate
`lib/proof/refine.jh` produces that `compiler/linear.jh`'s `check` is sound,
and that certificate's Agda export (`CheckCertificate.agda`, written by
Horn's `schematic-kernel --agda`), then checks `CertifiedRemoval.agda` with
Agda's `--safe` mode. This imports `Certified.agda`, whose theorem has no
certificate-validity premise: when the Horn relation for `check` returns
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
- `CertifiedRemoval.agda`: an accepted linear certificate discharges a
  semantic guard condition from `CheckRemoval.agda`, provided the path's
  facts hold in every invariant state and a failing guard makes the claim
  negative. Its constructors also require the successful continuation to
  preserve the next invariant. The checker's acceptance is still a Horn
  relation; execution-to-Horn correspondence is not assumed proved.

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

## Semantic check removal

`nix build .#checks.x86_64-linux.check-removal` runs `check-removal.sh`:

- `CheckRemoval.agda` defines a control-flow graph with assertions,
  guarded primitive operations, branches, jumps, returns and traps. State,
  events and primitive effects are parameters. `vc` constructs the local
  semantic conditions for a proposed invariant and removal mask.
- `forward` and `backward` establish one-step correspondence, preserving
  the invariant, after replacing an assertion by a jump or a checked
  operation by its unchecked form. `forward-run`, `backward-run` and
  `from-entry` preserve finite traces and final configurations in both
  directions, including observable effects and failures of retained
  checks. Cyclic graphs need no iteration bound or termination proof.
- `CheckRemovalExamples.agda` instantiates the theorem with an observable
  countdown loop with a zero-result postcondition, a cycle, an arbitrary
  state-changing operation, retained failing checks and a trap. `reject/`
  contains invalid conditions for
  removing a false guard, keeping an invariant after an arbitrary write,
  ignoring a branch, and returning without establishing the postcondition.
  Agda must reject each with a type mismatch;
  missing imports or other tool failures do not count as rejection.

This is a semantic specification and its soundness proof, not yet a proof
of the implementation in `obligations.jh`, `vc.jh` or `verify.jh`. Primitive
checked operations are defined as guarded unchecked operations; connecting
that definition to integer widths, wrapping arithmetic and memory is still
required. Calls with contracts, recursion through contracts, mutable borrow
and type-invariant reasoning, incomplete analysis, panic removal and call
retargeting are not proved by this core. They must be connected before the
0.5.0 release gate is met. Source-to-MIR and MIR-to-LLVM preservation also
remain separate compiler-correctness obligations, with LLVM trusted.

Use the matching system attribute on aarch64. All three checks are part of
`nix flake check`. For all proof tools and the pinned Horn source:

```sh
nix develop .#proofs
jihoo build -O2 compiler/main.jh -o out/jihoo
JIHOO=out/jihoo bash agda/check.sh
bash agda/check-removal.sh
```

`check.sh` uses Horn's `schematic-kernel` on `PATH` (or
`SCHEMATIC_KERNEL`), and both scripts use `HORN` for the Horn checkout.

The execution-to-Horn and verification-condition-generation proofs remain
separate release requirements in the [roadmap](../docs/internals/roadmap.md).
