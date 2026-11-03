# Verifier soundness proofs

`nix build .#checks.x86_64-linux.adequacy` checks `Integers.agda` with
Agda's `--safe` mode. It establishes the interpretation of the generated
theory in the integers. Its `sound` theorem still takes
`Valid goalH goalJ` as a premise; this command does not check the actual
36,631-step certificate in Agda.

`nix build .#checks.x86_64-linux.certificate` generates the actual proof
from the current `compiler/linear.jh` and checks it with the pinned Horn
Rust checker, separately from jihoo's checker. The output directory holds:

- `check.horn`: the rules generated from MIR;
- `check.theory`: the complete theory, including the proof's helper rules;
- `check.goals`: the expected soundness statement;
- `check.proof`: the actual certificate produced by `proof.refine`;
- `checked.txt`: the independent checker's acceptance report;
- `missing-rejected.txt` and `wrong-rejected.txt`: rejection reports for
  removing the result and replacing its reference with the wrong fact.

Use the matching system attribute on aarch64. Both checks are part of
`nix flake check`. Generation is separate from checking: consumers must
validate the certificate against the expected theory and goals, rather than
trust the exporter to have checked it.

## Remaining connection to Agda

`ImplicationBridge.agda` now proves the result boundary in every model of
the rules. It converts between the implicational calculus's `ValidR`
with plain hypotheses and the `Valid` interface used by `Adequacy.sound`.
Its `result` lemma permits reordering and contraction only with an explicit
proof that every remaining hypothesis occurs in the stated goal. It cannot
silently drop an assumption or treat a generalized rule hypothesis as a
plain premise. `bridge-check.sh`, run by the adequacy check, checks the
positive examples and requires Agda to reject both of those invalid uses.
This is a proved adapter for the eventual exporter, not the certificate
itself and not a discharge of `Valid goalH goalJ`.

The pinned Horn revision's `schematic-kernel --agda` exporter explicitly
rejects implicational certificates. This proof uses implication goals,
generalized induction hypotheses, `apply` and `invert`; the existing
non-implicational exporter cannot supply `Valid goalH goalJ`.

The next implementation must export those steps with their side conditions
and check them using the soundness results in `Implication.agda` (including
the unification obligations for inversion). It must instantiate the result
in `Adequacy`'s model and connect the exact exported goal to `goalH` and
`goalJ`. Checking the Rust implementation or merely importing the Agda
soundness lemmas is not a substitute for this step. Corrupted proof steps
must also be rejected by Agda itself.

The execution-to-Horn and verification-condition-generation proofs remain
separate release requirements in the [roadmap](../docs/internals/roadmap.md).
