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

What remains trusted here for the whole checker: Agda, Horn's Agda
development, and the translation of MIR into the rules (`compiler/horn.jh`) with `std`'s `Vec`
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

## List execution and the Horn model

`nix build .#checks.x86_64-linux.list-execution` runs `check-lists.sh`.
`ListExecution.agda` gives executable finite-list operations and proves
their correspondence to the actual `len`, `nth` and `snoc` relations
generated from `linear.jh`, for its term, fact and weight lists.

For arbitrary well-sorted ground elements, length gives the list's size,
a successful recursive lookup gives its element, and push gives the list
with that element appended. Each result derives the corresponding Horn
judgment in `Adequacy`'s model. The integer expression for an index may be
any ground expression with the same value as its natural index; it need
not have the syntax of the canonical numeral. Numerals' values are proved
to be the corresponding sums of ones in the ordered ring.

The six rule schemas for each list sort must occur in the generated
theory, with their premises, conclusions and variable sorts unchanged.
Agda checks these witnesses by conversion. The script regenerates the
theory from the current compiler, checks integer examples in
`ListExecutionExamples.agda`, and requires rejection of three incorrect
rules: a length increment of zero, indexing the head at one, and a push
that loses its element. Every mutation uses a fresh module directory;
parser errors and missing imports do not count as proof rejection.

This is the finite-list-to-Horn part of the execution bridge. The memory
representation, allocation, capacity bounds, pointer accesses and borrow
behavior of `std.Vec` remain assumptions until connected to these lists.
MIR integer overflow, calls and path-to-rule translation also remain
separate requirements before an execution of the whole checker can be
composed with `Certified.check-sound`.

## Scalar execution and overflow

`nix build .#checks.x86_64-linux.scalar-execution` runs `check-scalars.sh`.
`ScalarExecution.agda` defines executable exact addition and multiplication,
inclusive integer bounds and an overflow decision. Its theorems quantify
over arbitrary bounds; `signed 127` describes i128 without enumerating its
values. Successful results are in range and exact, and rejection means
the exact result is outside the range.

`Overflowing` states the MIR intrinsic contract used by `linear.add` and
`linear.mul`: a false flag gives the exact result, and a true flag means
it did not fit. The overflowed value is discarded by these helpers, so
this projection admits any in-range wrapped value. `projection-correct`
connects the helpers' flag branch to the executable checked operation.
`checked-execution` and `intrinsic-execution` give a numerical
representation of each returned `Option` and derive the corresponding
`fn.add` or `fn.mul` judgment in the generated theory. The result's term
need only have the same integer value, not the same spelling.

Agda finds the actual four helper rules by their full schemas and variable
sorts rather than by fresh names or positions. The Nix check requires
rejection of rules that add instead of multiplying, multiply instead of
adding, or lose an overflow rejection. Examples cover both inclusive
bounds, overflow in either direction, negative products, negating the
minimum and noncanonical integer representations. This is a simulation
into the Horn model, which may also derive extra overflow rejections.
The observable wrapped bits, the LLVM implementation of intrinsics and
general MIR paths/calls remain separate proof obligations.

The same check and the ordinary `verify` suite independently read emitted
signed and unsigned boundary constants and solve switch cases on both
targets (`tests/horn/scalars.py`). This found two translation bugs:
`i128::MIN` made the compiler overflow while constructing its magnitude,
and upper-half `u128` constants were read as negative i128 bit patterns.
The compiler now constructs the minimum's ring expression without that
overflow and interprets integer bits in their source type.

## Exported MIR execution and direct calls

`nix build .#checks.x86_64-linux.mir-execution` runs `check-mir.sh`.
`export-mir.jh` uses the compiler's loader, sema and borrow/drop checker to
export the actual MIR objects of `linear.add`, `linear.mul`, two direct
callers and an accumulator loop appended from `mir-callers.jh`. It retains
every basic block, statement, lifetime marker, branch, call and return in the supported
fragment. It checks signatures, frame/graph bounds and integer types,
and rejects unsupported operations rather than approximating them.

`MirExecution.agda` defines execution with local frames and tuple/Option
values. Lifetime markers clear locals, and an undefined read or invalid
projection cannot return a value. A direct call runs the selected
function's actual graph in a fresh frame, then resumes the caller.
`Run` and `Calls` describe arbitrary finite executions, including recursive
calls. `wp-sound` proves a finite symbolic execution certificate sound;
its fuel bounds the proof computation, not the execution semantics.
`Paths` gives a second proof method: follow each path to a return or an
annotated block, and prove the invariant again after executing that block.
`paths-sound` checks arbitrary finite returning executions by induction,
without bounding how often a loop visits its header or assuming termination.

`MirCorrespondence.agda` checks the signatures and evaluates the exported
graphs to prove that every helper return is the corresponding intrinsic
flag projection. It also constructs a graph execution for every permitted
intrinsic result, so this connection is not vacuous. Direct callers use
the callee's `Run` derivation, rather than an assumed contract. The
returned values have numerical Horn representations, and Agda checks
the actual helper/caller Horn rules used to compose the correspondence.
`InI128` instantiates the intrinsic contract with signed i128 bounds.

`MirLoopCorrespondence.agda` applies `Paths` to the actual `mir_loop`
graph, which repeatedly adds a fixed step until overflow. Given an
initially in-range accumulator, every return gives its last in-range
value, and adding the step to it is out of range. A history of numerical
representations derives the generated loop entry, back-edge and exit
rules, with one `fuel1` per successful iteration. Agda checks their full
schemas and variable sorts. Constructive executions cover any finite
sequence of permitted intrinsic outcomes, so the proof cannot hide a
stuck loop. The overflowed value is discarded, as in the scalar helpers.

Nix regenerates and checks the MIR and Horn theory for both targets.
Five negative cases change the operation, overflow return, direct callee,
local lifetime or caller Horn rule. Each must fail with a type mismatch
in the correspondence proof. A wrapping arithmetic operation must be
rejected by the exporter. Six more negative cases change the loop's
operation, returned value, accumulator update, overflow branch or Horn
step, or remove its Horn exit. Positive examples contain actual returning
callee/caller executions, overflow rejection and stale-read checks, and
immediate and multiple-iteration loop returns in both directions, including
numerically equal integer representations. A pure cycle cannot return,
even with an uninhabited postcondition.
Small-bound examples test control flow; they do not claim that the
native i128 operation overflows at those small bounds.

The output retains `GeneratedMir.agda`, `Theory.agda` and `program.horn`
under `x86_64/` and `aarch64/` for review. The MIR serializer
(`export-mir.jh`) and compiler frontend are still trusted to supply faithful
data; the proof is about those exported graphs. MIR semantics for other
operations, invariants for the checker's list-processing loops,
pointer/borrow and `Vec` memory behavior, observable wrapped bits, and the
LLVM intrinsic implementation remain
release requirements. This does not prove the full checker's execution
correspondence or the source-to-MIR/MIR-to-LLVM translations.

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

Use the matching system attribute on aarch64. All six proof checks are part of
`nix flake check`. For all proof tools and the pinned Horn source:

```sh
nix develop .#proofs
jihoo build -O2 compiler/main.jh -o out/jihoo
JIHOO=out/jihoo bash agda/check.sh
bash agda/check-removal.sh
JIHOO=out/jihoo bash agda/check-lists.sh
JIHOO=out/jihoo bash agda/check-scalars.sh
JIHOO=out/jihoo bash agda/check-mir.sh
```

`check.sh` uses Horn's `schematic-kernel` on `PATH` (or
`SCHEMATIC_KERNEL`), and the proof scripts use `HORN` for the Horn checkout.

The execution-to-Horn and verification-condition-generation proofs remain
separate release requirements in the [roadmap](../docs/internals/roadmap.md).
