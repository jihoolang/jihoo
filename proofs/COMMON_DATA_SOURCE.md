# Checked production Core connected to the common Data fixture

The 0.6 roadmap's main blocker is a common specified typing-to-runtime
ownership theorem. The earlier binary Case/Drop/application work extended that
judgment, but its example graphs were assembled manually. This integration
starts with `tests/core_data_source.jhc`, uses the production parser/checker,
and associates its exact constructor view with a Lean-checked adapted body.
It does not claim that the native compiler has become verified.

## Actual source and preserved snapshot

`core_data_source_probe.jh` parses with `core_parse.parse`, requires one family
and one definition, invokes `Core.check`, and only then reads roots, family
metadata and all nodes from that same Core instance. The snapshot has 95 nodes,
including checker-appended unused nodes. Original export root 29, type root 8,
body 28, family index and constructor order are retained. The selected program
rebuilds one level of Tree with Case, passes the computed result through a
direct lambda application, then drops it and returns 99.

The schema retains supported constructor fields, family data/parameter/arity/
global-prefix fields and constructor type IDs. Unknown constructors and negative
integer literals are explicitly opaque; this is a complete **constructor-view
snapshot**, not a lossless serialization of arbitrary Core terms. Names and
spans are not semantic inputs. No unsupported term is reinterpreted as a valid
Data constructor. The existing Buffer-only exporter is unchanged.

The production export must equal `tests/core_data_source.json`. Separately,
`EmitCommonDataSource.lean` serializes the Lean source-view constant and must
match that same whole snapshot, including unused rows and metadata. Thus fixture
association is tested across both implementations instead of being assumed
from handwritten IDs. Parser/exporter honesty remains a tested trust boundary;
there is no general theorem relating `Core.check` to this view or Lean typing.

## Strict adapter and target judgment

`CommonDataSource` checks bounded/backward supported graph edges, root/type IDs,
nonnegative i64 bounds, and exactly the specified family descriptor: Data,
zero parameters/indices/prior globals, nullary constructor `Ind(0, [])`, then
exactly two non-erased recursive Pi fields ending in `Ind(0, [])`.

Ind, Con and Drop must have the supported family/index/arity shapes. Case must
have two branches, a non-erased constant **Data** motive and a literal nullary
constructor in its empty arm. The node arm must bind two non-erased Tree fields;
its original body ID is used with right/left lexical order and zero ghost slots.
The target empty arm forces the common result kind to Data (`case_empty_result`),
so the adapter cannot silently discard a scalar/dependent motive and admit a
different target result kind. Unsupported node shapes become opaque, and
`opaque_not_typed` excludes them at typed execution roots. Adaptation itself is
not a general source checker; target typing remains a separate requirement.

`entry` additionally recognizes the export's exact Tree-to-I64 Pi and lambda
annotations and selects the original body ID. `entry_typed` proves the adapted
body in the existing CommonData judgment, and `entry_total` constructs safe
terminating abstract execution for any finite represented, exclusively owned
binary input and arbitrary frame. Concrete empty/nonempty traces and every-run
safety are also checked. A direct bounded scalar literal rule avoids inventing
an embedded source node for the original Integer 99.

## Native evidence and remaining gap

Native tests run check and preserves, compare the complete export, and execute
four closed applications of the same function to tree shapes at O0 and O2.
The production native export ABI currently requires scalar arguments/results,
so these tests do not exercise an external Tree-to-I64 entry or arbitrary
runtime inputs; optimization may specialize these closed calls. The checked
source fixture itself can be inspected but cannot be emitted as an external
Data-argument export. Wrapped malloc/free checks verify balanced,
non-invalid ownership lifecycles. Invalid duplicate fields, motive/domain
mismatches and oversized literals must fail checking and object emission; the
probe must not export them. Lean mutation regressions separately reject wrong
family metadata/telescopes, branch shapes, annotations, numeric bounds and IDs.

These are empirical native tests, **not** a simulation proof. The model's empty
is `none` and owns no allocation; native boxed nullary constructors allocate.
Native Case may reuse a pending shell. Native allocation counts, identities,
free order and field bytes are therefore not equated to the abstract trace.
Generic families, scalar/dependent Case motives, general Pi conversion,
compiler optimization/lowering refinement, Back and whole-language exact
accounting remain open. The full 0.6 soundness gate remains open.

The standalone recursive-field check now compares the Lean-emitted snapshot.
The existing native CI test phase runs `core_data_source.py` with and without
Python optimization on both architectures. Shared Core audit lists and
production compiler implementation remain unchanged.
