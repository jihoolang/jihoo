# Graph-certificate Lean dependency build

The graph-certificate check previously ran `lake build --wfail`, rebuilding the
entire `Jihoo` proof/example root before executing the Python integration tests.
It now names the imports used by its Lean validator and emitter entry points,
plus `Jihoo.InitializationStore` and `Jihoo.InitializationCalls` for the generated
native-proof harnesses. Lake still builds their transitive dependencies and
rejects warnings. Keep the explicit targets in sync when adding checker imports.

The independent `lean-proofs` check still builds the complete library, runs the
aggregate axiom audit, and checks generated fixtures. Every Python command,
including normal and optimized security checks, is unchanged. Both architecture
matrix entries, source filesets, and source-isolation expectations are unchanged.
No remote cache, credentials, secrets, permissions, or workflow changes are added.

## Measurement

Measured against main `8ac8db21064bd1ec7cdb353d29c4e1c42340774a`, using pinned
Lean 4.34.1 in the same local Linux environment. Both builds started with an empty
`.lake`; the baseline artifacts were moved aside before the second build.

| Cold build | Seconds | Lake jobs |
| --- | ---: | ---: |
| Full `lake build --wfail` | 391.905 | 370 |
| Explicit graph dependency targets | 136.174 | 154 |

This is 255.731 seconds (65.3%) less time in this build phase. The local Jihoo
source-module closure shrinks from 368 modules to 153. This is one timing pair,
not a statistically controlled benchmark or a measurement of total GitHub CI
latency. Source-isolation evaluations overlapped the baseline; the compiler and
integration test execution times are excluded. No claimed percentage reduction
for the complete workflow follows from these numbers.

## Validation

- Both cold Lean builds passed with `--wfail`.
- All direct imports of the 26 graph-check Lean entry points are included, as
  are both generated native-proof harness dependencies.
- All 91 Python command lines in the flake remain identical, including 35
  optimized-mode invocations; the aggregate Lean check is byte-for-byte unchanged.
- All 12 existing source-isolation mutations passed for both x86_64-linux and
  aarch64-linux, including exact source membership and restoration checks.
- The complete x86_64 Nix graph-certificate suite passed in 1983.281 seconds
  with the validation-only thread override described below, including every
  normal and optimized Python invocation. This duration has no paired baseline.
- Native aarch64 execution and hosted before/after workflow timing require CI.

The local rootless Nix runtime failed to spawn Lean processes with `resource
exhausted (error code: 12, not enough memory)` at its default settings and with
two-CPU affinity. A validation-only `LEAN_NUM_THREADS=2` override was used for the
successful integration run; it is not part of the proposed flake change.

## Integration after Case proofs

The optimization is integrated with main
`4847866b88358332a5b5735ab4b63a4448db48ee` (#204). The original measurement above
is retained as historical evidence, not a new timing claim. All 29 graph targets
and their 153-module dependency closure are byte-identical to the previously
validated optimization. All 91 Python command lines (35 optimized invocations),
aggregate `lean-proofs`, workflows, source filesets, and source-isolation script
remain unchanged relative to this main. Fresh source-isolation evaluation passed
all 12 mutations on both supported systems. A clean aggregate build passed all
381 jobs, 3,732 axiom audits, and the generated-fixture comparisons. This local
check used `LEAN_NUM_THREADS=2`; it is not a CI configuration change. The full
graph suite was not repeated locally after integration because its dependency
closure and invocation sequence are unchanged. Fresh exact-head hosted CI is
still required before merging.
