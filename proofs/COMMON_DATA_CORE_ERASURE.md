# Common Data erasure with compact Core islands

`CommonDataCoreErasure` adds scalar and owner binders whose arguments are the
existing `SizedErasure.Term`. Their runtime evaluates that compact argument using
`SizedErasure.Eval`, then prepends only its returned scalar or Buffer owner to the
original common environment. Core-local binders do not escape. The argument's
sized events are projected into the common trace; its entire final sized heap,
including dynamic lengths, becomes the continuation's initial heap. Data cells
are unchanged during the Core argument.

The target retains binary Tree construction, Case, Drop, Data application and
Buffer Free. The #184 `CommonDataErasure` and #186 `CommonDataBufferErasure`
syntax, evaluation and theorem interfaces are unchanged. This is an independent
extension, not an assertion that their variable indices are interchangeable.

## Two masks and the environment interface

`Lower g slots mask root target` uses two source-indexed lexical masks:

- `slots` selects the common runtime, retaining Data.
- `mask` selects the Core runtime, where Data projects to ghost.

Data binding extends them with `true` and `false`; Case extends them twice.
Scalar and owner binding extends both with `true`. Consumption changes resource
authority, not stale runtime slots. Target Core input is the compact projection
of the *common* runtime, not a reuse of its slot indices.

`Bridge slots mask source compacted` pairs the existing common `Env` relation
with the exact Core `EnvRel`. `Bridge.of_common` uses the independently developed
`CommonDataEnvironmentCompaction.project_compact` and `core_related` laws. That
module is integrated unchanged. Its residual-mask and position/rank laws explain
why common `[Data, Buffer]` index 1 becomes Core index 0.

## Proven endpoints

`typing_lowers` derives a finite structural witness from every constructor of
`SymbolicCommonDataSource.Typing` and lexical mask support. It reuses
`SymbolicCoreCompaction.typing_erases`, `index_erases`, and `scalar_erases`, checking
both Core branches regardless of the branch selected at runtime. It does not
assume successful execution, a successful compiler call, or an arbitrary Lower
certificate.

`Lower.preserves` transfers every source run with the exact returned common
value, projected trace and final common state. Thus the heap, length map and Data
cells agree, including Data frames retained across producer calls and pending
Case shells.

`typing_preserves` chooses one target before quantifying over all related source
executions. `closed_total_accounted` derives mask support and the bridge from
ordinary closing, source agreement and common compaction. It then derives an
actual compact execution, valid heap, safe steps and existing per-identity
Data/Buffer accounting from source typing and ownership invariants.

Regression fixtures cover dynamic allocation followed by Case/Free; split Data
application with delayed Buffer release; a general prefix producer that releases
one input, returns another and retains a third; effectful scalar application
under Case binders; and dynamic branch/owned-lend/framed-application/read-lend
composition followed by Data Case/Drop. All public integration theorems and the
independent environment bridge are included in the recursive axiom audit.

## Boundary

This remains the existing fixed binary Tree and constant-motive common-source
fragment with the existing symbolic Core grammar. It does not add general Data
families, dependent motives, recursion, arbitrary readers or Store. It does not
prove native lowering of the common target, production-checker refinement,
allocator/layout refinement, compacted dependent-context typing or general
expression reindexing. The structural witness is proposition-level; a separate
executable common compiler and its completeness theorem remain future work.
