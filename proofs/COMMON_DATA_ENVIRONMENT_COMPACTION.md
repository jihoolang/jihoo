# CommonData/Core environment compaction square

Independent proof on main `8b02eb54459cad340469f42d52e790599b72fa3f`
(PR #186). Only the two new modules and this note are added; shared target,
typing, aggregate imports, build configuration and central audits are untouched.

## API

Namespace: `Jihoo.CommonDataEnvironmentCompaction`.
Let `P = RecursiveBodyProjection.environment`,
`C e = (SizedErasure.compactEnv (P e)).2`, and
`M e = (SizedErasure.compactEnv (P e)).1`.
For `h : CommonDataErasure.Env slots source target`:

- `project_compact`: `C source = C target`.
- `core_related`: `EnvRel (M e) (P e) (C e)`.
- `relational_square`: the same equality for *any* two given projected
  `EnvRel` witnesses; `envRel_canonical` discharges their canonicality.
- `position_rank`: if `position slots k = some j`, then
  `rank (M source) k = rank (M target) j`.
- `relational_position_rank`: the rank law for arbitrary given `EnvRel` masks.
- `position_mask`: corresponding positions have equal Core retention bits.
- `select_mask`: `select slots (M source) = M target`. The residual mask is
  selected, not reused. `select` is an explicit lexical list selection.
- `position_exists`: every non-ghost source lookup has a CommonData position.
- `lookup`, `nat_lookup`, `scalar_lookup`, `buffer_lookup`: observable lookup
  preservation through both passes. `data_erased`, `ghost_erased`,
  `buffer_retained` distinguish precisely which values can disappear.
- `nat_binder`, `scalar_binder`, `owner_binder`, `data_binder`: CommonData
  relation extension plus the corresponding Core mask and runtime shape.
- `case_binders`, `case_position_rank`: both actual right/left Data fields
  remain CommonData binders, become false Core bits, and introduce no Core
  runtime slot. Existing `Env.enter` can provide the relation after a successful
  Case opening; this module does not duplicate heap/opening simulation.
- `projected_support`: symbolic closing plus existing ownership-sensitive
  agreement gives `MaskSupports (project retained.length ctx) (M source)`.
- `support_select`, `projected_support_compacted`: support transfers to the
  selected projected context with residual mask `M target`.

No heap liveness assumption is used in compaction. Buffer and borrow aliases
remain values even when typing entries are dead. The original agreement in
`projected_support` retains the full retained-Data and Buffer capability list.
Data is projected using the existing `.data _ -> .ghost` definition; no scalar
placeholder or erased ownership premise is introduced.

## Checked counterexamples and scope

`common_mask_not_core` shows that CommonData `[true]` for `[data none]` is
incompatible with its Core `[false]`. `data_buffer_counterexample` shows the
Buffer after Data has CommonData position 1 but Core rank 0. Checks also cover
mixed Data/ghost/Nat/Buffer environments, two Case fields, an explicitly retained
ghost, and a stale Buffer alias under a dead entry with an empty capability
inventory. The stale Buffer remains `.owner 7` while stale Data becomes ghost.

The rank equality alone does **not** license a Data lookup: removed slots can
have the same rank as a later retained slot. The generic lookup theorem requires
an actual projected non-ghost `SizedErasure.Value.embed` lookup.

Not claimed: term-lowering or execution simulation, whole-program erasure
totality, compacted-context typing, renaming of symbolic dependent expressions,
or native/MIR refinement. `select`/`MaskSupports` is only the environment and
mask interface; preserving dependent expression meaning requires the separate
index/typing bridge. No assumption of successful target evaluation is present.

## Independent validation

Lean 4.34.1, exactly as pinned by `proofs/lean-toolchain`:

```sh
cd proofs
lake build Jihoo.CommonDataEnvironmentCompactionChecks
```

Passed all 96 build jobs. The checks module audits every new theorem: 28 API
and counterexample theorems plus 5 concrete checks, 33 total. All use no axioms
or only `propext` / `Quot.sound`; no `sorryAx` or `Classical.choice`.

The first build attempts hit exit 137 in unchanged dependency modules because
the downloaded toolchain occupied memory-backed `/tmp`. Moving it to workspace
disk resolved this; the completed 96-job run is the validation result.
This is a focused independent build, not a claim that the aggregate full-project
or Nix checks ran.
