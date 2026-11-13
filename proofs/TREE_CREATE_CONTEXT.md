# Tree constructor common-context extension

Integrated with main `b5ed6688` (PRs #197–#200), preserving the Case entry
context registrations from #200. The extension imports the common resource
boundary from #197 and independently relocated constructor correctness from #199.

`TreeCreateContext.node_prefix_context` derives source/target child operands,
child layouts, joint ownership and target separation from `CommonContext`.
It produces the actual 13-step `Prefix`, the constructed result binding and
complete successor `CommonContext`. The captured-context law retires every
alias of both consumed child capabilities, shifts retained resource indices,
and preserves live scalar/natural and resource locals outside the write set.
Retained trees/buffers, buffer sizes, pending shells and both ambient frames
survive. The physical locals holding dead aliases need not be cleared.

`nil_prefix_context` proves the 3-step boxed Nil prefix and inventory extension;
the source state stutters while the target gains one object. `typing_construct`
extracts ordered child selections from common typing. `source_construct`
produces the source Eval using the same values obtained from context lookup.
The source trace allocates payload 0; the target trace allocates 24 bytes.

## Explicit assumptions

- Installed function and independent prefix placement, local types/bounds,
  distinct destinations and fresh parallel-copy temporaries (`Safe`).
- The input common context, with ordered child authority at indices 0 and 1.
- Actual allocator object/cell capacity (`Budget`), not assumed malloc success.
- Surviving lexical entries avoid every Node write (only the result for Nil).
  This condition is checked after alias retirement for Node.
- The next target heap index is not already reserved by the input inventory,
  pending shells or external frame. In particular, Context permits absent
  external target IDs, so external-frame freshness cannot follow from Context
  alone. The stronger explicit whole-inventory condition is sufficient.

No continuation execution, return ABI, general compiler lowering, native
correctness, reuse semantics, or whole-program correctness is claimed.

## Regressions and checks

The Node fixture instantiates the theorem with swapped operands/destinations,
a nonempty child, boxed Nil, duplicate child aliases in overwritten locals,
a retained Buffer with size 2, live scalar/natural locals and a suspended stack.
Nil also instantiates its full context theorem with retained scalar/natural
lexical bindings and checks the resulting values and suspended stack. Rejection tests cover a live
scalar clobber and duplicate boxed-Nil target authority. A typed source fixture
proves the source constructor execution.

Run `bash proofs/check-tree-create-context.sh`: builds with `--wfail` and audits
all 21 public theorems; only propext, Quot.sound and Classical.choice are allowed.
No `sorry`, `admit`, custom axiom or native_decide is used.

## Aggregate integration

`proofs/Jihoo.lean` imports the context module and its regression checks.
`proofs/Audit.lean` preserves all 3568 audits from main and adds the 21 Tree
context entries, for 3589 aggregate audits. `proofs/check.sh` enforces that count
and the standard-axiom allowlist. The default Nix `lean-proofs` check runs this
aggregate suite; both Test architecture jobs and Common Core backward proofs
also invoke the dedicated Tree context script.
