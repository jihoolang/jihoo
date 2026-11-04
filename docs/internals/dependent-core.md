# Native dependent core

The replacement direction for verification is to check the program and
its proofs in one native core, then erase and lower that checked program.
It does not require reconstructing the program's execution as Horn rules.
Horn's theory, exporter and certificate format are not compatibility
requirements for the new core.

The first executable slice is experimental. `jihoo core` reads a `.jhc`
core file; ordinary `.jh` syntax has not yet been elaborated into this
core. Its implementation is jihoo code in `compiler/core.jh`,
`core_parse.jh`, `core_lower.jh` and `core_driver.jh`.

```text
.jhc terms + types + proofs
  -> native core checker
  -> beta reduction and proof erasure
  -> MIR from those same terms
  -> initialization/borrow checking
  -> LLVM -> object
```

The core path calls neither the existing verification-condition generator
nor Horn/Agda. The existing `.jh` verifier and its checks remain the
baseline during migration; the new kernel is not yet formally proved
sound, and its erasure and lowering are not yet proved to preserve
behavior. Passing the prototype's tests does not complete the 0.5 release
requirements or establish correctness of the compiler or its executables.

## Run the executable slice

In the development shell, with a current compiler at `out/jihoo`:

```sh
out/jihoo core check examples/core_index.jhc
out/jihoo core emit-mir examples/core_index.jhc
out/jihoo core emit-llvm examples/core_index.jhc -o out/core_index.ll
out/jihoo core emit-obj examples/core_index.jhc -O2 -o out/core_index.o
```

The object exports `int64_t lookup(uint64_t i)`. A C or jihoo caller can
link it as an ordinary object. It returns 11, 22 or 33 at indices 0, 1 or
2, and -1 otherwise, including the upper half of U64. `--target x86_64`
and `--target aarch64` select the target. Core code generation uses the
native C ABI, with scalar arguments and results only.

The source defines a helper for arbitrary `n`, `xs : Array n` and `i`:

```text
(def get
  (pi n U64 (pi xs (Array n) (pi i U64 (pi0 p (Lt i n) I64))))
  (lam n U64 (lam xs (Array n) (lam i U64 (lam0 p (Lt i n)
    (index xs i p))))))
```

The exported caller compares its runtime index with 3. Only the true
branch has evidence of that inequality, which it passes to `get`:

```text
(export lookup
  (pi i U64 I64)
  (lam i U64
    (if-lt i 3 p
      (app get 3 (array (int 11) (int 22) (int 33)) i p)
      (int -1))))
```

The helper is type-checked before specialization, including its erased
parameter. Beta reduction substitutes its arguments without capturing
variables. MIR is then emitted directly from the checked terms. It has
one scalar argument, the caller's real branch and an array load, without
a proof argument, proof allocation or an additional bounds assertion.
This is already true before LLVM optimization. The caller's branch
remains necessary because its input can be any U64.

## Core syntax

The textual format uses parentheses and semicolon line comments. Local
names are elaborated to de Bruijn indices; definitions are nonrecursive
and may refer only to earlier definitions. A definition is
`(def name type value)` or `(export name type value)`. Exports are the
object's runtime entry points; helpers are normalized at their uses.

| term | meaning |
|------|---------|
| `(Type u)`, `Prop` | levelled universes and the universe of propositions |
| `U64`, `I64` | unsigned indices and signed array elements |
| decimal `n`, `(int n)` | checked U64 and I64 literals; no wrapping |
| `(Array n)` | immutable I64 array indexed by its U64 length |
| `(Lt i n)` | proposition that unsigned `i` is below `n` |
| `(pi x A B)` | dependent function type, with `x` in scope in `B` |
| `(lam x A body)` | function with an explicitly typed argument |
| `(pi0 p P B)`, `(lam0 p P body)` | erased proof binder |
| `(app f a ...)` | function application, checked before erasing arguments |
| `(array e ...)` | local immutable array |
| `(index xs i p)` | load, requiring exactly `Lt i (length of xs)` |
| `(decide-lt i n)` | evidence of a closed inequality that reduces to true |
| `(if-lt i n p yes no)` | unsigned branch; erased `p : Lt i n` exists only in `yes` |

`Type u` has type `Type (u + 1)`, never itself. Dependent function types
compute their universe levels; a function ending in a proposition is a
proposition. Type-level functions and higher-order beta reduction work,
but the executable ABI is restricted to U64/I64 arguments and results.
There are no axioms, casts, general recursion, unsafe memory operations
or eliminators that inspect evidence to produce runtime data.

Erased binders must bind propositions; proof binders must be erased.
Evidence can be used in types and proof arguments, but not as runtime
data. Erased data/type parameters, inductive propositions, equality and
general induction are future work. Runtime indices are real U64 values;
the prototype does not model them as unbounded mathematical naturals.

Both branches and all definitions are checked before normalization or
erasure. A false proof in an unused helper, erased argument or unreachable
branch is rejected. The true branch's proof cannot be used in the false
branch or escape in its result type. Foreign exports cannot require an
erased precondition or accept array pointers: the ABI cannot ensure that
a foreign caller supplies the evidence or a correctly indexed allocation.

Checking is bounded by one million checking steps, 200,000 arena nodes,
128 levels of nesting and a 1 MiB/50,000-token source limit. Exhaustion
rejects the input. `check` needs neither LLVM nor any proof tools.
Diagnostics support `--error-format=json`. No option bypasses the kernel.

## Tests and remaining work

```sh
python3 tests/core.py --compiler out/jihoo
JIHOO_COMPILER=out/jihoo jihoo run tests/runner.jh -- core
```

The `core` suite is part of the default runner and Nix/CI checks. It
checks both targets at `-O0` and `-O2`, executes host objects through the C
ABI and compares them with an independent named-variable evaluator.
Cases include nested proof binders, beta substitution, empty arrays,
signed element boundaries and arbitrary U64 indices. Negative cases
cover false and mismatched evidence, wrong lengths, erased runtime uses,
universe errors, recursion, overflow and scope escape. Kernel unit tests
also construct malformed graphs and false evidence without the parser.

The next stages of the replacement are:

1. Elaborate an explicit subset of ordinary `.jh` definitions into this
   same core, including source diagnostics and proof syntax.
2. Add the logical foundations users need: inductive propositions,
   equality, induction, erased indices and user-written lemmas. Specify
   normalization, universe and erasure rules before enabling them.
3. Add runtime operations with explicit ownership/effect rules, including
   borrowed and mutable memory and dynamic allocation. Extend the direct
   lowering of checked programs rather than adding a separate Horn model.
4. Establish the kernel's metatheory and the preservation obligations for
   erasure and lowering. External proof tools may validate this small
   trusted foundation; they are not a required user compilation stage.
5. Retire legacy verification paths as their source programs and enabled
   guarantees move to the core. Reproducing the legacy certificate format
   or preserving its implementation is not a migration requirement.
