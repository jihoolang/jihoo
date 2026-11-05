# Native dependent core

The replacement direction for verification is to check the program and
its proofs in one native core, then erase and lower that checked program.
It does not require reconstructing the program's execution as Horn rules:
Horn's checker is small, but a translation of jihoo programs into Horn
would itself be trusted, and would be much larger than this kernel. The
kernel stays small by providing general rules (such as declared inductive
propositions) rather than built-in special cases.
Horn's theory, exporter and certificate format are not compatibility
requirements for the new core.

The executable slice is experimental. Ordinary `.jh` files opt into a
small source subset with `#![dependent_core]`; `compiler/core_elab.jh`
constructs core terms directly from the ordinary parser's AST. `jihoo core`
also reads `.jhc` core files. Both frontends use `compiler/core.jh` and
`core_lower.jh`; `core_parse.jh` and `core_driver.jh` provide the textual
core frontend.

```text
.jh -> ordinary parser AST -> core terms + types + proofs
.jhc -> core parser        -> core terms + types + proofs
  -> native core checker
  -> beta reduction and proof erasure
  -> MIR from those same terms
  -> initialization/borrow checking
  -> LLVM -> object
```

The core path calls neither the existing verification-condition generator
nor Horn/Agda. Unmarked `.jh` files retain the existing verifier and its
checks during migration; the new kernel is not yet formally proved
sound. Source elaboration, erasure and lowering are not yet proved to
preserve typing or behavior. Passing the prototype's tests does not
complete the 0.5 release requirements or establish correctness of the compiler or its executables.

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

## Ordinary source subset

[`examples/core_index.jh`](../../examples/core_index.jh) exports the same
lookup and adds a small executable entry point:

```jihoo
#![dependent_core]

fn get(n: u64, xs: [i64; n], i: u64, p: erased(Lt(i, n))) -> i64 {
    index(xs, i, p)
}

export fn lookup(i: u64) -> i64 {
    if_lt(i, 3, fn(p) { get(3, [11, 22, 33], i, p) }, -1)
}

fn main() -> i64 { lookup(3) }
```

```sh
out/jihoo check examples/core_index.jh
out/jihoo emit-mir --lib examples/core_index.jh
out/jihoo emit-obj --lib examples/core_index.jh --target x86_64 -O0 -o out/lookup.o
out/jihoo emit-obj --lib examples/core_index.jh --target aarch64 -O2 -o out/lookup-arm.o
out/jihoo run examples/core_index.jh   # returns -1 as exit status 255
```

The file attribute selects the whole module. These are contextual forms
in the existing grammar, not global keywords or standard-library types:

| source | elaboration |
|--------|-------------|
| `u64`, `i64`, `[i64; n]`, `Lt(i, n)`, `Eq(a, b)` | scalar/array types and propositions |
| `trait F(a: u64, ...) { fn c(...) -> F(...) }` | [declared inductive proposition](#inductive-propositions) `F` with constructors `c` |
| `F(a, ...)`, `c(x, ...)` | a declared proposition; its constructor, fully applied |
| `p: erased(P)` | erased Pi/Lam binder of proposition `P` |
| `f(a, ..., p)` | dependent applications, with all arguments explicit |
| `[11, 22, 33]` | immutable core array |
| `index(xs, i, p)` | core load requiring exactly `Lt i (length of xs)` |
| `decide_lt(i, n)` | proof of a true, closed unsigned inequality |
| `if_lt(i, n, fn(p) { yes }, no)` | unsigned branch binding `p: Lt(i, n)` only in `yes` |
| `if_eq(a, b, fn(e) { yes }, no)` | equality branch binding `e: Eq(a, b)` only in `yes` |
| `refl(a)` | reflexivity evidence of `Eq(a, a)` |
| `transport(fn(k) { P(k) }, e, p)` | move evidence from `P(a)` to `P(b)` using `e: Eq(a, b)` |
| `induct(P, case, ..., evidence)` | structural induction: one case per constructor, into a proposition |
| `a + b`, `a - b`, `a * b` | [i64 arithmetic](#loops-and-arithmetic); overflow traps |
| `fold(n, init, fn(i, p, acc) { body })` | loop for `i` below `n`, with erased `p: Lt(i, n)` |

`n` and `i` are ordinary runtime U64 parameters. `[i64; n]` records the
length symbolically in the core; it does not evaluate `n` as a legacy
compile-time array size. The generic helper is checked once with symbolic
`n`, `xs`, `i` and `p`, before any caller substitutes a concrete array.
`erased(P)` marks a proof binder; it is not a `comptime` parameter or a
request to fix a value during specialization. `comptime`, `sink` and
`inout` parameters are rejected in this subset. A helper can forward
proofs or return `Lt(i, n)`, `Eq(a, b)` or declared evidence; the checker controls their runtime
relevance. Every definition and both branches are checked, including
unused helpers and discarded proof arguments.

Functions must have explicit parameter and result types and one value
expression per block. They may refer only to earlier definitions, and
calls supply exactly the declared number of arguments. Expressions are
names, checked integer literals (including negative I64 literals), arrays,
blocks, calls and the operations above. Integer literals take the
expected scalar type; array elements are I64 and indices/lengths are U64.
`erased` is allowed only as the outer parameter annotation. The forms
`erased`, `Lt`, `Eq`, `if_lt`, `if_eq`, `refl`, `transport`, `induct`,
`fold`, `index`, `decide_lt`, `u64`, `i64` and the entry symbol
`__jihoo_dependent_main` are reserved in marked modules. Functions,
propositions and constructors share one namespace. A branch
binder may shadow another local; de Bruijn indices preserve its scope.

Exports accept and return only U64/I64 values and cannot require proof
preconditions from foreign callers. Without `--lib`, the entry must be an
ordinary `fn main() -> i64`; its result becomes the process exit status
through the existing native entry wrapper. With `--lib`, only explicitly
exported functions are emitted. Helpers, including a non-exported `main`,
are still checked. A compilation needs at least one runtime export or an
entry point. `check` validates this executable subset, including its ABI,
without LLVM or a linker.

Imports, item attributes, contracts, foreign declarations, other profiles,
local statements, implicit proof search, ordinary `if`/index syntax,
u64 arithmetic, division and comparison operators, general runtime
closures/recursion, data (non-`Prop`)
inductive types and mutable memory are outside this slice and rejected. Marked modules cannot be imported by the
legacy frontend. This keeps the source scope explicit while extending
only one execution path. `fmt`, AST dumps and source diagnostics use the
ordinary parser; checking errors retain `.jh` byte ranges. Source parsing
uses the ordinary parser's limits; core checking and normalization retain
the core limits below.

`check`, `build`, `run`, `emit-mir`, `emit-llvm` and `emit-obj` route marked
files through the same core checker, erasure and MIR lowering as `.jhc`.
No temporary `.jhc` text is produced or reparsed. The ordinary initialization
and borrow checks and LLVM backend then run on that MIR. The branch proof
has no MIR argument or local, and `index` adds no bounds assertion.
`--no-verify`, `--release` and debug MIR switches never bypass proof
checking. `check --verify` still checks this same core. Legacy `verify`,
`emit-horn`, `emit-obligations` and the `test` harness are explicitly
unsupported for marked files; compilation does not call their VC machinery.

## U64 equality and proof transport

The equality slice adds intensional U64 equality in `Prop`. Its rules
are deliberately limited to erased evidence; array layouts and runtime
values do not change because of a proof.

- `Eq(a, b) : Prop` requires `a, b : U64`.
- `refl(a) : Eq(a, a)` accepts symbolic U64 values. Conversion uses the
  existing beta/branch normalization; an equality assumption does not make
  its endpoints definitionally equal.
- Given `P : U64 -> Prop`, `e : Eq(a, b)` and `p : P(a)`,
  `transport(P, e, p) : P(b)`. The family cannot return data or universes.
  Transport reduces to `p` when normalized `e` is `refl(a)`; otherwise it
  remains an erased proof term. There is no runtime proof inspection.
- `if_eq(a, b, fn(e) { yes }, no)` compares runtime U64 values and binds
  erased `e : Eq(a, b)` only in `yes`. Both branches are checked before
  normalization. A closed comparison reduces to the selected branch,
  substituting `refl(a)` into a true branch.

Source families are written `fn(k) { Lt(i, k) }` or `fn(k) { Eq(k, a) }`:
one untyped U64 binder and a proposition as their single expression.
They elaborate directly to core lambdas; they create no runtime closure.
The textual equivalents are `(Eq a b)`, `(refl a)`,
`(transport family e p)` and `(if-eq a b e yes no)`, with a family such as
`(lam k U64 (Lt i k))`. The full core checks arbitrary `U64 -> Prop`
families. Equality symmetry, transitivity and inequality rewriting are
ordinary user-written proof functions, derived from `refl` and `transport`.
There are no added axioms or unchecked casts. General equality of types
and data transport remain future work.

[`examples/core_equality.jh`](../../examples/core_equality.jh) and its
[core equivalent](../../examples/core_equality.jhc) define symmetry and
bound rewriting as user lemmas, then export `lookup(n, i)`. It returns
11/22/33 when `n == 3` and `i` is in range, -1 for an invalid index with
that length, and -2 for another length. Its entry returns 11 as the
process exit status. For example, the bound lemma is:

```jihoo
fn bound(i: u64, n: u64, m: u64, e: erased(Eq(n, m)), p: erased(Lt(i, n))) -> Lt(i, m) {
    transport(fn(k) { Lt(i, k) }, e, p)
}
```

The lookup first obtains `Eq(3, n)` from `if_eq`, derives `Eq(n, 3)`
with a user-written symmetry lemma, and rewrites `Lt(i, n)` into
`Lt(i, 3)`. The array's actual length remains 3 throughout. No equality
reflection silently unifies `n` with 3, and no array cast is performed.
In both frontends the unoptimized lookup MIR has two scalar arguments,
two real comparisons/branches and one array load, with no proof locals,
closures, transport operations or bounds assertions.

## Inductive propositions

A program declares its own inductive propositions. The kernel has no
built-in recursive proposition: an earlier slice's fixed `EqChain` is
now an ordinary declaration in
[`examples/core_chain.jh`](../../examples/core_chain.jh), checked by the
same rules as any other.

```jihoo
trait EqChain(a: u64, b: u64) {
    fn chain_refl(a: u64) -> EqChain(a, a)
    fn chain_step(
        a: u64,
        b: u64,
        c: u64,
        e: erased(Eq(a, b)),
        tail: erased(EqChain(b, c))
    ) -> EqChain(a, c)
}
```

In a marked module, `trait` declares a family `F : U64 -> ... -> Prop`,
one `u64` parameter per index (none is allowed), and each signature
without a body is a constructor. The kernel checks every constructor
type, a closed telescope, when the family is declared:

- data fields are `u64` and are the only runtime-typed fields; every
  other field is an erased proposition;
- the family itself may occur only as a whole erased field `F(indices)`
  (a recursive field) and as the result, `F(indices)` with exactly its
  arity of `u64` indices. The telescope is checked after normalization,
  and while its constructors are checked the family is not yet in scope,
  so any other occurrence (under an arrow, in an index, in another
  field's type) is rejected. This is strict positivity,
  restricted further to first-order recursive fields;
- a family may use earlier definitions and families, and is visible only
  to later items. Families and definitions form one ordered sequence;
  there is no mutual or forward reference.

`induct(P, case_1, ..., case_k, evidence)` eliminates evidence of
`F(t...)` into `P(t...)`, where `P : U64 -> ... -> Prop` has one binder
per index. There is one case per constructor, in declaration order. The
case for a constructor with fields `x...` and recursive fields `r_1...r_n`
has the type

```text
(x...) -> (erased ih_1 : P(indices of r_1)) -> ... -> (erased ih_n : P(indices of r_n))
       -> P(indices of the constructor's result)
```

with the hypotheses after all fields. Reduction applies the case of a
constructor to its fields and then to the induction on each recursive
field, a strict subterm; user code never chooses a recursive argument,
so proofs by induction terminate. Neutral evidence stays neutral, and
every case is checked even if no constructor reaches it. Motives and
cases cannot produce data, types or universes: evidence never decides a
runtime value, and the whole elimination is erased. The motive does not
depend on the evidence itself.

The family is found from the evidence's type. Cases can be named proof
functions with the signatures above or contextual lambdas, as for
`transport`; a constructor without fields and hypotheses can be given
as a proof expression. `induct` on an empty family (`trait Never {}`)
needs no cases and proves anything, which is sound because `Never` has no
evidence.

[`examples/core_inductive.jh`](../../examples/core_inductive.jh) and its
[core equivalent](../../examples/core_inductive.jhc) declare the edges of
a small graph and the nodes reachable from 0:

```jihoo
trait Edge(a: u64, b: u64) {
    fn e01() -> Edge(0, 1)
    fn e12() -> Edge(1, 2)
    fn e02() -> Edge(0, 2)
}

trait Reach(b: u64) {
    fn start() -> Reach(0)
    fn step(a: u64, b: u64, r: erased(Reach(a)), e: erased(Edge(a, b))) -> Reach(b)
    fn same(a: u64, b: u64, r: erased(Reach(a)), e: erased(Eq(a, b))) -> Reach(b)
}
```

`edge_bound` proves `Lt(b, 3)` for every edge by case analysis, and
`reach_bound` proves it for every reachable node by induction, for paths
of any length; its `same` case transports the hypothesis along the
equality. `node(b, r)` loads from a length-3 array with that proof. The
exported `cost(b)` builds the evidence for `b == 2` and `b == 1` from the
real comparisons and returns -1 otherwise. Its MIR has one argument, two
comparisons and two array loads: no evidence, cases, recursion or bounds
checks. Both frontends emit the same MIR before LLVM optimization.

`examples/core_chain.jh` proves `Eq(a, b)` from an arbitrary symbolic
`EqChain(a, b)` with the motive `fn(a, b) { Eq(a, b) }`, using the
equality-transitivity lemma in the step case, and then transports a
runtime range proof to a length-3 array. Its `lookup(n, m, i)` links the
guards `n == m`, `m == 3` and `i < n` into a chain.

In `.jhc`, `(inductive F N (c TYPE) ...)` declares a family of arity `N`
with constructors `c` whose types are core telescopes; `(F a ...)` and
`(c x ...)` use them, and `(induct F P case ... evidence)` names the
family explicitly. Kernel terms are `Ind(F, indices)`, `Con(F, k,
fields)` and `Elim(F, P, cases, evidence)`.

Not yet supported: data (non-`Prop`) inductive types and their
elimination into data, motives depending on the evidence, families
indexed by values other than `u64` or parameterized by propositions,
infinitary (arrow-typed) recursive fields, mutual families and erased
data indices.

## Loops and arithmetic

Runtime code has i64 `+`, `-` and `*` and one loop form:

```text
fold(n, init, body) : I64
    where n : U64, init : I64,
          body : (i : U64) -> (erased p : Lt(i, n)) -> (acc : I64) -> I64
```

It starts with `init` and replaces the accumulator by `body(i, p, acc)`
for each `i` from 0 to `n - 1`. In `.jh` the body is a contextual lambda
`fn(i, p, acc) { ... }` whose parameter types come from that signature.
Because `p` proves `Lt(i, n)`, a body loads from an array of length `n`
with `index(xs, i, p)` and no bounds check. A helper over arrays of any
length is checked once, for symbolic `n`:

```jihoo
fn dot(n: u64, xs: [i64; n], ys: [i64; n]) -> i64 {
    fold(n, 0, fn(i, p, acc) { acc + index(xs, i, p) * index(ys, i, p) })
}
```

The loop always terminates: its count is fixed before it starts. The
normalizer does not unroll loops, except that a loop of count 0 is its
initial value, so checking cost does not grow with the count. Arithmetic
on two literals is computed unless it overflows. An overflowing operation
is never folded or wrapped; it stays in the program, which traps at run
time as ordinary jihoo's checked arithmetic does. No proposition mentions
an i64 value, so arithmetic cannot change what a proof means. U64 values
appear in propositions and have no arithmetic yet: machine wrapping
would make `Lt(i, n)` and `Lt(i + 1, n + 1)` disagree at the top of the
range, so u64 arithmetic needs overflow evidence.

Calls evaluate their arguments first, as ordinary jihoo does, although
the normalizer substitutes helpers into their callers. When beta
reduction substitutes a runtime argument that can trap (one containing
arithmetic), the result is a kernel-internal `Strict(argument, result)`:
evaluate the argument, then the result. So `ignore(MAX + 1)` traps even
though `ignore` does not use its parameter, and an argument used in one
branch traps before the branch is chosen. Normalization drops `Strict`
when its first term cannot trap. Applying an `if_lt`/`if_eq` applies both
alternatives, and a loop body is eta-expanded, so any body of the loop
type lowers, including a branch that chooses between two lambdas.

[`examples/core_loop.jh`](../../examples/core_loop.jh) and its
[core equivalent](../../examples/core_loop.jhc) define `sum` and `dot`
and export `weighted(x)`, a dot product with runtime elements, and
`repeat(n, x)`, a loop of runtime count. Each export's MIR is one loop:
a comparison, the body's loads without bounds assertions, checked
arithmetic and the index increment, which cannot overflow because
`i < n`. Both frontends emit the same MIR. In `.jhc` the forms are
`(add a b)`, `(sub a b)`, `(mul a b)` and `(fold n init body)`, with a
body `(lam i U64 (lam0 p (Lt i n) (lam acc I64 ...)))`.

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
| `(Eq a b)`, `(refl a)` | U64 equality proposition and reflexivity evidence |
| `(transport family e p)` | equality elimination into a proposition family |
| `(inductive F n (c type) ...)` | top-level declaration of an inductive proposition |
| `(F a ...)`, `(c x ...)` | a declared proposition; a constructor with all fields |
| `(induct F P case ... e)` | proposition-only structural induction on evidence of `F` |
| `(add a b)`, `(sub a b)`, `(mul a b)` | i64 arithmetic; overflow traps at run time |
| `(fold n init body)` | bounded loop; `body : (i : U64) -> Lt i n -> I64 -> I64`, erased bound |
| `(pi x A B)` | dependent function type, with `x` in scope in `B` |
| `(lam x A body)` | function with an explicitly typed argument |
| `(pi0 p P B)`, `(lam0 p P body)` | erased proof binder |
| `(app f a ...)` | function application, checked before erasing arguments |
| `(array e ...)` | local immutable array |
| `(index xs i p)` | load, requiring exactly `Lt i (length of xs)` |
| `(decide-lt i n)` | evidence of a closed inequality that reduces to true |
| `(if-lt i n p yes no)` | unsigned branch; erased `p : Lt i n` exists only in `yes` |
| `(if-eq a b e yes no)` | equality branch; erased `e : Eq a b` exists only in `yes` |

`Type u` has type `Type (u + 1)`, never itself. Dependent function types
compute their universe levels; a function ending in a proposition is a
proposition. Type-level functions and higher-order beta reduction work,
but the executable ABI is restricted to U64/I64 arguments and results.
There are no axioms, casts, unbounded loops or recursion, unsafe memory operations
or eliminators that inspect evidence to produce runtime data.

Erased binders must bind propositions; proof binders must be erased.
Evidence can be used in types and proof arguments, but not as runtime
data. Erased data/type parameters, inductive data types, equality beyond
U64 and dependent motives are future work.
Runtime indices are real U64 values; the prototype does not model them as unbounded mathematical naturals.

Both branches and all definitions are checked before normalization or
erasure. A false proof in an unused helper, erased argument or unreachable
branch is rejected. The true branch's proof cannot be used in the false
branch or escape in its result type. Foreign exports cannot require an
erased precondition or accept array pointers: the ABI cannot ensure that
a foreign caller supplies the evidence or a correctly indexed allocation.

Checking is bounded by one million checking steps, 200,000 arena nodes,
128 levels of nesting. The `.jhc` parser also enforces a
1 MiB/50,000-token source limit. Exhaustion
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
The same suite now parses `.jh` programs, compares their MIR with the
corresponding `.jhc` programs, and compares host execution with the
independent evaluator. It checks proof forwarding, nested/shadowed binders,
signed and unsigned extremes, the entry wrapper, source JSON diagnostics,
formatter preservation and explicit rejection of unsupported syntax and ABI
preconditions. Both targets emit objects at `-O0` and `-O2`.
`tests/core_equality.py`, called by the same suite, also compares both
frontends' equality programs and objects with the independent evaluator.
It exercises symbolic symmetry/transitivity lemmas, bound/index rewriting,
reflexive computation, nested/shadowed binders and arbitrary U64 inputs.
Negative cases reject false equality, wrong transport direction or source
proof, runtime/type/array transport, equality reflection, scope escapes,
erased runtime uses and proof ABI preconditions. Kernel unit tests bypass
both frontends to check false reflexivity, the proposition-only restriction,
reflexive reduction and graph integrity for the new terms.
`tests/core_chain.py` adds the declared equality chain to this suite,
including neutral chain checking, reflexive and multiple-step reduction,
captured motives/cases, shadowing and a second result proposition family.
It compares both frontends' MIR and native execution at both optimization
levels and emits objects for both targets. Negative cases reject forged
induction hypotheses, wrong edge/tail/result indices, unchecked dead cases,
runtime elimination, scope escapes, proof ABI preconditions and deep
proofs that exhaust limits. Additional raw kernel tests bypass both
frontends, recheck a normalized induction result and reject an unused bad
step and cyclic inductive graphs.
`tests/core_inductive.py` adds the graph example, families without indices
or constructors, a family used by a later one, and both frontends' MIR and
native execution. Its negative cases reject non-positive occurrences
(under an arrow, in an index or field type), relevant or non-`u64` fields,
wrong results or arities, forward and duplicate names, partial or false
constructors, missing, extra or false cases, forged hypotheses, data
motives, runtime evidence and deep evidence that exhausts limits. Kernel
unit tests construct families without either frontend and reject
non-positive fields, misordered declarations, missing cases and data
motives.
`tests/core_loop.py` adds the loop example: both frontends' MIR and
native execution against the evaluator, overflow traps at `-O0` and
`-O2` (from literals, products and inside loops), constant folding and
the empty loop, and rejection of u64 arithmetic, other operators, loop
bounds above an array's length, a wrong index or bound, runtime uses of
the bound, wrong body arities or types and array exports. Kernel unit
tests check that overflow is not folded, that loops are not unrolled
and that a body needs exactly its erased bound.

The next stages of the replacement are:

1. Extend ordinary `.jh` elaboration only as additional program operations
   and their guarantees are supported by this same core.
2. Extend the logical foundations beyond U64 equality and declared
   propositions: dependent motives, inductive data types, erased indices,
   u64 arithmetic on indices with overflow evidence and inequality
   lemmas, equality of other types and reusable lemma
   libraries. Specify normalization, universe
   and erasure rules before enabling them.
3. Add runtime operations with explicit ownership/effect rules, including
   borrowed and mutable memory and dynamic allocation. Extend the direct
   lowering of checked programs rather than adding a separate Horn model.
4. Establish the kernel's metatheory and the preservation obligations for
   source elaboration, erasure and lowering. External proof tools may
   validate this small trusted foundation; they are not a required user compilation stage.
5. Retire legacy verification paths as their source programs and enabled
   guarantees move to the core. Reproducing the legacy certificate format
   or preserving its implementation is not a migration requirement.
