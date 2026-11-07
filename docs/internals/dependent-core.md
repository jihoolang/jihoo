# Native dependent core

This page is the design. What the kernel accepts is specified in
[the core specification](core-spec.md).

The replacement direction for verification is to check the program and
its proofs in one native core, then erase and lower that checked program.
It does not reconstruct the program's execution in another proof system:
such a translation would itself be trusted, and would be much larger than this
kernel. The kernel stays small by providing general rules (such as declared
inductive propositions) rather than built-in special cases.

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

The core path does not call the existing verification-condition generator.
Unmarked `.jh` files retain the existing verifier and its
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
| `enum E { V(T, ...) ... }`, `E.V(x, ...)` | a [data type](#data-types) and a value of it |
| `match v { V(x, ...) => e, ... }` | case analysis into the expected type |
| `F(a, ...)`, `c(x, ...)` | a declared proposition; its constructor, fully applied |
| `p: erased(P)` | erased Pi/Lam binder of proposition `P` |
| `n: erased(u64)` | an [erased index](#erased-indices-and-parameters): a u64 for types and evidence only |
| `buffer(n)`, `alloc(n, x)` | an [owned buffer](#owned-buffers) of n i64 values; a new one, each x |
| `load(b, i, p, fn(x, b) { k })`, `store(b, i, v, p)`, `free(b, rest)` | read b[i] and continue with b; write in place; free a buffer or heap data, then `rest` |
| `xs: ref T`, `let x = v` | a [borrow](#borrows) of a buffer or heap data; a local, which may end a borrow |
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
| `i + j` on `u64` | [addition in the naturals](#index-arithmetic-and-order); overflow traps |
| `lt_add(a, b, c, p)`, `lt_cancel(a, b, c, p)`, `lt_le(x, y, z, p, q)` | rules of the order of the naturals |
| `sub(a, b, p)`, `zero_le(a)` | `a - b` given `p: Lt(b, a + 1)`; evidence of `Lt(0, a + 1)` |
| `refine(fn(x) { P(x) })` | [refinement](#refinements): a u64 with erased evidence of `P` |
| `pack(a, p)`, `witness(s)`, `proof(s)` | a refinement from `p: P(a)`; its u64; its evidence |

`n` and `i` are ordinary runtime U64 parameters. `[i64; n]` records the
length symbolically in the core; it does not evaluate `n` as a legacy
compile-time array size. The generic helper is checked once with symbolic
`n`, `xs`, `i` and `p`, before any caller substitutes a concrete array.
`erased(P)` marks a proof binder; it is not a `comptime` parameter or a
request to fix a value during specialization. `comptime` and `sink`
parameters are rejected in this subset; `inout` is described in
[inout parameters](#inout-parameters). A helper can forward
proofs or return `Lt(i, n)`, `Eq(a, b)` or declared evidence; the checker controls their runtime
relevance. Every definition and both branches are checked, including
unused helpers and discarded proof arguments.

Functions have explicit parameter and result types (except the result-free
inout functions described below). Blocks may have local statements and finish
with a value expression. They may refer only to earlier definitions, and
calls supply exactly the declared number of arguments. Expressions are
names, checked integer literals (including negative I64 literals), arrays,
blocks, calls and the operations above. Integer literals take the
expected scalar type; array elements are I64 and indices/lengths are U64.
Without an expected type, arithmetic looks through literal-only subexpressions
for a nonliteral operand: `1 + n` and `(1 + 2) + n` infer U64 when `n` is U64,
just as `n + 1` does. Literal-only arithmetic defaults to I64. This neither
coerces mixed scalar types nor changes overflow checks.
`erased` is allowed only as the outer parameter annotation. The forms
`erased`, `Lt`, `Eq`, `if_lt`, `if_eq`, `refl`, `transport`, `induct`,
`fold`, `lt_add`, `lt_cancel`, `lt_le`, `sub`, `zero_le`, `refine`, `pack`, `witness`, `proof`, `index`, `decide_lt`, `u64`, `i64` and the entry symbol
`__jihoo_dependent_main` are reserved in marked modules. Functions,
propositions, constructors and import aliases share a namespace within each module. A branch
binder may shadow another local; de Bruijn indices preserve its scope.

Exports accept U64/I64 values and return U64/I64 values or
refinements, and cannot require proof preconditions from foreign callers. Without `--lib`, the entry must be an
ordinary `fn main() -> i64`; its result becomes the process exit status
through the existing native entry wrapper. With `--lib`, only explicitly
exported functions are emitted. Helpers, including a non-exported `main`,
are still checked. A compilation needs at least one runtime export or an
entry point. `check` validates this executable subset, including its ABI,
without LLVM or a linker.

Imports of ordinary modules, item attributes, contracts, foreign declarations, other profiles,
implicit proof search, ordinary `if`/index syntax,
u64 products, the `-` operator on u64 (use `sub`), division and comparison operators,
general runtime closures/recursion and unrestricted mutable memory are outside
this subset and rejected. Recursive data, structural recursion, local statements,
buffers and inout mutation are supported as described below. Marked modules cannot be imported by the
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
`emit-obligations` and the `test` harness are explicitly
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
one U64 binder (optionally annotated `k: u64`) and a proposition as their single expression.
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
  arity of `u64` indices. The telescope is checked as written, before
  normalization, and while its constructors are checked the family is
  not yet in scope, so any other occurrence (under an arrow, in an index,
  in another field's type, or one that beta reduction would remove) is
  rejected, and evidence inside the telescope is checked even where
  reduction would remove it. This is strict positivity,
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

Not yet supported for propositions: motives depending on the evidence, families
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
Optional annotations, such as `fn(i: u64, p: Lt(i, n), acc: i64) -> i64 { acc }`,
are checked against it, without changing which parameters are erased. An explicit
`erased(T)` annotation requires an erased binder. Parameters are checked in order,
so a later annotation sees earlier binders; duplicate names within a lambda or
extended data motive are rejected. The checker validates annotations before
conversion so that normalization cannot discard malformed evidence in them.
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
an i64 value, so arithmetic cannot change what a proof means. U64
values do appear in propositions; their addition is described
[below](#index-arithmetic-and-order).

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

## Index arithmetic and order

U64 terms denote natural numbers, and `+` on them is addition in the
naturals. At run time it is checked: a sum that does not fit traps
rather than wrap. So every U64 value a program computes is the natural
number its term denotes, and a proof about the naturals holds of the
values the program uses. Machine wrapping is never assumed: `Eq(2^64 - 1
+ 1, 0)` has no proof, and `decide_lt` decides only closed inequalities
whose sides fit a U64. Since the order of a sum's operands cannot change
whether its total fits, reordering operands keeps trap behavior.

Conversion compares sums in a canonical form: the variables in order,
then other terms, then the constant, with literals added and zero
dropped. So `(i + 1) + 1` and `2 + i` are the same term. A constant part
that does not fit a U64 leaves the sum as written. `Strict`, which only
orders the evaluation of traps, does not change a term's meaning and is
ignored by conversion.

`a <= b` is written `Lt(a, b + 1)`. Besides `decide_lt`, the kernel has
three rules of the order of the naturals:

```text
lt_add(a, b, c, p : Lt(a, b))         : Lt(a + c, b + c)
lt_cancel(a, b, c, p : Lt(a + c, b + c)) : Lt(a, b)
lt_le(x, y, z, p : Lt(x, y), q : Lt(y, z + 1)) : Lt(x, z)
```

`lt_le` (x < y <= z gives x < z) says the order is discrete: it holds
in the naturals but not in the reals, where the other rules also hold,
so it cannot be derived from them. The usual facts are ordinary lemmas:
`Lt(a, a + 1)` is `lt_add(0, 1, a, decide_lt(0, 1))`, weakening
`Lt(a, b)` to `Lt(a, b + 1)` is `lt_le(a, b, b + 1, p, lt_add(0, 2, b,
decide_lt(0, 2)))`, and transitivity follows from weakening and `lt_le`.
u64 products are not supported.

[`examples/core_order.jh`](../../examples/core_order.jh) and its
[core equivalent](../../examples/core_order.jhc) derive weakening and
transitivity and then:

- `neighbours(n, xs: [i64; n + 1])` multiplies `xs[i]` and `xs[i + 1]`
  for each `i < n`, with `lt_add(i, n, 1, p)` for the second load;
- `prefix(k)` compares `k` with 5 once and then sums the first `k`
  elements of a length-4 array, using `lt_le(i, k, 4, p, q)`: `i < k <= 4`;
- `next(i)` computes `i + 1` at run time, compares it with the length and
  loads at it; `next(2^64 - 1)` traps in the addition.

Their MIR has the comparisons and the checked additions, and no bounds
assertions or evidence. In `.jhc` the forms are `(uadd a b)`,
`(lt-add a b c p)`, `(lt-cancel a b c p)` and `(lt-le x y z p q)`.

### Subtraction

`sub(a, b, p)` is `a - b` in the naturals and needs evidence `p` of
`b <= a`, `Lt(b, a + 1)`. It never underflows; at run time it is an
ordinary subtraction, and its evidence is erased. The `-` operator on
u64 is rejected, since it would need that evidence. `zero_le(a)` is
evidence of `Lt(0, a + 1)`: without it no rule gives a lower bound for a
variable.

Conversion cancels subtraction, which is valid in the naturals given its
evidence: `a - b` is the rest of `a` when `b`'s variables, other terms
and constant are among `a`'s, so `(i + 2) - 1` is `i + 1` and closed
subtractions compute; and a sum containing `x - y` and all of `y`'s parts
is the sum with `x` in their place, so `(k - 1) + 1` is `k`. Two
subtractions of the same terms are the same term whatever their
evidence (proof irrelevance). There is no partial cancellation:
`(k - 1) + m` is not `(k + m) - 1`. Cancellation keeps the evaluation
of what it removes: `(k + 1) - 1` is `k` in conversion, but at run time
the addition is still evaluated, through `Strict`, so a `k + 1` that
would overflow still traps.

[`examples/core_sub.jh`](../../examples/core_sub.jh) and its
[core equivalent](../../examples/core_sub.jhc) prove
`Lt(n - (i + 1), n)` for `i < n` from `zero_le(i)` and cancellation
(`d < d + (i + 1)`, which is `n`), so `reversed` multiplies `xs[i]` with
`ys[n - 1 - i]` in a loop. `last(k)` loads `xs[k - 1]` after checking
`0 < k` and `k < 5`, with `pred(k, p)` a runtime helper and
`Lt(pred(k, p), k)` a lemma proved by cancellation. Their MIR has the
comparisons and the two subtractions, and no bounds assertions. In
`.jhc` the forms are `(usub a b p)` and `(zero-le a)`.

## Refinements

A refinement `refine(fn(x) { P(x) })`, `{x : U64 | P x}`, is a U64
together with erased evidence that `P` holds of it. A function can
return a value and what is known about it, which a caller then uses
without a separate lemma:

| term | type |
|------|------|
| `refine(P)` | `Type 0`, for `P : U64 -> Prop` |
| `pack(a, p)` | `refine(P)`, for `a : U64` and `p : P(a)` |
| `witness(s)` | `U64`, for `s : refine(P)` |
| `proof(s)` | `P(witness(s))`, erased |

In source, `pack` takes `P` from the expected type: a function's result,
a parameter or a branch of one; in `.jhc` it is written
`(pack P a p)`. A refinement is data, so a binder of one is not erased,
and `proof(s)` is evidence, usable only where evidence is. There is no
subtyping: `refine(fn(j) { Lt(j, n) })` is not `refine(fn(j) { Lt(j, n
+ 1) })`; a user lemma repacks the witness with weakened evidence.

`witness(pack(a, p))` is `a` and `proof(pack(a, p))` is `p`. The witness
of a branch is the branch of its alternatives' witnesses, so
`witness(if_lt(i, n, fn(p) { pack(i, p) }, pack(0, z)))` is the branch
choosing `i` or `0`, and the proof of a branch stays a neutral proof of
`P` at that branch. Packs with the same witness are the same whatever
their evidence (proof irrelevance). At run time a refinement is its U64:
`pack` lowers to its witness and `witness` to its argument, and its
predicate and evidence are neither stored nor evaluated. A witness that
can trap is still evaluated when it is passed, even if unused, as any
argument is. An export may return a refinement, received by a foreign
caller as a `uint64_t`; it cannot take one, since the caller could not
supply the evidence.

[`examples/core_refine.jh`](../../examples/core_refine.jh) and its
[core equivalent](../../examples/core_refine.jhc) define

```jihoo
fn below(i: u64, n: u64, nz: erased(Lt(0, n))) -> refine(fn(j) { Lt(j, n) }) {
    if_lt(i, n, fn(p) { pack(i, p) }, pack(0, nz))
}

fn at(n: u64, xs: [i64; n], s: refine(fn(j) { Lt(j, n) })) -> i64 {
    index(xs, witness(s), proof(s))
}
```

and `pred(k, p) : refine(fn(j) { Eq(j + 1, k) })`, `k - 1` with its
successor equation, from which `last(k)` derives `k - 1 < 4` for
`k < 5`. `clamp(i)` exports `below(i, 4, ...)` as a `uint64_t`. Their
MIR has the comparisons, one subtraction and the loads: no pairs,
evidence or bounds assertions. In `.jhc` the forms are `(Refine P)`,
`(pack P a p)`, `(witness s)` and `(proof s)`.

Refinements carry U64 values only; dependent pairs of other types remain future
work. Refinement accumulators are supported by the dependent loops described
below in "Loops whose invariants are types".

## Data types

An `enum` in a marked module declares a data type, of `Type 0`. Its
variants' fields are positional and are `u64`, `i64`, refinements,
earlier data types or `erased(P)`; a field cannot name another, so a
refinement field carries what is known about a value. `E.V(x, ...)`
builds a value, with every field, and `E.V` one without fields; variants
are always qualified when built and bare (or qualified) in patterns.

```jihoo
enum Slot {
    Empty
    Full(refine(fn(j) { Lt(j, 4) }))
}

fn read(xs: [i64; 4], s: Slot, missing: i64) -> i64 {
    match s {
        Empty => missing
        Full(j) => index(xs, witness(j), proof(j))
    }
}
```

`match v { ... }` has one arm per variant, in any order, binding every
field by name or `_`, without guards; its type is the expected type,
which every arm has. `induct(fn(x) { P(x) }, case..., v)` proves a
proposition about any value by cases, one per variant in declaration
order, as for inductive propositions:

```jihoo
fn position_bound(s: Slot) -> Lt(position(s), 4) {
    induct(fn(t) { Lt(position(t), 4) }, decide_lt(0, 4), fn(j) { proof(j) }, s)
}
```

In the kernel both are `Elim(F, P, cases, v)`, whose motive `P : F ->
Prop` or `P : F -> Type 0` depends on the value: the case for a variant
with fields `x...` has type `(x...) -> P(V(x...))`, and the elimination
has type `P(v)`. `match` is the motive that ignores the value. Into
`Prop` it is evidence and erased; into `Type 0` it is runtime code, and
its value and cases are runtime terms. A larger motive, returning types,
is rejected. The kernel checks a declaration as for propositions: the
type is not visible to its own fields, so it is not recursive, and
runtime fields are first-order.

A flat data value has no runtime representation. Case analysis of a variant
reduces to the case applied to the fields. Runtime normalization distributes
a case on a branch into a branch of the cases (shifting over the true
branch's evidence binder), and a case on `Strict(t, y)` becomes `t` then
the case of `y`. Pure conversion retains an elimination on a symbolic
branch: its dependent motive may give the alternatives different types,
which an ordinary branch cannot express. Concrete choices still compute.
Evaluation still goes the value, then the case. Since an export cannot take or return data, and a
loop accumulator is an i64, every case analysis in an export reduces
away. A data value that is passed but not used is evaluated field by
field for its traps; erased fields are not evaluated. The cost is that a
case on a branch duplicates the cases in each alternative, bounded by
the kernel's limits.

[`examples/core_data.jh`](../../examples/core_data.jh) and its
[core equivalent](../../examples/core_data.jhc) read a table through a
`Slot`, prove the slot's position in range by cases, and nest a
`Reading` with i64 fields in a `Sample`. `measure(i, x)` builds a
sample from two branches and takes it apart in two matches; its MIR
has the two comparisons, a product, a sum and a load. In `.jhc`,
`(data E (V TYPE) ...)` declares a data type whose constructor types are
telescopes ending in `E`, and `(induct E P case ... v)` with
`P = (lam x E T)` takes a value apart.

Recursive data, structural recursion, data accumulators and runtime layouts
are implemented in the later sections below. Data in exported signatures
remains subject to the supported ABI described by the core specification.

## Erased indices and parameters

A parameter `n: erased(u64)` is an erased index: a u64 that types and
evidence may use, but no runtime term. It is never passed or evaluated,
so an argument that would trap does not, and an export cannot have one.
A helper over arrays of any length need not take the length at run time:

```jihoo
fn head(n: erased(u64), xs: [i64; n + 1]) -> i64 { index(xs, 0, zero_le(n)) }
```

An erased index denotes a natural number like any u64 term in a type;
the array's actual length is the length its type states, because the
array was built with that length or passed with that type. Erased
binders are otherwise propositions: an erased `i64` is rejected.

A data type can have u64 parameters, `enum Slot(n: u64) { ... }`, which
its variants' fields may use:

```jihoo
enum Slot(n: u64) {
    Empty
    Full(refine(fn(j) { Lt(j, n) }))
}

fn read(n: erased(u64), xs: [i64; n], s: Slot(n), missing: i64) -> i64 {
    match s {
        Empty => missing
        Full(j) => index(xs, witness(j), proof(j))
    }
}
```

`Slot(4)` and `Slot(5)` are different types. In the kernel each
constructor binds the parameters first, as erased u64 fields, and returns
them unchanged, which the kernel checks; case analysis of a `Slot(n)`
substitutes the `n` of the value's type into each case, so the `Full`
arm knows `j < n` for that `n`. Patterns bind only the variant's own
fields, and `Slot.Full(s)` takes its parameter from the expected type:
a function's result, a parameter or an arm. A parameter is a field of
the value, erased, so it is never evaluated.

When no surrounding type is available, write the parameters on the constructor:

```jihoo
let empty = Slot(n).Empty
let full = Slot(4).Full(pack(2, decide_lt(2, 4)))
match Slot(3).Empty { Empty => 7; Full(j) => witness(j) }
```

`Slot(n).Variant(fields...)` supplies the same field context as a local
`Slot(n)` annotation; nested constructors and `pack` can use that context.
Imported families use `module.Slot(n).Variant`, including import aliases.
Every parameter must be supplied in declaration order. An explicit qualifier
must agree with any surrounding expected type, up to existing core conversion.
The compiler checks the written qualifier before normalization, including proof
terms in its indices, so an invalid proof cannot disappear during conversion.
The parameters remain erased and are not evaluated at runtime. Existing private
family/field restrictions and ownership checks apply unchanged; this is source
elaboration into the existing `Con` term, not a new kernel rule.

In `.jhc`, `(data E N P (c TYPE) ...)` declares a data type with `N`
indices, the first `P` of them parameters; constructors take the
parameters explicitly, `(Full n s)`. The other indices are true indices,
which a constructor may return as any u64 terms, and the motive of a
case analysis is a function of them and the value:
`P : (indices) -> E(params, indices) -> Prop or Type 0`. Each case has
type `(fields) -> P(its result's indices, c(params, fields))`, so it
learns the indices. `tests/core_indexed.py` defines

```text
(data View 1 0
  (Zero (View 0))
  (Succ (pi k U64 (View (uadd k 1)))))
```

and returns, for any `v : View n`, a refinement below `n + 1`, by a case
on `v` whose motive depends on `n`. Source `enum` declarations have
parameters but no other indices.

[`examples/core_indexed.jh`](../../examples/core_indexed.jh) and its
[core equivalent](../../examples/core_indexed.jhc) read tables of
lengths 3 and 5 through slots, widen a `Slot(3)` to a `Slot(5)` with
evidence of `3 <= 5`, prove a slot's position below its `n` by cases and
read the head of a nonempty array. Each export takes only its runtime
arguments; the MIR has no length, tag, evidence or bounds assertion.

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
| `(data E (c type) ...)` | top-level declaration of a data type, without indices |
| `(data E n p (c type) ...)` | a data type with `n` u64 indices, the first `p` parameters |
| `(Buffer n)`, `(alloc n x)` | an owned buffer of n I64 values; a new one |
| `(case F P case ... v)` | one level of case analysis of heap data: the node is freed |
| `(load b i p k)`, `(store b i v p)`, `(free b rest)` | read and continue with `k x b`; write in place; free, then `rest` |
| `(drop F v rest)` | free heap data `v` of type `F` and every node it owns, then `rest` |
| `(Ref T)`, `(lend x f g)` | a borrow of an owned `T`; run `f` on a borrow of `x`, then `g` on its result and `x` (of a variable: [dependent](#dependent-lends)) |
| `(view F T case... r)`, `(view-rec F T case... r)` | read borrowed heap data one level, or recursively, freeing nothing |
| `(view F (lam r (Ref F) T) case... r)` | the same, with a result that [depends on the borrow](#views-whose-result-depends-on-the-borrow); `T` may be a function type, and the view applied to its arguments |
| `(loop n T init body)` | a loop [whose invariant is a type](#loops-whose-invariants-are-types), or a proof by induction on the naturals |
| `(absurd T p)` | code that cannot run, of type `T`, with `p : Lt i 0` |
| `(borrow x)` | a borrow of the owned `x`, in types and evidence, or in the reader of a lend of `x` |
| `(deref r)` | the value a borrow `r` reads, in types and evidence only |
| `(F a ...)`, `(c x ...)` | a declared proposition; a constructor with all fields |
| `(induct F P case ... e)` | proposition-only structural induction on evidence of `F` |
| `(add a b)`, `(sub a b)`, `(mul a b)` | i64 arithmetic; overflow traps at run time |
| `(fold n init body)` | bounded loop; `body : (i : U64) -> Lt i n -> I64 -> I64`, erased bound |
| `(uadd a b)` | addition in the naturals; traps at run time beyond U64 |
| `(lt-add a b c p)`, `(lt-cancel a b c p)`, `(lt-le x y z p q)` | order rules of the naturals |
| `(usub a b p)`, `(zero-le a)` | `a - b` with `p : Lt b (a + 1)`; evidence of `Lt 0 (a + 1)` |
| `(Refine P)`, `(pack P a p)` | a U64 with evidence of `P : U64 -> Prop`; one, from `p : P a` |
| `(witness s)`, `(proof s)` | a refinement's U64, and its erased evidence of `P (witness s)` |
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
or eliminators that inspect evidence to produce runtime data, apart from
`absurd`, whose evidence is of `Lt(i, 0)` and which produces nothing. Data
types are eliminated into `Prop` or `Type 0`, never into types.

Erased binders must bind propositions or U64 indices; proof binders
must be erased. Evidence and erased indices can be used in types and
proof arguments, but not as runtime data. Erased type parameters,
recursive data types, equality beyond U64 and motives depending on
evidence are future work.
U64 terms denote natural numbers; runtime U64 addition traps instead of
wrapping, so computed values are those numbers.

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
`tests/core_order.py` adds the index-arithmetic example: both frontends'
MIR and native execution against the evaluator, u64 overflow traps from
runtime values, literals and unused arguments, and rejection of wrapped
literals, inequalities decided beyond U64, each rule with wrong premises
(including `<=` and `<=` for `<`), u64 subtraction and products,
unchecked or too-long computed indices and runtime evidence. Kernel unit
tests check canonical sums, that 2^64 is not 0, and the rules' premises.
`tests/core_sub.py` adds subtraction: both frontends' MIR and native
execution, cancellation, closed computation and proof irrelevance in
accepted lemmas, and rejection of missing, strict or reversed evidence,
underflow, partial cancellation, wrapped results, the `-` operator,
unchecked `k - 1` loads and runtime uses of evidence. Kernel unit tests
check cancellation and that `0 - 1` has no evidence. Conversion orders sum atoms
without the evidence ignored by equality: replacing a subtraction proof, even
inside a nested atom, leaves sums convertible. Source and core regressions cover
nested subtraction with distinct erased proofs and relevant operands that still
must differ. Raw kernel tests cover the same ordering rule for refinements and
erased `Give` results, without omitting their evidence from graph checks.
`tests/core_refine.py` adds refinements: both frontends' MIR and native
execution, projections, proof irrelevance, repacking with weaker
evidence and branches of packs; witnesses that trap are evaluated even
when unused, and erased predicates are not. It rejects false or
mismatched evidence, subtyping, wrong bounds, runtime proofs,
projections of u64 values, untyped packs, data predicates, erased
refinements and refinement arguments of exports. Kernel unit tests
check evidence at the witness, projection, erasure and the witness of a
branch.
`tests/core_data.py` adds data types: both frontends' MIR and native
execution, `match` with qualified, bare and `_` patterns, nested data,
proofs by cases (including nested induction) and closed computation.
Unused values are evaluated field by field for their traps, and erased
fields are not. It rejects missing, duplicate or guarded arms, wrong
field counts, matches without an expected type or on non-data, recursive
and higher-order fields, unqualified or unknown variants, false proofs
by cases, data in exports, erased data, large motives, motives of other
types and evidence fields used at run time. Kernel unit tests reject
recursive and indexed data and large or mistyped motives, and check that
a case on a branch distributes only for runtime lowering. Preservation
fixtures also cover dependent heap cases and borrowed views, both comparison
forms, and outer variables under evidence binders. Every pure normal form
must recheck; this remains a regression check, not a soundness proof.
`tests/core_indexed.py` adds erased indices and parameterized and
indexed data: both frontends' MIR and native execution, exports without
erased arguments, unevaluated erased arguments and kept parameterized
value traps, widening and closed computation, and a `.jhc` view whose
cases learn their index. It rejects erased values in runtime terms
(results, arguments, branches, loops, witnesses, fields, sums), erased
i64, wrong parameters or lengths, values without an expected type,
unparameterized uses, false proofs by cases, unwidened slots, erased
exports and parameter binders in patterns; in `.jhc`, parameters bound
late, relevant or changed, motives without their indices or with other
parameters, and wrong index cases. Kernel unit tests check parameter
binding and erased indices in runtime terms.
`tests/core_buffer.py` adds owned buffers: both frontends' MIR and
native execution against the evaluator, which tracks every buffer it
allocates; native objects are linked with counting `malloc`/`free`
wrappers, and every call must free exactly what it allocates, including
a u64 that touches memory inside a cancelled subtraction. Size overflow
traps and a failed allocation stops the program. It rejects leaks and
unequal branches in `.jhc`, where no free is inserted, double frees,
uses after free, two calls, captures by loop bodies,
lambdas and partial applications (also of a fresh buffer), out-of-bounds
or unchecked indices, wrong lengths, lost stores, erased buffers,
buffers in exports, data and arrays, and malformed continuations.
Kernel unit tests check the exact-once count and that an allocating
argument is bound, not substituted.
`tests/core_list.py` adds recursive data: both frontends' MIR and native
execution against the evaluator, which takes every node apart once;
native objects count `malloc` and `free`, and every call frees what it
allocates. Valid programs include `tail` by `match`, binary trees with
a proof by induction that mirroring keeps the leaves, and a
parameterized list of checked indices. It rejects double
uses, runtime uses of a recursion's rest, captures by recursion cases,
heap data in exports, false inductions, changed
parameters, flat fields of heap data and loop captures. Kernel unit
tests check boxing, one-level analysis and that sums convert in any
order but run in theirs.
`tests/core_scope.py` adds frees inserted where ownership ends: both
frontends' MIR and native execution of the example against the
evaluator, counting every node and buffer; twelve implicit programs that
must compile to the same MIR as their explicitly freed versions and free
what they allocate; and rejection of double uses, uses after free, a
free in one branch and again after it, frees of scalars and flat data,
captures, and, in `.jhc`, leaks and drops of flat data, of another type,
of a buffer or twice. Kernel unit tests check that heap data is dropped
exactly once and that freeing is no computation in conversion.
`tests/core_borrow.py` adds borrows: both frontends' MIR and native
execution against the evaluator, whose borrows expire with their lend
and fail any later read; recursions over borrows free nothing; trees and
lists read through borrowed fields, a borrow in one branch and in a
match arm; counted allocations and frees. It rejects borrowing and
consuming in one expression (either order), uses after a move, escaping
or returned borrows, consuming, freeing, storing to or loading from a
borrow, unchecked indices, two owners in one expression, temporaries,
borrows in exports, of scalars or flat data and in data fields, and
captures by a recursion over a borrow; in `.jhc`, lends whose result is
a borrow, a function or of the wrong type, of a scalar or through
another type's borrow, that also use or leak the owner, views of an
owner, freeing or owning a borrowed field, and wrong arities; and five whole programs that a type
variable or a continuation's closure would otherwise make unsound, while
a polymorphic identity on i64 is still accepted. Kernel unit tests check
that no borrow outlives its lend and that views give borrowed fields.
`tests/core_borrow_proof.py` adds borrows in types and evidence: both
frontends' MIR and native execution against the evaluator, which
evaluates evidence and `(borrow x)` without consuming or freeing memory;
counted allocations and frees; proofs by computation through views and
lends and by induction, lemmas applied to temporaries and preconditions
on consumed values. It rejects false computations, unproved
preconditions and a proof that needs induction; in `.jhc`, a borrow in
code that runs, of a scalar or of a borrow. Kernel unit tests check
that views and lends compute in the pure model only, and that a
`Borrow` is evidence only.
`tests/core_lend.py` adds dependent lends: both frontends' MIR, with no
bounds check on a load at a borrowed list's length, and native
execution against the evaluator with counted allocations; facts kept
across lets that lend the same list; and 6 source and 10 core
rejections of evidence about the wrong list, owners used in a reader,
before a lend, twice or never after it, and borrows by name outside
their lend. Kernel unit tests check that the owner given back is used
exactly once, by either name.
`tests/core_borrow_induct.py` adds proofs by induction over borrows:
both frontends' MIR, from which the induction is erased, and native
execution against the evaluator, which reads `(deref r)` as the value r
borrows; a lemma over a borrowed tree used at run time; and 6 source and
5 core rejections. Kernel unit tests check both of `Deref`'s reductions
and that it is evidence only.

## Owned memory plan

Heap memory in the core follows ordinary jihoo's ownership: allocation
is explicit, there is no garbage collector, and memory is freed either
explicitly or when its owner's scope ends. The two are layered so that
the trusted part stays small:

| layer | rule | trusted |
|-------|------|---------|
| kernel | an owned value is used exactly once at run time: freed, moved into a call or a constructor, taken apart, or returned | yes |
| source | allocation is explicit; the elaborator inserts `free` where an owner's scope ends, and code may also free explicitly | no |

A wrong free inserted by the elaborator is a kernel error, never a leak,
double free or use after free, and lowering translates a checked `free`
to a call without deciding anything. This is a quantitative type
discipline (as in Idris 2): erased binders are used zero times at run
time, owned ones exactly once, and scalars any number of times. A use in
a type or in evidence is not a use at run time, so a proposition can
still mention a value that has been freed or moved.

The steps, each an ordinary slice with its tests:

1. The kernel's linearity check, owned heap buffers `buffer(n)` with
   proved-bounds loads and stores, and explicit `free`; a loop may carry a
   buffer as its accumulator. Implemented: see
   [owned buffers](#owned-buffers).
2. Recursive data types as heap nodes (a tag and fields), with the
   existing strict positivity. Implemented: see
   [recursive data](#recursive-data-on-the-heap).
3. Structural recursion that consumes them: a case on a node frees it, and
   lowering emits a recursive function; termination is structural.
   Implemented with step 2.
4. Frees inserted by the source elaborator where an owner's scope ends.
   Implemented: see [frees where ownership ends](#frees-where-ownership-ends).
5. Borrows: reading a value without consuming it, as in `length(xs)`
   with `xs: ref List`. Implemented: see [borrows](#borrows).

## Owned buffers

`buffer(n)` is an owned heap buffer of n i64 values, the first step of
the [plan](#owned-memory-plan). Every owned value is used exactly once
at run time:

| form | type | use of `b` |
|------|------|------------|
| `alloc(n, x)` | `buffer(n)`, n copies of x | a new owner |
| `load(b, i, p, fn(x, b) { k })` | the type of `k` | `b`, given back to `k` with `x = b[i]` |
| `store(b, i, v, p)` | `buffer(n)`, `b` with `v` at `i` | `b`, returned |
| `free(b, rest)` | the type of `rest` | `b`, freed before `rest` |

`p` is evidence of `Lt(i, n)`, so loads and stores have no bounds
checks. Passing a buffer to a function or returning it also uses it.
A loop may carry a buffer as its accumulator, which the body uses once
and returns:

```jihoo
fn running(n: u64, b: buffer(n + 1)) -> buffer(n + 1) {
    fold(n, b, fn(i, p, acc) {
        load(acc, i, weaken(i, n, p), fn(x, acc) {
            load(acc, i + 1, lt_add(i, n, 1, p), fn(y, acc) {
                store(acc, i + 1, x + y, lt_add(i, n, 1, p))
            })
        })
    })
}
```

The kernel counts, for each owned binder of a runtime function, the
uses of the bound value at run time: types and evidence are not
visited, both branches of a comparison and every case of a match must
use it alike, and the count must be one. A function's own later
parameters are part of it, but no other function value can capture an
owned value: not a lambda, a loop body (which runs many times), nor a
partial application, which also cannot take a fresh buffer. A load's
continuation and a match's cases run once and may use one. So the
kernel rejects a buffer that is never freed, freed twice, used after it
is freed or passed to two calls. In source, the elaborator
[inserts the frees](#frees-where-ownership-ends) a scope needs, checked
by this same count.

Memory operations are not computed by normalization. When beta
reduction would substitute an argument that touches memory, the redex
stays and binds it, so it is evaluated exactly once, and an application
of such a redex moves inside it. u64 cancellation and loop
eta-expansion never drop or repeat such a term. A buffer is a pointer
at run time: `alloc` calls `malloc` for `8 * n + 8` bytes (checked: an
overflowing size traps; the extra element keeps an empty buffer a
distinct allocation), stops the program with "allocation failed" when
it returns null, and fills the elements; `load` and `store` are offsets;
`free` calls `free`. `malloc` and `free` are declared after the exports
when a buffer is used. Exports cannot take or return buffers and arrays
cannot contain them; [a data type can hold one](#a-vector-with-contracts-as-types).

[`examples/core_buffer.jh`](../../examples/core_buffer.jh) and its
[core equivalent](../../examples/core_buffer.jhc) compute running sums
in place over a buffer of runtime length and read a three-element table
at a runtime index. Each export's MIR calls `malloc` and `free` once
and has no bounds checks; valgrind finds no leaks or errors. In `.jhc`
the forms are `(Buffer n)`, `(alloc n x)`, `(load b i p k)` with
`k = (lam x I64 (lam b (Buffer n) ...))`, `(store b i v p)` and
`(free b rest)`.

## Recursive data on the heap

A data type with a recursive field, or with a field that is itself on
the heap, is *boxed*: the kernel decides this from the declaration. Its
values are heap nodes, owned like buffers and used exactly once.

```jihoo
enum List {
    Nil
    Cons(i64, List)
}

fn sum(xs: List) -> i64 { induct(fn(t) { i64 }, 0, fn(x, rest, ih) { x + ih }, xs) }

fn head_or(xs: List, missing: i64) -> i64 {
    match xs {
        Nil => missing
        Cons(x, rest) => x + drop(rest)
    }
}
```

`List.Cons(x, xs)` allocates a node that owns `xs`. There are two ways
to take a value apart:

- `match` is one level of case analysis (kernel term `Case`): the node is
  freed and each arm receives all of its fields, recursive ones as owned
  values that the arm must use, as `rest` above.
- `induct(fn(t) { T }, case..., v)` is structural recursion (`Elim`).
  Each case receives the fields, the recursive ones erased, followed by
  the result for each recursive field: `fn(x, rest, ih)`. The recursion
  consumes the rest, so a case can mention `rest` only in types and
  evidence. With `T` a type it is runtime code; with `T` a proposition
  it is a proof by induction, erased:

```jihoo
fn doubled_length(xs: List) -> Eq(length(doubled(xs)), length(xs)) {
    induct(fn(t) { Eq(length(doubled(t)), length(t)) }, refl(0), fn(x, rest, ih) {
        transport(fn(k) { Eq(length(doubled(rest)) + 1, k + 1) }, ih,
            refl(length(doubled(rest)) + 1))
    }, xs)
}
```

The cases of a recursion run once per node, so they cannot use an outer
owned value; a match's arms run once and may. A parameterized type's
recursive fields keep its parameters, `enum Indices(n: u64) { None,
More(refine(fn(j) { Lt(j, n) }), Indices(n)) }`, and a heap type cannot
hold a flat data value, which has no representation. Erased binders may
now be data, which recursion uses for its recursive fields.

A node is `8 * (1 + fields)` bytes from `malloc`: the constructor's
index, then each runtime field (u64, i64, refinement or pointer) in
declaration order; erased fields and parameters take no space. `match`
loads the tag, switches, loads the fields, frees the node and runs the
arm. A recursion becomes a recursive MIR function of the node and of the
outer runtime values: it loads the fields, frees the node, calls itself
on each recursive field and then runs the case. Its depth is the depth
of the data, on the machine stack.

Normalization is in one of two modes. Conversion computes in the pure
model, where nodes are values: any argument is substituted and a known
node is taken apart without being built. Code to run, normalized by
lowering, binds an argument that allocates once instead, keeps traps
with `Strict`, and evaluates a sum's operands in their order. In the
pure model a sum's non-variable operands are sorted by structure, since
addition commutes in the naturals; a proof that needs commutativity of
variables gets it by `refl`.

[`examples/core_list.jh`](../../examples/core_list.jh) and its
[core equivalent](../../examples/core_list.jhc) build lists in a loop,
double, sum and measure them, take the head with `match` and prove that
doubling keeps the length. valgrind finds every node freed. In `.jhc`, a
`(data ...)` declaration with a recursive field is boxed, `(induct F P
case... v)` is the recursion and `(case F P case... v)` the one-level
analysis.

## Frees where ownership ends

Step 4 of the [plan](#owned-memory-plan). In source, an owned value (a
buffer or heap data) need not be freed by hand: the elaborator inserts a
free where it is no longer owned, and the kernel checks the result with
the same exactly-once count, so a wrong free is a compile error.

```jihoo
fn head_or(xs: List, missing: i64) -> i64 {
    match xs {
        Nil => missing
        Cons(x, rest) => x          // rest is freed
    }
}

fn sum_if(i: u64, xs: List) -> i64 { if_lt(i, 10, fn(p) { sum(xs) }, 0) }   // freed in the else branch

fn at(i: u64, b: buffer(3)) -> i64 {
    if_lt(i, 3, fn(p) { load(b, i, p, fn(x, b) { x }) }, -1)   // b freed after the load, and in the else branch
}
```

The elaborator applies two rules, innermost first:

- **Scopes.** A function's parameters, a match arm's fields, a load's
  continuation and the binders of a loop body or a recursion case each
  own their owned values. One that the scope's body does not use at run
  time is freed before the body: `free(rest, x)`.
- **Alternatives.** Exactly one branch of `if_lt` and `if_eq`, one arm of a
  `match` and one case of a flat data type's `induct` runs. An owned value
  of the enclosing scope that some alternative uses is freed at the start
  of each alternative that does not. So `sum_if` frees `xs` in its else
  branch, and a nested branch is balanced before the one around it.

Freeing at the start of a scope is the same program as freeing at its
end, since freeing has no other effect, and holds the memory for less
time. A value that a body uses twice or that a function captures is not
repaired: the kernel reports it. Proofs are left alone, since evidence
owns nothing at run time. Uses are counted by the kernel's own function,
but the elaborator's answer is not trusted: the whole result is checked.

`free(v, rest)` also frees heap data: the kernel term `Drop(F, v, rest)`
(in `.jhc`, `(drop F v rest)`) frees v, a value of boxed type F, and
every node it owns, then runs `rest`. Lowering makes one function per
type that switches on a node's tag, loads its fields on the heap, frees
the node and then frees each of them; its depth is the data's. In the
pure model of conversion, `free` and `drop` are their rest, since nodes
are values there; code to run keeps them.

[`examples/core_scope.jh`](../../examples/core_scope.jh) writes no
`free`, and its [core equivalent](../../examples/core_scope.jhc) writes
out the frees the elaborator inserts; both compile to the same MIR, and
valgrind finds every node and buffer freed. `tests/core_scope.py` checks
twelve more such pairs, from unused parameters to nested branches and
trees with a list inside.

## Borrows

Step 5 of the [plan](#owned-memory-plan). A parameter `xs: ref List` (or
`b: ref buffer(n)`) reads an owned value without consuming it. Passing
an owned local where a borrow is expected lends it, and the owner is
usable again after the expression that borrows it:

```jihoo
fn length(xs: ref List) -> u64 { induct(fn(t) { u64 }, 0, fn(x, rest, ih) { ih + 1 }, xs) }

export fn stats(n: u64, x: i64) -> i64 {
    let xs = repeat(n, x)
    let s = total(xs)                 // borrows xs
    let second = second_or(xs, -1)    // borrows it again
    s + second + sum(xs)              // consumes it
}
```

`match` and `induct` on a borrow read the nodes in place and free
nothing; the fields on the heap arrive borrowed, so `second_or` can call
`head_or(rest, missing)` on the tail. `index(b, i, p)` reads a borrowed
buffer. A borrow is copied freely; it cannot be freed, consumed, stored
or loaded from, and data, buffers and arrays cannot hold one.

The kernel has one rule that ends borrows, `Lend(x, f, g)`: f receives
`Ref(T)`, a borrow of the owned x : T, and its result A can hold no
borrow and is no function; g then receives that result and x itself. A
borrow is made only by a lend or by reading a field through another
borrow, so none outlives the lend that made it, and the owner, used once
by the lend, cannot be consumed while it is lent. The result type must
be known to hold no borrow: a scalar, a refinement, an array, a buffer
or data, not a type variable. `View(rec, F, T,
cases, r)` reads borrowed heap data: one level, or a structural
recursion whose cases receive the fields and the results for the
recursive ones. At run time a borrow is the owner's pointer, a lend runs
f and then g, and a view is the same switch and recursion as for owned
data without the frees.

The elaborator, which is not trusted, finds the lends. A block's value,
a `let` value, a match arm and an `else` value may each borrow one owned
local of their context: they are elaborated with a borrow binder for
each, and the one they use becomes a lend around them. After a `let`,
the rest of the block sees the owner again; after the others, the owner
is freed. So an expression that borrows a value cannot also consume it
(`total(xs) + sum(xs)` is a double use): bind the borrowing part with
`let` first. Only a named value is lent: `length(repeat(2, 1))` asks for
a `let`.

[`examples/core_borrow.jh`](../../examples/core_borrow.jh) and its
[core equivalent](../../examples/core_borrow.jhc), which writes out the
lends and views, compile to the same MIR: the recursions over borrows
call no `free`, and valgrind finds every node and buffer freed.

An independent review of this step found two ways around these rules,
which the kernel now rejects, and which `tests/core_borrow.py` keeps as
whole programs. First, a type variable is used without linearity: had it
been instantiated with a buffer, a function could use its argument
twice, and as a lend's result it could stand for a borrow. A type
argument at run time is therefore first order: no buffer, heap data,
borrow or function type occurs in it. Second, a continuation that
receives owned values (a load's, a lend's, a case's) runs once with the
arguments it is given; had its result been a function, that function
could hold those values and run twice. So such a result is not a
function type. The first and the closures of loads and cases predate
borrows.

Not yet supported: lending more than one owner in an expression,
lending a temporary, and returning a borrow from a function, which source
cannot write. To change a value, see [inout parameters](#inout-parameters). Types and evidence may borrow any
value: see [borrows in types and evidence](#borrows-in-types-and-evidence).

Not yet supported for heap data: mutual recursion, recursion depth
beyond the machine stack, and heap data in exports.

Not yet supported: buffers of other element types, and buffers in
exports and arrays. A data value
whose fields touch memory cannot yet be passed to a function: the
argument is bound once, and data has no runtime representation, so
lowering reports an error rather than evaluating it twice.

## Borrows in types and evidence

A function that reads a borrow applies in types and proofs to any value
of its type, as `length` does to an owned list here:

```jihoo
fn length(xs: ref List) -> u64 { induct(fn(t) { u64 }, 0, fn(x, rest, ih) { ih + 1 }, xs) }

fn doubled_length(xs: List) -> Eq(length(doubled(xs)), length(xs)) {
    induct(fn(t) { Eq(length(doubled(t)), length(t)) }, refl(0), fn(x, rest, ih) {
        transport(fn(k) { Eq(length(doubled(rest)) + 1, k + 1) }, ih,
            refl(length(doubled(rest)) + 1))
    }, xs)
}

fn head(xs: List, p: erased(Lt(0, length(xs)))) -> i64 { ... }   // consumes xs
```

Nothing in a type or in evidence runs, so nothing there is lent: the
kernel term `Borrow(x)` (in `.jhc`, `(borrow x)`) is a borrow of an owned
x : T, of type `Ref(T)`, and is allowed only where `infer` checks a
type or evidence (and in the reader of a [lend](#dependent-lends) of x). It is neither a use of x nor a lend, so x may be a
temporary such as `doubled(xs)`, a value moved or freed meanwhile (as in
`head`'s precondition) or a recursion's erased field. The elaborator,
untrusted, borrows in place wherever it elaborates a type or evidence:
types, the expressions of a proposition, erased arguments and the
evidence arguments of `refl`, `transport`, `index`, `decide_lt` and the
other rules. In code that runs, a borrow is still of a named value and
lent.

Conversion computes in the pure model, where a borrow reads the value it
borrows:

- `View(rec, F, T, cases, Borrow(v))` with v a known node applies the
  node's case to its fields, those on the heap as `Borrow` of them, and,
  in a recursion, to the view of each recursive field. A view of a
  branch is the branch of the views; `Strict` keeps its traps first.
- `Lend(x, f, g)` is `g(f(Borrow(x)), x)`.

Both reductions keep types: `f` expects a `Ref(T)`, and a view's case
receives exactly the `Borrow` of each heap field. Code to run keeps
lends and views, which read memory, and lowering never sees a `Borrow`,
since only types and evidence hold one. So `length(pair(x))` is 2 by
`refl(2)`, and so is `count_pair(x)`, which lends a local list to
`length` and frees it; `doubled_length` holds by induction on the owned
list, since a view of a constructor computes like the recursion that
built it.

[`examples/core_borrow_proof.jh`](../../examples/core_borrow_proof.jh)
and its [core equivalent](../../examples/core_borrow_proof.jhc) compile
to the same MIR, from which the proofs and preconditions are erased: the
only recursion left is `doubled`'s. `tests/core_borrow_proof.py` runs
both against the independent evaluator, which evaluates evidence without
consuming or freeing memory, and checks counted allocations and frees
and 7 source and 6 core rejections: false computations through views and
lends, a proof that needs induction, unproved preconditions, and a
`Borrow` in code that runs or of a scalar or a borrow. An independent
review found no unsound case.

A proof by induction over a borrow is one over the value it reads:
see [induction over a borrow](#induction-over-a-borrow). Evidence about
an owner applies to the borrow a lend makes of it: see
[dependent lends](#dependent-lends).

## Dependent lends

When a lend lends a variable, the kernel knows what its borrow reads
and what it gives back:

```jihoo
fn size(xs: ref List) -> refine(fn(k) { Eq(k, length(xs)) }) { pack(length(xs), refl(length(xs))) }

fn slot(xs: ref List, b: buffer(4), p: erased(Lt(length(xs), 4))) -> i64 {
    load(b, length(xs), p, fn(v, b) { v })
}

fn slot_owned(xs: List, b: buffer(4), p: erased(Lt(length(xs), 4))) -> i64 { slot(xs, b, p) }

export fn demo(n: u64, x: i64) -> i64 {
    let xs = repeat(n, x)
    let k = size(xs)                  // k : refine(fn(m) { Eq(m, length(xs)) })
    if_lt(witness(k), 4, fn(q) {
        slot(xs, store(alloc(4, 0), 2, x, decide_lt(2, 4)), transport(fn(m) { Lt(m, 4) }, proof(k), q))
    }, -1)
}
```

`slot_owned` lends `xs` to `slot`, whose precondition is about the
borrow: it holds because it is the owner's. `size(xs)` has a result type
that mentions the owner, and `demo` uses that evidence in a later lend
of the same list.

The rule, for `Lend(x, fn(r) { body }, fn(a, y) { rest })` with x a
variable:

- `body` is checked with r = `Borrow(x)`. So the result type A may
  mention `Borrow(x)` (it still holds no borrow: a scalar, a refinement,
  an array, a buffer or data), and evidence about x is evidence about r.
  While `body` is checked, code there may also borrow x by name, which
  lowering compiles as x's pointer, as it does r.
- `rest` is checked with y = x: the owner given back is x itself, so
  types after the lend can still mention x. x is not counted at the lend;
  `rest` must use x, by either name, exactly once. So x is not used
  before its lend (its one use is after it), not consumed by the reader
  (that would be a second use), and nothing after the lend outside
  `rest` uses it.

Lowering runs `f` and `g` themselves, unchanged: r is x's pointer and y
is x's value, the same pointer, so the substituted terms the kernel
checked compute what lowering runs. A lend of any other term, or with a
reader or continuation that is not a lambda, keeps the earlier rule:
the borrow is a variable, and A cannot depend on it.

The elaborator, untrusted, now continues a `let` that lends an owner
with the same variable, freeing it at the start of the rest if the rest
does not use it, and infers a borrowing `let`'s type as the kernel
checks it, so `let k = size(xs)` needs no annotation.

[`examples/core_lend.jh`](../../examples/core_lend.jh) and its
[core equivalent](../../examples/core_lend.jhc) compile to the same MIR,
whose only checks are the allocations': the load at the list's length
has none. `tests/core_lend.py` runs both against the evaluator with
counted allocations and frees, a fact kept across several lets that lend
the same list, and a reader that borrows its owner by name, and checks 6
source and 10 core rejections: evidence about another list or an older
one, a false size, a use after moving, the owner used in the reader,
unused or used twice after the lend, consumed before it or by a nested
lend, a borrow by name after the lend, of another owner or as the
reader's result, and a continuation that returns a closure.

## Induction over a borrow

`induct` into a proposition on a borrow is a proof by induction over
the list or tree the borrow reads:

```jihoo
fn twice(xs: ref List) -> u64 { induct(fn(t) { u64 }, 0, fn(x, rest, ih) { ih + 2 }, xs) }

fn twice_length(xs: ref List) -> Eq(twice(xs), length(xs) + length(xs)) {
    induct(fn(t) { Eq(twice(t), length(t) + length(t)) }, refl(0), fn(x, rest, ih) {
        transport(fn(k) { Eq(twice(rest) + 2, k + 2) }, ih, refl(twice(rest) + 2))
    }, xs)
}
```

A view's result is runtime data, not a motive, so the proof is not a
view. One kernel term, `Deref(r)` (in `.jhc`, `(deref r)`), is the value
a borrow `r : Ref(T)` reads, of type T, allowed only in types and
evidence. In the pure model a borrow is the value it reads, so
`Deref(Borrow(x))` is x and `Borrow(Deref(r))` is r. The elaborator
makes the proof an ordinary induction over `Deref(xs)`, whose motive
reads each value `t` through `Borrow(t)`: its cases receive the fields,
the recursive ones erased, and the hypotheses. Its result, the motive at
`Deref(xs)`, is the claim about `xs`, since `Borrow(Deref(xs))` is `xs`.
Such a proof is evidence and never runs, so it neither reads nor
consumes the list.

[`examples/core_borrow_induct.jh`](../../examples/core_borrow_induct.jh)
and its [core equivalent](../../examples/core_borrow_induct.jhc)
compile to the same MIR: the induction is erased, and a precondition
about `length(xs) + length(xs)` justifies a load at `twice(xs)` without
a bounds check, the list's length checked once through a
[dependent lend](#dependent-lends). `tests/core_borrow_induct.py` runs
both against the evaluator with counted allocations, proves a tree
lemma by induction over a borrowed tree and uses it at run time, and
checks 6 source and 5 core rejections: false steps and bases, a claim
proved by `refl` that needs induction or by a hypothesis alone, evidence
about another borrow, and a `Deref` in code that runs or of a value that
is not a borrow.

## Views whose result depends on the borrow

A recursion or a `match` over a borrow can return what the program needs
to know about the value it read, and take arguments that change along
the way:

```jihoo
fn size(xs: ref List) -> refine(fn(k) { Eq(k, length(xs)) }) {
    induct(fn(t) { refine(fn(k) { Eq(k, length(t)) }) }, pack(0, refl(0)), fn(x, rest, ih) {
        pack(witness(ih) + 1, transport(fn(k) { Eq(witness(ih) + 1, k + 1) }, proof(ih),
            refl(witness(ih) + 1)))
    }, xs)
}

fn head(xs: ref List, p: erased(Lt(0, length(xs)))) -> i64 {
    match xs {
        Nil => absurd(p)
        Cons(x, rest) => x
    }
}

fn nth(xs: ref List, i: u64, p: erased(Lt(i, length(xs)))) -> i64 {
    induct(fn(t, i: u64, p: erased(Lt(i, length(t)))) { i64 }, fn(i, p) { absurd(p) },
        fn(x, rest, ih, i, p) {
            if_lt(0, i, fn(q) {
                let e = lt_add(0, i, 1, q)
                ih(sub(i, 1, e), lt_cancel(sub(i, 1, e), length(rest), 1, p))
            }, x)
        }, xs)(i, p)
}
```

`View(rec, F, T, cases, r)`'s `T` is either one type of runtime data or a
motive `fn(s: Ref(F)) { T(s) }`. The kernel's rules for a motive are:

- A case for constructor `c` binds the fields, heap ones as borrows `r_j`,
  and in a recursion a result `ih_j : T(r_j)` for each recursive field. It
  gives `T` at `Borrow(c(fields))`, where a heap field is `Deref(r_j)`.
  Since `Borrow(Deref(r))` is `r`, that type computes: `length` of this node
  is `length(rest) + 1`. This is the ordinary dependent eliminator of the
  pure model, where a borrow is the value it reads.
- A later field's type that mentions an earlier heap field reads it through
  its borrow, so a data type can carry a proof about its own heap field, and
  a view gives that proof about the borrow.
- The view's type is `T(r)`.
- A motive's domain is exactly the borrow read, and its body is runtime data,
  of sort `Type 0`: a view computes neither types nor propositions. That
  body's kind is known at a symbolic borrow, so every case's result has one
  representation.

`T` may also be a function type, which is how arguments change along a
recursion. Such a view is runtime code only when applied to all of its
arguments, and these rules keep its linearity:

- A function's body runs any number of times, so a case's lambdas capture no
  owned value: the existing `Lam` rule of `uses`. The rule that a
  continuation's result is not a function does not apply to a view, whose
  cases receive no owned value.
- The exception is a one-level view applied to all its arguments. Exactly one
  case runs, once, so its lambdas for those arguments count as that run, as
  those of a lambda head do. A partial application that captures is rejected.
  `head_into` in `tests/core_nth.py` uses a buffer in such an arm.
- A recursion's cases use no outer owned value, as before; an owned argument
  is passed through the function result instead, as in `fill` there.
- A lend's result is still not a function, so no function holding a borrow
  outlives the lend.

`Absurd(T, p)` (source `absurd(p)`, `.jhc` `(absurd T p)`) has type `T` given
`p : Lt(i, 0)`, for `T` not a function type, and lowers to `unreachable`.
Since exports cannot require evidence, reaching it would need a false proof.
It uses nothing, so an owned value another alternative uses is freed before
it, as in any branch.

At run time a function result is not a closure. Lowering adds its runtime
arguments to the recursion's parameters, after the node and the outer values.
A recursive field's result is then not computed before the case runs: `ih` is
a call the case makes with its own arguments, zero or many times, so `nth`
walks only `i` nodes. A call from inside another recursion's case passes that
call's operands to the inner function as parameters. A hypothesis that is not
called with all its arguments, and a case that does not end in lambdas for
them, are lowering errors. The elaborator eta-expands a case against its type,
so `fn(x, rest, ih) { ih }` and a branch whose alternatives are lambdas lower
normally.

The elaborator, untrusted, adds:

- `induct(fn(t, a: A, ...) { T }, ...)(args)`: a motive with a value and
  arguments. It is written over a value `t`, which the elaborator turns into
  a motive over a borrow by reading `t` as `Deref(s)`. A case may name the
  arguments with its other binders, or return `fn(a, ...) { ... }`.
- `match` on a borrowed variable refines the expected type and the erased
  evidence in scope that mentions the variable. Such evidence becomes
  arguments of the view's result, each arm rebinding it under its own name, as
  `p` in `head`. Evidence about another value is not refined.
- `match` on a borrow into a proposition is a proof by cases about the value
  the borrow reads, through `Deref`, so nothing is read or lent.
- `refine(...)` and `buffer(n)` as a motive's result.

Types and proofs stay out of the run: `examples/core_nth.jh` and its
[core equivalent](../../examples/core_nth.jhc) compile to the same MIR, whose
only checks are the allocations'. `tests/core_nth.py` runs both against the
independent evaluator, which recomputes every piece of erased evidence, on
both targets at `-O0` and `-O2`, for indices in and out of the list, with
counted allocations and frees. It runs programs with an owned argument through
a recursion, a hypothesis returned unapplied, a branch with a function
result, a hypothesis called from another recursion, an owned value used in a
refining arm, a proof by cases and a data type whose proof reads its own heap
field, and asserts the reason for each of 11 source and 15 core rejections.

A program of about 150 lines reached the arena's 200,000 term limit, because
`shift` and `normal` copied terms they did not change. They now return the same
node for an unchanged term, which does not change any result.

A `let` binds a value that reads borrowed data once rather than repeating the
walk at each use (`Core.reads`), and `may_trap` treats a call of a recursion's
result as able to trap, so such a call is kept even when its result is unused.

Owned case analysis may generalize evidence into erased function arguments,
as described in the later inout section. Still unsupported: refining evidence
through a borrow that is not a variable, and `.jh` syntax for a proof field in an
`enum` that mentions an earlier field, which `.jhc` declares with named fields.

## Loops whose invariants are types

A loop may state how its accumulator's type changes with the iteration:

```jihoo
fn matches(n: u64, limit: u64) -> refine(fn(c) { Lt(c, n + 1) }) {
    fold(n, fn(k) { refine(fn(c) { Lt(c, k + 1) }) }, pack(0, decide_lt(0, 1)), fn(i, p, acc) {
        if_lt(i, limit, fn(q) {
            pack(witness(acc) + 1, lt_add(witness(acc), i + 1, 1, proof(acc)))
        }, pack(witness(acc), lt_le(witness(acc), i + 1, i + 2, proof(acc),
            lt_add(0, 2, i + 1, decide_lt(0, 2)))))
    })
}

fn all_even(n: u64) -> Even(n + n) {
    fold(n, fn(k) { Even(k + k) }, zero(), fn(i, p, acc) { twice(i + i, acc) })
}
```

The kernel term is `Loop(n, T, init, body)` (`.jhc`: `(loop n T init body)`),
with `T : U64 -> Type 0` or `U64 -> Prop`, `init : T(0)` and `body : (i : U64)
-> (erased p : Lt(i, n)) -> T(i) -> T(i + 1)`, of type `T(n)`. In the pure model
it is primitive recursion on `n`; the normalizer computes only a count of 0, as
for `fold`, so a loop's result is known through its type rather than by
unrolling it.

- Into `Type 0`, `T`'s body is a scalar, a refinement, a buffer or heap data,
  known at the symbolic index, so that every iteration's accumulator has one
  representation and ownership. An owned accumulator is used exactly once by
  the existing rule for a binder, and the body captures no outer owned value.
- Into `Prop`, it is a proof by induction on the naturals. The accumulator is
  erased, and the proof erases like any other: `doubled` in the example has no
  loop.

Lowering is `fold`'s. In source the form has four arguments; the three-argument
`fold` is unchanged. A dependent view's motive has the same restriction on its
result, for the same reason.

A heap value can hold a proof about its own field, so a loop can build one and
keep the invariant: `tests/core_invariant.py` has `Sized(n)`, a list with
evidence that its length is `n`, built with `T(k) = Sized(k)`. `.jhc` declares
it; `.jh` has no syntax yet for a proof field that names an earlier field.

A `let` now runs a `fold` or `Loop` once rather than at each use of its value.

[`examples/core_invariant.jh`](../../examples/core_invariant.jh) and its
[core equivalent](../../examples/core_invariant.jhc) compile to the same MIR,
with no bounds check. `tests/core_invariant.py` runs both against the evaluator
on both targets, an owned accumulator with counted frees, and asserts the
reason for each of 8 source and 12 core rejections: an invariant false on entry
or not preserved, an off-by-one table, false inductions, a wrong count,
a representation that depends on the index, a function or borrow accumulator,
an evidence accumulator kept at run time, an owned accumulator used twice or
dropped, and a claim that needs a loop to be unrolled.

## Inout parameters

An `inout` parameter changes a buffer or heap data that its caller keeps:

```jihoo
fn bump(n: erased(u64), inout b: buffer(n), i: u64, p: erased(Lt(i, n)), by: i64) -> i64 {
    let before = index(b, i, p)
    store(&b, i, before + by, p)
    before
}

export fn demo(x: i64) -> i64 {
    var b = alloc(4, x)
    let first = bump(4, &b, 2, decide_lt(2, 4), 10)
    first + index(b, 2, decide_lt(2, 4))
}
```

The kernel has no mutable references. A function with an inout parameter takes
the owner and gives it back, so the pure model of `f(inout x: T) -> A` is a
function from T to a new T with an A. Three terms state this:

- `Back(e, T, M)` (`.jhc`: `(Back T M)`, or `(Back0 T M)` when `e`), a type: an
  owner of type T given back, with a result of type `M(x)` that may mention the
  new owner x. T is a buffer or heap data. `M : T -> Type 0` holds no borrow, is
  no function and has one representation for every owner: a scalar, a
  refinement, a buffer, heap data or another `Back`. With `M : T -> Prop`, the
  flag `e` is set and the result is erased evidence.
- `Give(e, M, x, a)` (`(give M x a)`, `(give0 M x a)`) with `a : M(x)`, of type
  `Back(e, T, M)`.
- `Take(v, k)` (`(take v (lam x T (lam a A rest)))`), which gives `k` the owner
  and the result. `rest`'s type depends on neither. `Take(Give(M, x, a), k)`
  computes to `k(x, a)`, keeping an argument that touches memory bound once.

A value of `Back` is used exactly once, by the rule for owned values, and it
cannot be lent, read or freed; a loop accumulator, a data field and a type
argument cannot be one. Since the owner moves in and comes back, the existing
count of uses is the whole safety argument: while a function changes an owner
nothing else can name it. There is no aliasing to rule out, and no new rule
about what an exclusive borrow may do.

Source gives this the syntax of ordinary jihoo, and the elaborator, untrusted,
writes the terms:

- The result type sees each inout parameter as it ends. `old(x)`, in types and
  evidence only, is the value it started with, so a contract can compare them:
  `fn same(inout xs: List) -> Eq(length(xs), length(old(xs)))`. With no result
  type, the function gives back evidence of `Lt(0, 1)`.
- `f(&x)`, with x a `var` or an inout parameter, is a `let`'s value, a statement
  or a block's value. It becomes a `Take`, and the rest sees the new owner under
  the name x. Facts about the old value stay about the old value: a new binder
  is a different variable, so a stale fact does not type-check as a fact about
  the new one.
- `store(&b, i, v, p)` is a statement that rebinds b. `index(b, i, p)` now also
  lends an owned local.
- Every value a function can end with gives its parameters back, through
  branches, `match` arms, `load` and `free`. If the value borrows, it is lent
  around the `Give`, so a function may end with a read of what it changes.

- `x = v` assigns, and the old value is freed if nothing uses it. As an inout
  parameter's last assignment in a block, x is v itself for the block's value,
  so evidence there computes with it: `xs = List.Cons(x, xs)` and then
  `refl(length(old(xs)) + 1)` proves `Eq(length(xs), length(old(xs)) + 1)`. Such
  an x cannot be lent; an earlier assignment rebinds x as a `let` would, with
  only what its type says.
- A `match` on an owned variable of heap data refines the expected type, so an
  arm proves what the function promises about the value it took apart.

A change inside a `let`'s value, a loop body or a recursion's case is an error:
such code would need to return the new owner to what follows. Call a function
with `&x` there, or pass the owner as the accumulator.

At run time `Give` is the owner alone when its result is erased, and otherwise a
tuple of the owner and the result, in registers or on the stack, never on the
heap. Helpers are inlined, so most `Take(Give(...))` pairs meet in the optimizer;
a tuple stays only where it crosses a branch or a recursion's call.

When a case takes a node apart, lowering frees it at the end of the block, and
a node of the same size built before then reuses it. So rebuilding a node
changes it in place, as `set_head` does, and a recursion that rebuilds a list
allocates nothing. This is an optimization of lowering alone: the kernel still
sees a free and an allocation. A recursion on owned data cannot yet have a
function result, so changing the i-th element of a list walks all of it; use a
buffer for that.

[`examples/core_inout.jh`](../../examples/core_inout.jh) and its
[core equivalent](../../examples/core_inout.jhc) compile to the same MIR, whose
only checks are the allocations'. `tests/core_inout.py` runs programs with
branches, two owners, a read of another owner and heap data at `-O0` and `-O2`
with counted allocations, and asserts the reason for each of 29 source and 22
core rejections: passing an owner both ways, a false or stale fact, an owner
consumed, used twice or dropped, a borrow or function as the result, a value of
`Back` lent, freed or used as a loop accumulator, and a wrong erased flag.

An independent review (Codex) of this section, of views whose result depends on
the borrow and of loops whose invariants are types found no unsound case and one
program the kernel accepted and lowering rejected: a dependent view whose arrays
differ in length, now rejected by the kernel. Its negative programs are kept in
`tests/core_rejected`.

## A vector with contracts as types

[`lib/dependent/vec.jh`](../../lib/dependent/vec.jh) is a growable vector of i64
in the core, `import dependent.vec`:

```jihoo
pub struct Vec {
    pub len: u64
    pub cap: u64
    pub data: buffer(cap)
    pub room: erased(Lt(len, cap + 1))
}

pub fn get(v: ref Vec, i: u64, p: erased(Lt(i, len(v)))) -> i64
pub fn set(inout v: Vec, i: u64, x: i64, p: erased(Lt(i, len(v)))) -> Eq(len(v), len(old(v)))
pub fn push(inout v: Vec, x: i64) -> Eq(len(v), len(old(v)) + 1)
pub fn drop_last(inout v: Vec, p: erased(Lt(0, len(v)))) -> Eq(len(v) + 1, len(old(v)))
pub fn clear(inout v: Vec) -> Eq(len(v), 0)
```

A `requires` is a parameter of erased evidence and an `ensures` is the result
type, so a caller's evidence follows the vector through its changes and a read
has no bounds check. `size` gives the length as a refinement, a loop's bound with
evidence that it is the length; `with_capacity`, `new`, `len`, `capacity` and
`last` complete it. A `let` of an owned value keeps only its type, so `var v =
vec.new()` knows nothing about the length until `clear` says it is 0.

This needed four things, each usable on its own:

- A data type may hold a buffer, which makes it heap data, and a field's type may
  name the fields before it. Dropping such a value frees its buffers; a `match`
  on a borrow gives the buffer borrowed. Source writes these as `struct S { a: u64,
  b: buffer(a), p: erased(Lt(0, a)) }`, built with `S { a, b, p }` and taken apart
  with `match s { S { a, b, .. } => ... }`.
- A `match` on an owned variable refines the evidence that mentions it, as one on
  a borrow does. The term is `Case` with a motive whose result is a function of
  erased evidence, applied to that evidence. This is the kernel's one new rule:
  `Case` may have such a result only as the head of an application that supplies
  all of it, so nothing is left that could hold the owned values its cases receive
  and run twice. Lowering calls the case with its evidence erased. A field taken
  from an owned value may be changed with `&` in its arm.
- A marked module may import marked modules. Each is elaborated after those it
  imports, and only the root has an entry point. Declarations retain their module
  identity: `alias.name` reaches only that direct import's public functions,
  types and proposition constructors; `alias.Enum.Variant` selects its variants.
  Modules may reuse names without conflating their types or proofs. Public
  proposition constructors and enum variants follow their family's visibility.
  Struct fields are private unless `pub`; construction and induction require all
  fields to be accessible, while a named match may leave private fields with `..`.
  Qualified patterns check family identity, and discarded binders cannot be read
  through `_`. See [module boundaries](../language/dependent-types.md#module-boundaries)
  for entry points, foreign symbols and the direct-import restriction.
- A node waiting to be freed goes down both branches of an `if_lt`, so a push with
  room allocates nothing.

The elaborator now checks only what each definition adds, and the kernel's step
limit is per definition. The full check before lowering is unchanged.

Elements are i64: the core has no type parameters, and a vector of another type
is written again. A `pop` that returns the element and states the new length
would need a result that is a value with evidence, so `last` and `drop_last` are
separate.

[`examples/core_vec.jh`](../../examples/core_vec.jh) has no check but the
allocations'. `tests/core_vec.py` compares a script with a model on lists and
loops that grow from nothing with counted allocations, a push with room allocating
nothing, and asserts the reason for each of 16 source, 2 module and 10 core
rejections: a read with no evidence, at the length or about another vector, a
fact kept across `clear` or `drop_last`, a false `room`, a buffer of the wrong
length, a field used twice or dropped, a borrowed buffer freed or written, and a
`Case` with a runtime argument or only part of its evidence.

An independent review (Codex) of this section and of the rest of inout found no
unsound case and no wrong result, and one defect, in lowering: a field whose type
was written as an alias or a computation, such as `Buf` for `(Buffer 1)`, was not
freed with its node. Lowering now normalizes the constructors' types first; this
predates buffers in data, since it also applied to a heap field of another type.
The review's programs are in `tests/core_rejected` and `tests/core_accepted`, the
latter linked with a count that fails a program whose allocations are not all
freed.

The next stages of the replacement are:

1. Extend ordinary `.jh` elaboration only as additional program operations
   and their guarantees are supported by this same core.
2. Extend the logical foundations beyond U64 equality, declared
   propositions and flat, indexed data types: recursive data types,
   structural recursion,
   products, equality of other types and
   reusable lemma
   libraries. Specify normalization, universe
   and erasure rules before enabling them.
3. Add runtime operations with explicit ownership/effect rules, including
   borrowed and mutable memory and dynamic allocation. Extend the direct
   lowering of checked programs rather than adding a separate model.
4. Establish the kernel's metatheory and the preservation obligations for
   source elaboration, erasure and lowering. External proof tools may
   validate this small trusted foundation; they are not a required user compilation stage.
5. Retire legacy verification paths as their source programs and enabled
   guarantees move to the core. Reproducing the legacy certificate format
   or preserving its implementation is not a migration requirement.
