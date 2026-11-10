# Core specification

This is the normative description of the native dependent core: what
`compiler/core.jh` accepts, how its terms compute, and what `compiler/core_lower.jh`
makes of them. [The design](dependent-core.md) explains why each part exists and
how source is written; where the two differ about what is accepted, this page is
meant to be right, and a difference is a bug in one of them or in the code. The
elaborator (`core_elab.jh`) and the textual parser (`core_parse.jh`) are not
described: they are untrusted, since the kernel checks their output.

**Status.** The full properties in [What is intended](#what-is-intended) are
not mechanically proved. The [Lean 4 formalization](lean-proofs.md) proves
arithmetic-fragment consistency and semantic conversion soundness, plus
capture-avoiding index/value substitution, conversion-aware finite-scope beta
preservation and logical consistency for a separate index-dependent calculus
with value lets. These are not proofs of this whole calculus
or the implementation. The remaining properties
rest on the independent evaluator, rejection suites and reviews. The
[roadmap](roadmap.md#the-050-release-gate-for-the-native-core) starts the full proof
from this specification. Do not describe the kernel as verified.

`tests/core_spec.py` fails if a term of `Term` has no entry in
[The terms](#the-terms), so the page cannot silently fall behind by a whole term;
it cannot tell whether a rule's text is still accurate.

## Judgments

The kernel's input is a graph of term nodes, in which every child's id is below its
parent's. `check` validates this for every node, reachable or not, before typing.
Terms use de Bruijn indices. A context Γ lists bindings `x : T`, each *erased* or
*runtime*. There are three judgments:

- **Typing**, `Γ ⊢g t : T` (`infer`). The position `g` is either *code*, which may
  run, or *ghost*, which is a type or evidence and never runs. Some rules below say
  they check a part "in ghost position". A ghost position stays ghost in every part
  beneath it.
- **Conversion**, `a ≡ b` (`equal`): the normal forms of a and b are `identical`.
- **Uses**, `use(t, v) = n` (`uses`): how many times running a checked code term t
  uses variable v. Types and evidence are not visited.

`require` is `Γ ⊢g t : T'` with `T' ≡ T`. Checking is by inference over annotated
terms: nothing is solved or searched for.

A program is a sequence of families and definitions, each of which sees only those
before it (`check`). A definition `d : T = v` requires T to be a type or proposition
in ghost position, and `⊢g v : T`, where g is ghost when T is a proposition and code
otherwise. There is no recursion between definitions.

## Quantities

- **Erased** binders hold evidence, or a u64 or data value known only to types and
  evidence (`binder`: an erased binder's type is a proposition, U64 or a data type).
  Reaching one from code is rejected ("erased value used at runtime"). A proposition's
  binder must be erased.
- **Unrestricted** values are `U64`, `I64`, refinements and flat data. They may be used
  any number of times.
- **Owned** (`owned`) values are buffers and boxed data. **Linear** (`linear`) values
  are owned values and values of `Back`. A runtime lambda on a linear binder, in code,
  requires `use(body, 0) = 1`, counting the function's later parameters as part of
  it (`uses_function`). So every linear value is used exactly once at run time.
- **Borrows** (`Ref(T)`) are copied freely. They cannot be freed, consumed, stored in
  data or returned past their lend.

Three rules keep a linear value from being hidden in something that could run twice
or not at all:

- `use` rejects a lambda that captures a linear value, unless it is the head of a
  redex, or a case or continuation given all its arguments, each of which runs once.
- A partial application cannot take a non-erased linear argument (`unsaturated`), nor
  capture one.
- A continuation that receives owned values has no function as its result
  (`not_function`): `Load`, `Lend`, `Take`, and `Elim` and `Case` into `Type 0`, with the
  one exception under [`Case`](#elim-case). An elimination into `Prop` may give a function
  proposition: evidence does not run.

A type argument at run time must satisfy both **first-order kind**
(`first_order_kind`) and **first-order value** (`first_order`) checks. Its expected
kind normalizes to a universe, optionally preceded by a telescope whose domains
all normalize to U64. Runtime and erased U64 index binders are both allowed.
This expected-kind check also applies when the argument is a variable rather
than a lambda. The value's normal form must mention no buffer, boxed data,
borrow, `Pi` or `Back`, since a type variable is used without linearity and could
stand for one. Its lambda annotations are omitted by the value scan only after
the expected kind has restricted family inputs to U64 indices.

Checking the value alone is insufficient: `fn(A: Type) { A }` has a plain body,
but substituting it for `F` can expose Buffer(n) behind a formerly neutral
`F(Buffer(n))` domain. The conservative runtime rule therefore rejects families
over types, type families, signed indices and other non-U64 domains, even if a
particular family's result would be harmless. Ordinary monomorphic type arguments
and U64-indexed families remain supported. Ghost computations in types/evidence
are unaffected; for example an identity type function can still appear directly
in a binder annotation that normalizes to Buffer(n). This restriction closes the
higher-kinded ownership-instantiation counterexample; it is not a new theorem
of whole-Core typing or mode preservation.

## Families

A family (`signature`, `declare`) is a name, a kind (proposition or data), an arity of
at most 16 U64 indices, of which a data type's first `params` are parameters (a
proposition has none), and constructors, each a closed telescope ending in the family
applied to indices. A family is visible
only after its own declaration, so it can occur only as a whole field `F(indices)` or
as the result: this is strict positivity.

- A field of a proposition is erased, or a U64. A recursive field is erased.
- A field of a data type is erased, or a `U64`, an `I64`, a refinement, a buffer or an
  earlier data type. A recursive field of a data type is a runtime value, never erased,
  with the type's parameters. A field's type may mention the fields before it.
- A data type's constructor binds the parameters first, erased, and returns them
  unchanged.
- The telescope, a recursive field's family and the parameters are matched as written,
  before normalization: an alias for the telescope's tail is not unfolded, and `n + 0` does
  not count as the parameter n. Other field types are normalized after they are checked.
- A data type is **boxed** when a runtime field is recursive, a buffer or boxed. A boxed
  type cannot hold a flat data value, which has no representation.

Case types (`case_type`, `data_case_type`, `recursion_case_type`, `view_case_type`) are
computed from the telescope and appear under [`Elim` and `Case`](#elim-case) and
[`View`](#view).

## The terms

Each entry gives the term's **Type** rule, **Uses**, what it **Reduces** to in `normal`,
and how it **Runs** after erasure (`Lower.expr`). "Congruence" means normal forms of the
parts; "the parts" under Uses means the sum of the uses of the listed parts; "no uses"
means it is not visited. In a rule, `T(x)` is application.

### `Var`, `Global`

- **Type.** The context's or the definition's type, weakened. An erased `Var` is
  rejected in code. A `Global` must be defined earlier.
- **Uses.** `Var(k)` is 1 if k is v. `Global` has no uses: definitions are closed.
- **Reduces.** `Var` is normal. `Global` unfolds to the normal form of its value.
- **Runs.** `Var` is its environment entry. `Global` does not remain after normalization.

### `Universe`, `Prop`, `U64`, `I64`, `Array`, `Lt`, `Eq`, `Pi`, `Refine`, `Buffer`, `Ref`, `Ind`

- **Type.** `Universe(n) : Universe(n + 1)`, n below 32. `Prop`, `U64` and `I64` are in
  `Universe(0)`. `Array(n)`, `Refine(p)` with `p : U64 -> Prop`, and `Buffer(n)` are in
  `Universe(0)`, with n : U64 in ghost position. `Lt(a, b)` and `Eq(a, b)` are in `Prop`, on
  U64 in ghost position. `Ref(T)` is in `Universe(0)`, T in `Universe(0)` and owned.
  `Ind(F, xs)` needs F's arity of U64 indices and is in `Universe(0)` for data and `Prop`
  otherwise. `Pi(e, A, B)` checks the binder, then is `Prop` if B is a proposition, which is
  impredicative, and otherwise `Universe(max(level of A, level of B))`.
- **Uses.** None.
- **Reduces.** Congruence.
- **Runs.** Types have no runtime form. `runtime` maps `U64` and `Refine` to u64, `I64` to
  i64, `Buffer`, `Ref` and boxed `Ind` to a pointer.

### `Lam`, `App`

- **Type.** `Lam(e, A, b)` checks the binder, then b under it at the same position, with
  the use count in code when A is linear; its type is `Pi(e, A, B)`. `App(f, a)` needs f's
  type to normalize to `Pi(e, A, B)`, requires `a : A`, in ghost position if e, and has type
  `B[a]`. In code a type argument is first order. At the top of a spine in code, a result that
  is still a function is a partial application: its head must not be a `Case`, and its
  arguments must not be linear.
- **Uses.** A `Lam` alone counts as 0 but rejects a capture. An `App` spine with a lambda
  head counts the runtime arguments and the body. A `View` or `Case` head counts its
  cases with the arguments as binders. Otherwise the head's uses. In each case every
  remaining runtime argument is added. A partial application with any use is rejected.
- **Reduces.** `App(Lam(e, A, b), a)` is `b[a]`. In runtime mode, for a non-erased a, if a is
  effectful or reads, the redex is kept, binding a once, and if a may trap, the result is
  `Strict(a, b[a])`. An erased argument has no evaluation to keep. Applying `IfLt` or `IfEq` applies both alternatives; applying
  `Strict(t, g)` is `Strict(t, g(a))`; applying a kept redex moves the argument inside it.
- **Runs.** A kept redex evaluates a, then the body. A head that is a `View`, a `Case` with
  erased arguments, or a recursion's result is called with its arguments. Any other
  application has no runtime form.

### `Natural`, `Integer`, `Elements`, `Index`

- **Type.** `Natural : U64`, `Integer : I64`. `Elements(xs) : Array(|xs|)` with each x : I64.
  `Index(a, i, p) : I64` where a's type is `Array(n)` or `Ref(Buffer(n))`, i : U64 and
  `p : Lt(i, n)` in ghost position.
- **Uses.** The elements; `Index` a and i.
- **Reduces.** Congruence. An array read does not compute.
- **Runs.** Constants; a local array; a load at the index, with no bounds check.

### `Refl`, `Transport`, `Decide`, `ZeroLe`, `LtAdd`, `LtCancel`, `LtLe`

These are evidence, and every part is in ghost position.

- **Type.**
  - `Refl(a) : Eq(a, a)`.
  - `Transport(P, e, p) : P(b)` for `P : U64 -> Prop`, `e : Eq(a, b)`, `p : P(a)`. So equality
    eliminates only into propositions.
  - `Decide(a, b) : Lt(a, b)` when a and b normalize to numerals with a below b.
  - `ZeroLe(a) : Lt(0, a + 1)`.
  - `LtAdd(a, b, c, p) : Lt(a + c, b + c)` from `p : Lt(a, b)`, and `LtCancel` the converse.
  - `LtLe(x, y, z, p, q) : Lt(x, z)` from `p : Lt(x, y)` and `q : Lt(y, z + 1)`: the naturals are
    discrete.
- **Uses.** None.
- **Reduces.** `Transport(P, Refl(_), p)` is p. The others are congruence.
- **Runs.** Erased.

### `Arith`, `UAdd`, `USub`, `Strict`

- **Type.** `Arith(op, a, b) : I64` on I64. `UAdd(a, b) : U64` on U64. `USub(a, b, p) : U64`
  with `p : Lt(b, a + 1)` in ghost position. `Strict(a, b)` has b's type, a being checked.
  Source and textual core cannot write `Strict`: normalization makes it.
- **Uses.** The operands; `Strict` a and b.
- **Reduces.**
  - `Arith` on two integers folds unless it overflows, which stays a runtime trap.
  - `UAdd` becomes the canonical sum (`sum`): variables in index order, then other terms, in
    structural order in the pure model and in their evaluation order in runtime mode, then
    the constant. In ghost mode a constant beyond 2^64 - 1 is a deterministic balanced
    `UAdd` tree of U64 literals; runtime mode leaves such a sum as written. Collection charges
    every visited occurrence, including repeated graph references, to the checker step budget.
    `(x - y) + y` cancels to
    x when the sum has y's parts, unless a part is effectful or y holds a `Strict`, keeping y's
    traps. At most 64 cancellations are tried, after which the sum simply stays as it is.
  - `USub` cancels `(r + b) - b` to r under the same conditions.
  - `Strict(a, b)` is b if a cannot trap. Conversion ignores `Strict`.
- **Runs.** Checked: `Arith` and `UAdd` trap on overflow. `USub` cannot underflow: it has
  evidence. `Strict` evaluates a for its effects, then b. U64 terms therefore denote natural
  numbers.

### `Pack`, `Witness`, `Proof`

- **Type.** `Pack(P, a, q) : Refine(P)` with `P : U64 -> Prop` and `q : P(a)` in ghost position
  and a : U64 at the current position. `Witness(s) : U64` and
  `Proof(s) : P(Witness(s))` for `s : Refine(P)`, the latter in ghost position.
- **Uses.** `Pack` and `Witness` their value. `Proof` none.
- **Reduces.** `Witness(Pack(_, a, _))` is a, and a witness of a branch is the branch of
  witnesses, keeping `Strict`. `Proof(Pack(_, _, q))` is q, through `Strict`. Conversion ignores
  `Pack`'s evidence.
- **Runs.** A refinement is its u64.

### `IfLt`, `IfEq`

- **Type.** `IfLt(a, b, yes, no)` needs a and b : U64. `yes` is checked under an erased binder
  of `Lt(a, b)`, or `Eq(a, b)` for `IfEq`, and its type must not depend on it; `no` has the same
  type.
- **Uses.** a and b, plus the alternatives, which must use v equally.
- **Reduces.** On two numerals, the chosen alternative, `yes` given `Decide` or `Refl`.
  Otherwise congruence.
- **Runs.** A comparison and a branch, with no evidence. Both alternatives have one layout.

### `Con`, `Elim`, `Case`

<a id="elim-case"></a>

- **Type.**
  - `Con(F, k, xs)` needs a constructor k of F and all and only its fields, and instantiates its
    telescope field by field. Runtime fields of data are at the current position, and erased
    fields and all fields of a proposition are in ghost position. Its type is the telescope's
    result.
  - `Elim`, `Case` and `View` need exactly one case per constructor.
  - `Elim(F, P, cases, x)` on a proposition: `P : U64... -> Prop`, each case of `case_type`:
    `(fields...) -> (erased ih : P(indices of r))... -> P(result)`, x evidence of F, all in ghost
    position. Only propositions eliminate this way.
  - `Elim` on data, and `Case` (`eliminate`): `P : (indices...) -> F(...) -> Prop` or `Type 0`, x of
    that type. Each case gives P at the node built from its fields, from those fields: for
    `Case`, `data_case_type`, with recursive fields owned; for `Elim` on boxed data,
    `recursion_case_type`, with recursive fields erased and a hypothesis `ih : P(r)` per recursive
    field, erased when P is a proposition. Into `Prop` it is evidence, in ghost position. The
    result is `P(indices..., x)`, which, into `Type 0`, is no function.
  - `Case` is for boxed data. As the head of an application it may have a result that is a
    function of erased arguments only (`erased_function`), evidence, indices or data, and the
    application's top must supply all of them, so nothing is left that could hold the owned values its cases receive and run
    twice.
- **Uses.** `Con` its runtime fields. `Elim` and `Case`: x, plus one case's uses, which must be
  equal across cases. A recursion's cases run once per node, so they may not use an outer
  linear value. `Elim` on a proposition has none.
- **Reduces.** `Elim` on a known constructor is its case applied to the fields, then to the
  `Elim` of each recursive field. `Case` on a known constructor is its case applied to the
  fields, so the node is never built. Only runtime normalization distributes `Case`, and `Elim`
  on data, over `IfLt` and `IfEq` in the scrutinee. Pure conversion keeps an elimination on a
  symbolic branch, including its dependent motive. Both modes distribute over `Strict`.
  A data type's parameters are not given to a case.
- **Runs.** A boxed `Con` allocates a node of a tag and one slot per runtime field. `Case` switches
  on the tag, loads the fields and frees the node at the end of the block, and a node of the same
  size built before then reuses it. `Elim` on boxed data is a recursive function that calls itself
  on each recursive field first, then frees the node. Flat data has no representation: its case
  analysis must reduce away, and lowering rejects what does not. Runtime
  normalization sequences a flat constructor's effectful or borrowed-reading
  runtime fields through its checked telescope before substituting the constructor.
  Fields are evaluated once in declaration order; erased fields stay erased.
  This sequencing does not run during pure conversion and does not introduce a
  general flat-data runtime layout. A flat result crossing a lend continuation or
  an effectful branch may still fail to lower; bind scalar results before building
  the record in those cases.

### `Fold`, `Loop`

- **Type.**
  - `Fold(n, init, body)`: n : U64, init an I64 or an owned value of type A, `body : (i : U64) ->
    (erased p : Lt(i, n)) -> A -> A`. Its type is A.
  - `Loop(n, T, init, body)`: `T : U64 -> Type 0` or `Prop`, `init : T(0)`, `body : (i : U64) -> (erased
    p : Lt(i, n)) -> T(i) -> T(i + 1)`, of type `T(n)`. Into `Type 0`, T's body must be `U64`, `I64`, a
    refinement, a buffer or boxed data. Into `Prop`, everything is in ghost position and the
    accumulator is erased.
  - For both, a body that touches memory must be written with its three binders.
- **Uses.** n and init. The body runs many times, so any use in it is rejected.
- **Reduces.** A count of 0 is init. Otherwise congruence: a loop is never unrolled, and its result
  is known through its type. In runtime mode a body without three leading binders is eta-expanded,
  so that lowering finds them; lowering does not read their annotations.
- **Runs.** A counted loop whose accumulator is a local. `Loop` into `Prop` is erased.

### `Alloc`, `Load`, `Store`, `Free`, `Drop`

- **Type.**
  - `Alloc(n, x) : Buffer(n)` with n : U64 and x : I64.
  - `Store(b, i, v, p) : Buffer(n)` for `b : Buffer(n)`, i : U64, v : I64, `p : Lt(i, n)` in ghost
    position.
  - `Load(b, i, p, k)`: b, i and p as for `Store`, and `k : I64 -> Buffer(n) -> T`, of type T, which
    depends on neither and is no function.
  - `Free(b, rest)` and `Drop(F, x, rest)` have rest's type, b a buffer, x of boxed F.
- **Uses.** The parts; `Load`'s k with its two arguments as binders.
- **Reduces.** Memory operations do not compute. In the pure model `Free` and `Drop` are rest, and
  `Alloc`, `Load` and `Store` are neutral. In runtime mode all are congruence.
- **Runs.** `Alloc` calls `malloc` for `8 * n + 8` bytes, checked, and traps on null. `Load` and
  `Store` are offsets with no bounds check. `Free` calls `free`. `Drop` calls one function per family
  that frees the node, its buffers and the owned fields within.

### `Lend`, `Borrow`, `Deref`

- **Type.**
  - `Lend(x, f, g)`: x owned of type T, `f : Ref(T) -> A`, `g : A -> T -> R`. A is `U64`, `I64`, a refinement,
    an array, a buffer, data or a `Back` (`outlived`), so it holds no borrow; R depends on neither
    and is no function.
  - When x is a variable and f and g are lambdas, the lend is *dependent* (`dependent_lend`): f's body
    is checked with r = `Borrow(x)`, where code may also borrow x by name, and A may mention it; g's body
    is checked with the owner given back equal to x, and uses x exactly once by either name.
  - `Borrow(x) : Ref(T)` for x of owned T, in ghost position, or in code only for a variable x
    inside the reader of a lend of it (`lending`). `Deref(r) : T` for `r : Ref(T)`, in ghost position
    only.
- **Uses.** A dependent lend: the reader with r = `Borrow(x)`, plus the continuation with y = x. Any
  other lend: x, f with one binder and g with two. `Borrow` and `Deref` have none.
- **Reduces.** In the pure model a lend is `g(f(Borrow(x)), x)`. `Deref(Borrow(x))` is x and
  `Borrow(Deref(r))` is r. In runtime mode a lend is congruence.
- **Runs.** A borrow is the owner's pointer: x, then f, then g. `Borrow` is its variable's pointer.
  `Deref` is erased.

### `View`

- **Type.** `View(rec, F, T, cases, x)`: x : `Ref(F(ps))`, F boxed with no true indices. T is any type
  in `Universe(0)`, or a motive `Ref(F(ps)) -> Universe(0)`, whose body, past any `Pi`, must be `U64`,
  `I64`, a refinement, a buffer, data or an array of a length mentioning none of those binders. Each case is
  `view_case_type`: the fields, those on the heap as `Ref`, then, if `rec`, a result per recursive
  field, then T at a borrow of the node it reads, whose heap fields are `Deref` of their borrows. Its type
  is T, or T(x) with a motive.
- **Uses.** x, plus one case's uses, equal across cases, with a function result's arguments as binders.
  A recursion's cases may not use an outer linear value. Nothing is consumed by reading.
- **Reduces.** In the pure model a view of `Borrow(v)` with v a known node is its case applied to the
  fields, heap ones as `Borrow`, then, if `rec`, the view of each recursive field. It distributes
  over `Strict` in v, but stays neutral on symbolic `IfLt` and `IfEq` so its dependent motive is
  retained. In runtime mode, congruence.
- **Runs.** The same switch and recursion as for owned data, freeing nothing. A function result's
  arguments are parameters of the recursion, and a hypothesis is a call.

### `Back`, `Give`, `Take`

- **Type.**
  - `Back(e, T, M) : Universe(0)`: T in `Universe(0)` and owned, `M : T -> Universe(0)` or `Prop`, with e
    set exactly when M gives a proposition (`back_motive`). Into `Universe(0)`, M's body is `U64`, `I64`, a
    refinement, a buffer, boxed data or a `Back`, which holds no borrow and is no function.
  - `Give(e, M, x, a) : Back(e, T, M)` for x of owned T and `a : M(x)`, in ghost position if e.
  - `Take(v, k)`: `v : Back(e, T, M)` and k literally two lambdas, `fn(x : T) { fn(a : M(x)) { rest } }`, the
    second erased exactly if e, whose annotations are compared by conversion. rest's type depends on
    neither binder and is no function.
- **Uses.** `Give` x, and a unless e. `Take` v, plus k with two binders. `Back` none.
- **Reduces.** `Take(Give(_, _, x, a), k)` is `k(x, a)`, through the rules for `App`. `Back`, `Give` and any
  other `Take` are congruence, and conversion ignores `Give`'s erased evidence.
- **Runs.** `Give` is x alone if e, and otherwise an unboxed pair of x and a. `Take` binds its parts.

### `Absurd`

- **Type.** `Absurd(T, p) : T` for T a type or proposition that is no function, and p evidence of `Lt(i, n)`
  with n normalizing to 0.
- **Uses.** None: it cannot run.
- **Reduces.** Congruence.
- **Runs.** An unreachable terminator, if T has a layout: lowering rejects one that has none, such as
  an array or flat data.

## Modes of normalization

`normal` computes in one of two modes. The **pure model** is used by the kernel for
conversion: any argument may be substituted, memory operations are neutral, and lends and views of
known values compute. **Runtime mode** (`runtime`) is used by lowering on code to run: an
argument that is effectful or reads stays bound once, traps are kept by `Strict`, and lends and views
stay. Runtime normalization also distributes data eliminations over symbolic branches to remove
flat data before MIR lowering. Pure conversion does not: a dependent motive may give the alternatives
different types, while `IfLt` and `IfEq` require one common type. Consequently a symbolic elimination
and its manually distributed form need not be definitionally equal. Concrete scrutinees still compute.

At an application, an argument normalized to `Lam` is already a function value:
its body is not evaluated when passed. It can be substituted even when the body
contains arithmetic, reads or memory effects. Likewise `Strict(Lam(...), b)`
normalizes to `b`. For a runtime lambda application, a `Strict(prefix, value)`
argument becomes `Strict(prefix, App(lambda, value))` before substitution, so its
prefix is evaluated once before the body. Discarding a nested strict result
reassociates `Strict(Strict(prefix, value), b)` to
`Strict(prefix, Strict(value, b))`. This allows arithmetic captured by a partial
application without a runtime closure, while retaining capture-time overflow
traps even when the function is unused. Applying the function still normalizes
its body under the ordinary runtime rules. A retained redex representing an
effectful capture is floated out of a runtime lambda's argument position, with
the consumer shifted under its binder. Discarding such a redex similarly moves
the discard under that binder. The effectful argument is never substituted or
duplicated; only its bound value is reused. This handles called and unused partial
applications such as `f(free(alloc(n, 7), 5))` without runtime closure allocation. This exception is local to application and
`Strict`: the predicates below still inspect lambda bodies when analyzing invoked
loop and induction cases. Runtime normalization is not covered by a general
formal preservation or compiler refinement theorem.

Three syntactic predicates decide this, each conservative at the depth limit, and otherwise the
disjunction over a term's children:

- `effectful`: `Alloc`, `Load`, `Store`, `Free`, `Drop`, `Case`, and boxed `Con` and `Elim`.
- `may_trap`: those, and `Arith`, `Strict`, `UAdd`, and in runtime mode a call of a variable.
- `reads`: `View` with a result that is not a function, `Fold`, `Loop`, and a call of a view or variable.

`Absurd` and `Back` are neither effectful nor trapping; a `Give` is as its owner, and its result unless
erased; `Refine` and `Proof` do not trap, and `Pack` is as its witness. `Index` has no special case: a
read of an array or a borrowed buffer may be substituted and so repeated, which is safe since the
buffer cannot change while it is lent.

Conversion (`identical`) is syntactic equality of normal forms, up to:

- `Strict(_, y)` being y;
- evidence being irrelevant in `USub` and `Pack`, and in an erased `Give`.

Other evidence is compared as written. The structural order used to canonicalize
sums (`compare`, `conversion_children`) ignores exactly the same evidence, including
inside otherwise different atoms. Replacing an irrelevant proof must not change
where an atom sorts relative to another one. All children still participate in
graph validation, typing and substitution; irrelevance never excuses invalid evidence.

## Lowering

`compile` checks the whole program again, independently of what elaboration checked, and normalizes
constructor types. There must be at least one export. An export's parameters are all non-erased `U64`
or `I64`, since a foreign caller has no evidence to give, and its result is `U64`, `I64` or a refinement.
Its normal form has a lambda for each parameter. Its body is normalized in runtime mode, and
`Lower.expr` emits MIR by the **Runs** entries above: evidence and erased binders have no locals, and
reaching one is an internal error.

Lowering may **reject** a checked program with a diagnostic. It does not emit code for one that
it cannot represent, so a program accepted by `core check` need not compile.
The marked `.jh` frontend's `check` also checks executable lowering. Known core cases are:

- a term with no runtime form, such as flat data computed at run time by a view;
- a recursion whose result is an array, since `runtime` has no layout for one;
- a `Load`, `Lend`, `Take`, case or hypothesis whose continuation is not literally lambdas after
  normalization, such as a function chosen by a branch;
- a case or branch whose alternatives have different layouts;
- a function result not called with all its arguments;
- an `Absurd` at a type with no layout.

## Limits

Checking stops with an error, never acceptance, at any of these. Failing to compute is not evidence.

- 200,000 terms (`LIMIT`), counting those the kernel makes as well as its input.
- 1,000,000 steps (`STEPS`) of the kernel's recursive operations, reset for each definition with the
  families before it. Lowering's normalization continues the last count. Structural equality and
  sum ordering charge each visited pair, including repeated DAG references; sorting variables,
  cancellation candidate comparisons, pool copying and removal shifts also consume this budget.
  Exhaustion propagates as a diagnostic rather than equality, inequality or an unsuccessful
  cancellation. Depth exhaustion in comparison is likewise an error, including identical IDs.
  These are operation charges, not a wall-clock or allocation-complexity theorem: other recursive
  predicates and vector/node cloning are not individually metered by these comparison checks.
- Recursion depth 128 (`DEPTH`), a budget for each operation rather than a bound on source nesting: for
  example, each field of a telescope starts anew.

## What is intended

These are the properties the rules are meant to have. They are stated for a closed, checked program, and
are tested but not proved:

1. **Consistency.** There is no closed evidence of `Lt(0, 0)`.
2. **Preservation.** The pure model's reductions are intended to preserve types. Symbolic data
   elimination and views retain their motives instead of distributing into differently typed branches.
   This repairs the rechecking failures in `examples/core_data.jhc` and `core_indexed.jhc`, as well as
   dependent heap cases and views. `jihoo core preserves FILE` rechecks each definition's pure normal
   form at its declared type in ghost position. The `core` suite requires it to pass on every core
   example, accepted fixture and preservation regression, without expected failures. This finite check
   is not a proof of preservation or of runtime quantity soundness. Runtime normalization is a separate
   lowering transformation whose correctness remains to be established.
3. **Quantities.** In the erased program every linear value is used exactly once, and no borrow outlives
   its lend. Allocations are freed exactly once on every path that does not trap.
4. **Safety.** Accesses with evidence are in bounds, and `Absurd` is not reached.
5. **Adequacy.** The erased program computes the pure model's value, or traps on an overflow or a failed
   allocation.

What stays trusted is the kernel's implementation of these rules, `core_lower.jh`, MIR to LLVM, LLVM and
the runtime.


## Formalization boundary

The specification above, rather than historical feature snapshots in the design
notes, is the intended starting point for a Lean formalization. There is not yet
a machine-checked soundness proof for the whole specified calculus. A useful order is typing and capture-avoiding
substitution, conversion and pure preservation, quantities and borrow lifetimes,
then runtime normalization and erasure adequacy. Each theorem must state which
term forms and reduction rules it covers.

Pure ghost normalization is not runtime evaluation: it can erase evidence and
ignore resource use. Rechecking pure normal forms is regression evidence only;
it does not establish linearity, trap preservation, allocation behavior or the
correctness of lowering. The executable semantics must account for those
separately. A proof of the core calculus alone does not verify the source
elaborator, the implementation of its checker, MIR to LLVM, LLVM or the runtime.
Partial lowering and documented source inference restrictions are not additional
core typing rules and should not silently narrow a theorem advertised for the
whole core.


The [Lean proof boundary](lean-proofs.md#closed-local-array-and-subtraction-safety)
now includes closed local-array selection and unsigned subtraction safety in the
higher-order `Raw.Beta` fragment, including `ZeroLe`. Bounds follow from typing
and closed literal consistency, without assuming evidence normalization. Literal
operands are required, or explicit finite beta/add evaluations to those operands.
This does not discharge the whole-calculus, quantity/borrow or lowering obligations
above; actual kernel and native behavior are checked by finite regression tests.


A [quantity control foundation](lean-proofs.md#quantity-control-and-partial-executions)
proves exact resource counts for successful abstract control executions and upper
bounds for finite prefixes, including traps. Local binders, branches, repetition,
known once-called continuations and erased code have separate rules. The missing
whole-core projection, operational simulation and heap/borrow lifetime obligations
are explicit; these results do not yet establish item 3 above.


[Mixed binder and owner-alias accounting](lean-proofs.md#mixed-binders-and-owner-aliases)
extends that foundation with mode-aware scopes and capture-avoiding identification
of variable slots. Returned-owner aliases are counted together before branch
agreement. Authenticating the modes and aliases from whole-core typing, and
proving heap/borrow and runtime correspondence, remain separate obligations.


[Binder-capability projection](lean-proofs.md#binder-capabilities-from-checked-domain-observations)
now derives modes and lend permissions from normalized-domain summaries and
checks them against actual checked Core telescopes. Its formal result is
conditional on authentic summaries: formation/normalization provenance,
first-order type instantiation, source-owner identity and borrow lifetimes are
not established by this classification theorem.


[Rooted context provenance](lean-proofs.md#rooted-context-and-lend-owner-provenance)
now derives descriptors along original lambda edges and resolves a Lend's
variable owner with Core's reverse context indexing. Its structural theorem is
relative to a faithful syntax view and contextual domain observer; the actual
kernel interfaces are regression-tested, not proved. Whole-Lend continuation
projection and heap/borrow soundness remain outstanding.


[Scoped Lend projection](lean-proofs.md#scoped-lend-reader-and-continuation-projection)
derives reader/continuation controls in a bounded structural fragment and keeps
the fresh result distinct from the returned owner. Its use-accounting theorems
are relative to faithful typed observations and abstract control execution;
whole-kernel substitution, runtime and heap/borrow correspondence remain open.


[Lend substitution correspondence](lean-proofs.md#lend-substitution-and-ownership-projection)
proves that variable/borrow substitution commutes with quantity-annotated source
projection, including nested scopes/Lends, and compares it with actual kernel
substitution. Native transformation refinement and typed mode stability, as well
as runtime and heap/borrow soundness, remain separate obligations.

The [heap/lease primitive semantics](lean-proofs.md#allocation-identities-and-scoped-read-leases)
now proves allocation/lease invariant preservation, permanent expiry, no double
free, and a nested-reader payload frame property. Coupling exact free-event
identities to checked quantity traces yields actual deallocation, conditional
on that trace projection. This is not a proof that whole-Core typing establishes
the primitive preconditions or prevents escaping borrows; recursive heap fields,
allocator address reuse and native execution correspondence remain open.

The [structured scalar Lend fragment](lean-proofs.md#structured-scalar-lend-execution)
now derives reader authority, scalar-only results, heap-transition preconditions,
lease-map restoration and exact free-event projection from its own scoped
syntax. It instantiates the existing original/returned-owner quantity rule.
A live target with no preexisting lease is an entry premise, not a proof of
unique ownership aliases. Full graph/context correspondence and the broader
owned-result, nested-Lend and recursive-heap cases remain open.

The [bounded original-constructor Lend bridge](lean-proofs.md#original-constructor-graphs-for-scalar-lend)
now checks the exact root/type/lambda spine, tracks scalar/ghost binder shifts
and original/returned-owner aliases, and translates supported read bodies to
the scoped model. Forward and reverse correspondence cover the new restricted
constructor semantics; every admitted execution satisfies the primitive heap
endpoint. This does not yet formalize the whole Core operational semantics or
prove the native exporter faithfully supplies the view; opaque constructors,
general ownership contexts and broader heap features remain outside its scope.

[Linear allocation/admitted-call programs](lean-proofs.md#linear-allocation-and-admitted-call-programs)
now thread distinct live, lease-free allocation capabilities through finite
calls to the admitted Lend graph fragment. They derive call-entry guards and
prove concrete allocation/release conservation, exactly-once freeing of tracked
resources and an empty final heap for closed complete executions. These are
formal caller-program rules, not yet a translation of general native caller
graphs. Successful-allocation, finite-control and scalar-fragment restrictions
remain explicit; full capabilities, failures, recursion and MIR correspondence
remain open.

[Original finite caller graphs](lean-proofs.md#original-core-allocationcaller-graph-recognition)
now recognize literal allocation and App/Lam call-binding spines directly from
constructor IDs. A lexical-binding interpretation proves consumed names remain
tombstones while live capability slots compact, and admitted closed caller
executions inherit heap safety and a completely empty final live heap. This is
a restricted heap-effect semantics, not scalar-result preservation or general
native caller/lowering adequacy; the trusted exporter and finite successful-
allocation restrictions remain explicit.

[Lease-free heap erasure](lean-proofs.md#lease-free-heap-erasure-of-admitted-callers)
now translates this admitted caller subset into an independent pointer-identity
heap with no lease state. Callee scalar results, observable effect order and
erased final heaps correspond; target determinism plus source totality covers
all complete target runs, including exact release/no-leak guarantees. This is an
abstract erasure stage, not native MIR CFG or final caller-result adequacy.

The [result-bearing caller extension](lean-proofs.md#scalar-results-through-owned-caller-bindings)
distinguishes scalar bindings from live owner slots and consumed-owner tombstones.
Its finite return fragment can select a literal or an earlier/later callee result;
owner insertion and consumption preserve the meaning of existing scalar names.
This addresses caller results for that restricted constructor subset, not general
Core arithmetic/control flow or native MIR/machine result adequacy.

[Bounded emitted-MIR execution](lean-proofs.md#bounded-execution-of-emitted-mir-caller-graphs)
retains actual local/block/instruction identities for closed one-cell caller
examples, including malloc/assert and the initialization-loop backedge. A checked
source/MIR pair compares its scalar result and allocation/free lifecycle under
an independent bounded MIR semantics. This is conditional translation validation,
not a general `core_lower.compile` theorem or concrete-address machine refinement;
unsupported shapes and exhausted fuel reject rather than certify a partial run.

The pure model now also has [bidirectional payload-erasure adequacy](lean-proofs.md#bidirectional-pure-payload-erasure-adequacy):
every finite execution of an annotation/proof-payload-erased term lifts back to
the source, with scalar and trap observations preserved. This is generic over
the existing pure grammar and retains ghost binder slots. It is not a theorem
about the full Core grammar or native ghost-slot deletion/lowering.

The [typed owned-result Lend slice](lean-proofs.md#typed-owned-result-lend-transfer)
now accounts separately for a newly allocated Buffer result and the original
owner. Direct continuation typing derives alias-safe consumption and primitive
heap guards. This covers a previously omitted `outlived` result class only for
the stated one-cell subset, not all specified ownership rules; see the
[release-gap assessment](0.6-proof-status.md).

The common constructor judgment also distinguishes [scalar and owned returns](lean-proofs.md#returning-owned-results). An owned result retains exactly one live, unborrowed
capability instead of falsely treating that result as a leak. Fresh-context
consumption composes with the existing scalar continuation guarantees; arbitrary
dependent result substitution and general lowering remain outside this slice.

A [owned-producing application extension](lean-proofs.md#syntactic-owned-producing-application-composition)
connects recursive direct App/Lam graph nodes to producer evaluation and binding
of the exact returned capability. The producer accounts for every current
resource and the body receives only the result. The singleton body restriction
is not a proof that arbitrary captures can be discarded.

[Framed application](lean-proofs.md#framed-owned-application-with-captured-bindings)
retains captured owner/scalar bindings across an explicit static resource split.
Its frame safety is derived from typing and execution; deterministic evaluation
is stated for a fixed partition plan, not arbitrary erased or inferred plans.

The [constructor-closure integration](lean-proofs.md#composing-calls-under-existing-core-constructors)
uses that same framed judgment for calls inside allocation, Free, mixed Lend
and let continuations. Lend readers retain their existing restrictions: the
new continuation runs after the lease closes, not inside an active reader.
