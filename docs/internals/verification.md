# Design: verification (0.5) and mathematics (0.6)

The replacement direction is a [native dependent core](dependent-core.md):
check the program and its proofs together, then erase and lower those
same terms. The first executable `.jhc` slice is available through
`jihoo core`. Ordinary `.jh` elaboration has not yet moved to that core.
The implementation, principles and unfinished proof connections below
describe the existing verifier while that migration is in progress;
its Horn encoding is not a compatibility requirement on the replacement.

Status: research. The compiler proves checks and
[contracts](../language/contracts.md) itself
([`jihoo verify`](../reference/command-line.md#verification); every
build removes the proved checks and rejects unproved contracts), and runs
on its own source; the
experiments that led to it are in
[jihoo-proofs/obligations](https://github.com/jihoolang/jihoo-proofs/tree/main/obligations).

## Goal

jihoo 0.5 proves, while compiling, that a program's checks cannot fail and
that its functions meet their contracts. A proof costs nothing at run time:
it is checked and then erased, and a check that is proved is removed, so a
verified program is faster than the same program unverified.

jihoo 0.6 makes proofs importable libraries over the native core: lemmas
about integers, sequences and the program's own data, proved by induction
and used in program specifications. Mathematics beyond what programs need
grows from there through the same core's types and proofs, erased before
runtime code generation. The earlier Horn library remains part of the
existing verifier's development, not a required API for these libraries.

## Principles

- **A small checker trusts nothing the prover produced**, the way the
  [borrow kernel](redesign.md) trusts nothing sema decided and Horn's kernel
  trusts nothing its engine produced. Provers are untrusted and may be large,
  heuristic or external; their bugs lose proofs, never soundness.
- **Obligations come from MIR**, after `elab` and `check`, where every move,
  borrow, check and drop is explicit. Ownership does most of the work that
  separation logic does elsewhere: without shared mutable state, an `inout x`
  is a value going in and a value coming out.
- **Proved or kept.** The checks the compiler inserts (bounds, overflow,
  division by zero) stay at run time unless proved. An explicit contract that
  is not proved is a compile error; a debug option may turn contracts into
  run-time checks, but nothing turns them into assumptions.
- **No new trust in the seed.** The compiler and `lib/std` use a new
  feature only after a release, as for every feature
  ([self-hosting](self-hosting.md)).

## How a check is proved

```
MIR ──▶ obligation generator ──▶ goals ──▶ prover ──▶ certificate ──▶ checker
        (trusted: semantics)               (untrusted)                 (trusted)
```

A goal is *these facts imply that claim*. For the checks MIR inserts today,
the facts and claims are linear integer inequalities, and the certificate is
a list of Farkas weights: non-negative multipliers for the facts and the
negated claim whose sum is a negative constant. The checker multiplies and
adds; it decides nothing else. A Fourier–Motzkin or simplex prover finds the
weights. Loops are cut at their heads by invariants; each path from the entry,
or a loop head, to a check, a return or a loop head gives the goals on that
path.

Goals that need induction (a property of every element, of every `n`) are
0.6's: the [Horn](https://github.com/jihoo12/horn) kernel's schematic
certificates, already ported to jihoo in jihoo-proofs, check them.

## What is trusted

| Part | Trusted | Why |
| --- | --- | --- |
| The checker (`linear.jh`, 155 lines; later the Horn kernel) | yes | it accepts the proof |
| The obligation generator (`vc.jh`, 1,670 lines, the model `obligations.jh` builds from MIR, 2,250, and the arithmetic on forms in `forms.jh`, 53) | yes | it states what MIR means: a wrong rule proves a false thing |
| What a proof rests on, what is removed and which contracts are errors (`verify.jh`, 840) | yes | a proof under an unproved assumption must not count |
| MIR itself and `check.jh` | yes, already | obligations assume a well-borrowed program, and that `unreachable` blocks are not reached |
| Where the checker runs: compiled into `jihoo`, or in `interp.jh` | yes | |
| Provers (`fm.jh`), invariant inference and cut points (`infer.jh`) | no | everything they say is checked |

Line counts leave out comments, blank lines and tests.

The generator is the hard part, as Horn's rules are for cubical type theory.
It is tested against the interpreter, which already executes MIR: on random
inputs that satisfy a function's `requires`, a check the generator proved must
never fail and an `ensures` must hold. The build's overflow mode is part of
the semantics: with `--release`, `+` wraps and gives no obligation.

## Findings so far

The obligations experiment models MIR's integer part and proves two
functions transcribed from `emit-mir`:

- `clamp(x, lo, hi)` meets `lo <= result <= hi` under `lo <= hi`
  (6 of 6 goals).
- In `sum(xs)`, with the invariant `0 <= i <= xs.len`, the bounds check of
  `xs[i]` and the overflow check of `i + 1` are proved; `s + xs[i]` can
  overflow and stays unproved (8 of 10).
- Ten rejection cases pass: changed or negative weights, false claims, a
  missing `requires`, invariants that fail on entry or are not preserved,
  an off-by-one loop condition, a loop without an invariant.
- At `-O2` nothing of the verifier remains in the program.
- **Compile-time evaluation is too slow for this.** `clamp` takes 1.35
  million interpreter steps and `sum` 3.96 million, against a limit of one
  million per evaluation; about 60% of them are `std` code (a `Vec(i128)`
  push is about 46 steps).

The model now comes from the compiler:
[`emit-obligations`](../reference/command-line.md#verification-model)
prints it, and the same functions verified from its output get the same
verdicts as the hand-written ones. Two more programs check the
boundaries with real MIR: a loop `while i <= xs.len` leaves `xs[i]`
unproved, and a local lent to an `inout` parameter is opaque after the
call, so an `ensures` that depends on its old value is not proved. Reading
`x as u64 < len as u64` as `0 <= x < len` needs the length's range, which
the model takes from the view: a length is never negative.

The generator is now tested against the interpreter, as planned above:
every check in the model carries the span at which compile-time evaluation
reports it failing, and random inputs that meet a function's `requires`
run as `const`s. No check the generator proved has failed, in debug or
`--release` builds, over three samples (slices, unsigned and narrow
integers, casts, a local changed through `inout`); the unproved ones do
fail (`255 + 1` in a `u8`, `0 - 1` in a `u64`, the off-by-one loop). The
test itself is tested: making the model read `i <= len` as `i < len`, or
forget that `bump(&x)` changes `x`, is reported as a soundness bug.

The same test runs over every program in `tests/run` and `examples`: 98
files, 364 functions, 317 checks, 25 of them proved, and no proved check
failed on 270 random inputs. Most checks are in loops, and a loop without
an invariant proves nothing. Untrusted Houdini-style inference, which
proposes bounds between a loop's counters, its arguments and lengths and
keeps those that check, raises the proved checks from 25 to 66, still
with none failing. The runs found bugs only in the tools: the checker and
the generator now keep every number within bounds where i128 arithmetic
cannot overflow, give up on a function after 2,000 paths, and stop a path
that comes back to a block instead of unrolling the loop; a function they
gave up on proves none of its checks.

Each opaque value now carries the reason the model does not follow it,
and each unproved check reports where the values it depends on come from.
Over the same corpus, with inference, 69 of 317 checks are proved; of the
others, about 80 depend on a value loaded from memory (an element of a
`Vec`, a field behind a borrow), about 35 on a call's result, about 70 on
a loop the inferred invariants do not cover, 13 on an argument that only
a `requires` could bound, and 30 are checks the model cannot state. Loads
and calls need contracts (a `Vec`'s elements, the callee's `ensures`):
that is where the proof rate comes from next, more than from a richer
arithmetic. MIR's `unreachable` is trusted, as LLVM trusts it: a path that
reaches it ends there.

Contracts are now written in the source
([syntax](../language/contracts.md)) instead of in a separate file naming
MIR's local and block numbers. Sema lowers each clause to a linear form
over MIR locals, never run and invisible to `elab` and `check`, and
`emit-obligations` prints it next to the function's MIR. Clauses take
`result` as local 0, and a parameter in `ensures` (or `old(x)`) as an
entry variable, equal to the parameter on entry. Three things the model
did not follow are now variables: the integer an `inout` parameter points
to, when its pointer only reaches it; a local lent to one call
(`bump(&x)`), which the call gives a new value; and at a loop head, a
variable the function never assigns, which keeps its value on entry, so
`requires` still holds of it there. A call proves the callee's
`requires` with its arguments, and assumes its `ensures` of the new values.
In jihoo-proofs, a sample of calls proves `bump`'s and `inc`'s contracts,
a caller's `ensures` from them, a loop whose invariant carries what the
calls promise, and a recursive function. A call that cannot meet its
callee's `requires` stays unproved. The differential test now separates a
failure under a contract that is not proved (a callee's unproved
`ensures`, or a `requires` a call left unproved) from a bug, and forgetting
to prove a callee's `requires` is caught as a bug. The corpus, which has no
contracts, is unchanged: 69 of 317 checks proved, none failing.

The checker now runs in the compiler, as compiled code
([`jihoo verify`](../reference/command-line.md#verification)), on the
model built from MIR in memory rather than read from text. Three changes
made it fit real programs, the compiler's own first:

- **Sparse forms.** A linear form lists its nonzero terms. The
  experiment's dense forms grew with the number of variables, and on the
  compiler's `drive` (1,387 blocks, about 2,000 locals) the path states
  needed more than 4 GB.
- **Cut points where paths meet.** Following every path between loop heads
  doubles the paths with each branch. An untrusted pass, in an order
  where every block comes after the blocks that reach it, makes a block a
  cut point when more than 32 paths reach it. A cut point is checked like
  an invariant (with no facts, or the facts inference proposes) and starts
  new paths, so the work is linear in the size of the function. The
  generator checks that no path runs more blocks than the function has,
  which a cycle without a cut point would do.
- **What a proof rests on.** Every fact on a path is tagged with what it
  rests on: nothing (the path, a type's range), the function's
  `requires`, a cut point's facts, or a callee's `ensures`. The facts a
  certificate gives a positive weight are what the proof used. The
  assumptions that hold are the greatest set where each one is proved,
  each proof resting only on assumptions in the set: a function's
  `requires` when every call proves it and nothing else can call it (an
  exported function, the entry, a destructor, a function in a `dyn` table
  or used as a value), its `ensures` and its cut points' facts when
  every path proves them. A check is proved, and removed by verification,
  only when each of its obligations is. Without the tags, one wrong
  `ensures` in `main` made every `requires` that `main` proved unproved.

`tests/verify` lists the verdicts for loops and contracts, and the
`verify` suite runs every program of `tests/run` built with `--verify`,
which must do the same as without: the programs that trap on purpose
still trap. jihoo-proofs' differential test takes the compiler's verdicts
with `--verdicts compiler`: over its samples (debug and `--release`) and
the 99 files of `tests/run` and `examples`, no check the compiler proved
failed in the interpreter.

On its own source (`jihoo verify compiler/main.jh`, 3,587 functions with
the instances of `std`), the compiler proves 378 of its 2,489 checks in
22 seconds and 700 MB, and follows all but 3 functions everywhere. Of the
others, about 800 depend on a value loaded from memory (a field, a
`Vec`'s contents), about 500 on a loop the inferred invariants do not
cover, about 480 on an argument, and about 100 on a call's result. The
bounds checks of `Vec` indexing are inside `std`'s `Vec.index`, where the
length is a field; half the kept checks are in `std`. `std` contracts
over lengths and fields (step 5) are the next source of proofs.

### Fields, panics and calls

Step 5 needed three things in the model before `std` could state useful
contracts, and one decision.

- **Fields are variables.** An integer field of a local (`x.f.g`), or of
  what a borrowed local points to (`(*self).len`), is a variable while the
  model sees everything that changes it: the local's address is never
  taken, every mutable borrow of it or its parts is passed to a single
  call, and no part of its type is `#[interior]`. An assignment to the
  field or to a place containing it gives it a value (a copy of the
  source's field when there is one), and so does an assignment to the
  borrow it is reached through (`p = &v` makes `(*p).len` the variable of
  `v.len`); a drop, a call lent a place that contains it, a call given a
  mutable borrow that reaches it, and a call writing its result there give
  it a new value. The borrow kernel guarantees that nothing else changes
  it while a borrow lives; unsafe code that writes through a raw pointer
  to a place held under a borrow breaks the promise that `noalias` on
  borrowed parameters already relies on, and that is the assumption the
  model adds. A field of a parameter has an entry value like the
  parameter, so clauses name fields (`self.len`, `old(self.len)`) and
  `x.len()` as the `len` method's `ensures result == ...` defines it, and
  a call maps the callee's fields to the caller's variables: those of its
  arguments, through the argument when the parameter is a borrow, and
  those of the place its result goes to.
- **Panics are checks.** A call to a function that never returns, and
  `trap()`, is a check that the path cannot be taken; proved, it becomes
  MIR's `unreachable` and its branch goes away. Proving it needs
  conditions that are not conjunctions: `x != y`, and `i as u64 >= len as
  u64`, which is `i < 0 || i >= len` when `len` is not negative and three
  cases when the model does not know that. A bool now carries what holds
  when it is true and what holds when it is false, each a disjunction of
  conjunctions (at most 8); a branch adds the disjunction to the path, and
  an obligation is proved when it is proved in every case (at most 16, the
  latest disjunctions first; the others are dropped, which only loses
  facts). An `assert` is proved by refuting each case of its negation.
- **A small function's panics are its callers' checks.** `Vec.index`
  panics when `i as u64 >= self.len as u64`; inside it, `i` is anything,
  so the panic stays. For a function of at most 32 blocks with such a
  call, the generator records each path from its entry to the panic, over
  the function's variables on entry; a call proves the panic away when
  every such path, with the arguments for the parameters (and the
  caller's variables for their fields), contradicts what the caller knows.
  The panic is then a check at the call, and verification sends the call to a
  copy of the function without the panics that call proved away. A site
  that a path from a loop head reaches, or whose paths say nothing about
  the entry values (`malloc` failed, an enum's tag), is not lifted.

The decision: **`requires` stays the caller's duty.** Under the rule
that a function's `requires` holds only when every call proves it,
putting `requires 0 <= i && i < self.len` on `Vec.index` would remove its
check only in an instance whose every call proves it, which in the
compiler is almost none, and would make every other `v[i]` an unproved
contract, which step 3 turns into an error. Lifting needs no `requires`:
each call proves or keeps its own bounds check, and unproved calls run
the original. `std`'s contracts are therefore `ensures` that describe
what holds when the function returns (`Vec.len` returns `self.len`,
`push` adds one, `as_slice`'s length is `self.len`), which callers use to
prove the panics away, and no `requires` on functions that check their
arguments.

On the compiler's own source, before `std` states any contract, fields as
variables raise the bounds and overflow checks proved from 378 of 2,489 to
698 of 2,631 (the source grew), in about 15 seconds and 700 MB. The new
kinds add 260 calls that never return (none proved: the compiler's panics
mark states it believes impossible for reasons the model cannot see) and
1,769 calls that may reach a small function's panic, of which 4 are
proved. The `verify` suite fails when `jihoo verify compiler/main.jh`
proves fewer of any kind than `tests/verify/compiler.proved` records.

With 0.4.4 as the seed, `std` states its contracts: `Vec.new` and
`with_capacity` return an empty vector, `len` returns `self.len`,
`reserve` keeps it, `push` and `insert` add one, `remove` takes one away,
`pop` takes at most one away, and `as_slice`'s length is `self.len`;
`String`'s are the same over its bytes (`self.len()`), with `push_str`
adding the `str`'s length. No `std` function has a `requires`. Every one
of these `ensures` is proved. The compiler then proves 720 bounds and
overflow checks and 120 of its calls that may panic, nearly all `v[i]` in
loops over `v` or after a length test; most of the other `v[i]` index
with a value loaded from memory (a token's position, a block's number),
which no contract on `Vec` can bound.

A case of a disjunction is often refuted by the path alone, without the
claim: in `if x > 0 { return x }; y` under `requires x > 0 || y > 0`, the
case `x > 0` contradicts the branch taken, and says nothing about `y`.
The prover kept only the facts connected to the claim's variables, so it
missed those; when that fails it now tries the latest facts (a case and
the conditions before it) by themselves. That proves 746 bounds and
overflow checks on the compiler and 125 calls, for about 7% more time.

`reserve` then also promised room: `self.len + n <= self.cap` on return.
That proves `push`'s `self.len += 1` in each of its instances (900 bounds
and overflow checks on the compiler, with the prover's retry above). Working out what `Vec` can promise
(its type invariant, next) found a bug: `push` and `insert` reserved only
when `len == cap`, but a `String` from a literal borrows the literal's
bytes with `cap` 0, so they wrote into the literal. They now reserve when `len >= cap`.

The finding about cost decides where the checker runs. A compiler pass can run the
checker as compiled code, outside the interpreter's budget; library proofs
(0.6) run in the interpreter and need it to be faster or their limit to be
chosen by the program.

### Type invariants

The checks inside `std`'s own methods need facts no caller's contract
gives: `Vec.pop`'s `self.len -= 1` after `self.len != 0` needs `len` not
to be negative. A struct's `invariant`
([contracts](../language/contracts.md#type-invariants)) states such facts
once, over `self`'s fields.

- **Where it is assumed.** On entry, of what each parameter holds: the
  parameter, or what it borrows, and the structs inside them by fields (at
  most 3 deep), not through other borrows or pointers. After a call, of the
  place the result goes to and the places lent mutably to the call. A
  function that code outside the program may call (`export`, `main`)
  assumes nothing of its parameters. Each assumed fact rests on
  `Tag.TypeInvariant(type)`.
- **Who proves it.** Only a *writer* of the type can make a value that
  breaks it: a function that assigns one of its fields, lends or takes the
  address of one, or builds one with a struct literal (the fields are
  private to the struct's module, so outside it, only code that module
  exports). A writer proves the invariant, with `Source.TypeInvariant`,
  wherever another function could see the value: of what each call is
  given (by value, borrowed or lent), of what a drop destroys (a
  destructor assumes it), and on return, of its result and of what its
  `inout` parameters hold. A function that writes nothing passes on
  values it was given, which already hold it, or gets them from calls.
- **What counts.** A proof that assumes a type's invariant counts only
  when every writer's obligations of that type are proved and the writer
  was followed everywhere: one failure removes them all, which is the
  induction on the order in which functions see values. As elsewhere,
  unsafe code that stores a value breaking it where another function
  reads it, or writes the fields through a pointer the model does not see
  as a field, breaks the promise.
- **Cost.** Every value of the type adds its facts after each call. Those
  of a disjunctive invariant split proofs into cases, so an obligation
  takes such a disjunction only when it names the claim's variables, or
  those of the facts that do.

On a local build with `invariant 0 <= self.len && 0 <= self.cap` on `Vec`,
the writers that failed to prove it were real bugs: `truncate` and
`filled` with a negative count gave a negative length (`truncate` then
dropped values before the buffer), and `reserve` with a negative count
could copy borrowed bytes past what it allocated. With 0.4.5 as the seed,
`std` states it, with `with_capacity` ensuring room for `n` values and
loop invariants in `filled` and `truncate`; every writer proves it, and
the compiler's bounds and overflow checks proved go from 907 to 939, for
about 21 seconds instead of 15. `len <= cap || cap == 0` holds too, but
costs more than it proves yet.

### The checker's own checks

Roadmap step 6.6 starts with the trusted checker, `linear.jh`: the loops
of `Lin.combine` (merging two sorted lists of terms), `sorted` and
`check` state their invariants, and the compiler proves every bounds check
in the checker. Four changes made that possible, and raised the proved
checks of the whole compiler too:

- **Wrapping arithmetic** is followed (`AddWrap`, `SubWrap` in `vc.jh`):
  a range `for` steps its counter with `+% 1`, which was opaque, so no
  loop over `0..v.len()` kept its counter's bounds. The result is a new
  variable that equals the exact sum when that fits the type, and
  otherwise the sum minus or plus the type's size; both operands are in
  the type's range, so it wraps at most once. A constant step that is not
  negative cannot go below, which leaves two cases. 128-bit types are not
  followed, as before. `--release` builds' `+` and `-` are the same.
- **Candidates for a range's end.** The end is a variable assigned once
  (a copy of `len()`), which a cut point forgets like any other. Inference
  now proposes, for a variable assigned once that a counter is compared
  with, that the counter is at most it and that it equals what it is a
  copy of, through copies and the fields given to the call that made it
  (`len()`'s `self.len`). Loops with written invariants get the candidates
  after the written facts, which are never dropped, and cut points where
  many paths meet get the written invariants' facts, since one inside a
  loop must carry them to the head. Inference stops in a function once
  its rounds have proved goals of 500,000 facts in all, and functions
  above 400 blocks get no candidates about ends: there, rounds cost
  seconds and settle on nothing.
- **Differences first.** Most facts on a path are differences
  (`x - y + c >= 0`) or bounds, and Fourier–Motzkin over 100 of them can
  run out of rows on a goal as plain as `r == i + 1 && i >= 0` implies
  `r >= 0`. The prover first looks for a negative cycle among them
  (Bellman–Ford, with a node for zero): its facts, each weighted by how
  often the cycle uses it, add up to a negative constant, which is the
  certificate. Then elimination runs over the 8, 24 and 64 facts nearest
  the claim, and last over all of them.
- **Cases by relevance.** An obligation splits on the disjunctions that
  name the claim's variables (or those of facts that do) first, and then
  on the others while the cases stay at most 16; before, the latest ones
  came first, and one unrelated `k != 0` could push out the `i != len` a
  loop's invariant needed.

The compiler then proves 969 of its 2,748 bounds and overflow checks
(from 939), and 155 calls prove a panic away (from 129), in about 22
seconds. What the checker keeps are the overflow checks of its `i128`
arithmetic: products of a coefficient and a weight, which are not linear,
and `i128` values, whose range the checker's own numbers cannot state.
`check` no longer computes `abs` of its inputs (`i128::MIN` would trap) but
tests each number against the bound.

The checker then lost those last checks by computing exactly instead of
within bounds: its sums go through `add` and `mul`, which give `None`
when the result does not fit an i128 (overflow of `+%` gives the sum the
other sign than both operands; `mul` multiplies the magnitudes in halves
of 64 bits, none of whose products can wrap a `u128`), and a certificate
whose sum does not fit is rejected. Nothing in the checker can trap, its
soundness no longer rests on the bounds the generator and provers keep
their numbers within (those only make certificates fit), and it accepts
certificates with weights above 2^50 that it used to reject. The
generator's arithmetic on forms, which traps on overflow, moved to
`forms.jh`. `jihoo verify compiler/main.jh` keeps no check in
`linear.jh`, and `tests/verify/compiler.proved` says so with a `clean`
line, which the `verify` suite checks.

### The checker's soundness

The last part of 6.6 is to prove, in jihoo, that the checker is sound:
when `check` accepts a certificate, no integer point satisfies the facts
and the negated claim. It is stated and proved in Horn rules, and
[`lib/proof`](../../lib/proof/schematic.jh) checks the proof: Horn's
schematic checker in jihoo, with implication goals, rule hypotheses,
application, induction under hypotheses and inversion, whose algorithm
Horn's Agda development proves sound.

The theory ([`lib/proof/farkas.jh`](../../lib/proof/farkas.jh)) has two
parts.

- **The integers**, as the axioms of an ordered commutative ring
  ([`lib/proof/ring.jh`](../../lib/proof/ring.jh)): `eq` with congruence,
  the ring laws, `le` with addition, products of non-negatives and
  `0 <= 1`, and `1 <= 0` gives `false`. A sort `Z` of expressions, never
  inducted on or inverted, so the value of a form at a point
  (`val l x`, `ev t x`, `look x v`) is an expression with defining
  equations, and needs no proof that it exists. Defining the integers by
  rules instead, as functions on numerals, makes every ring law an
  induction, and Horn's proof search does not find them: an intermediate
  result has to exist, which a relational encoding cannot state.
- **The checker**: `ms n a b w r` merges two term lists as
  `Lin.add_scaled` does, one rule per branch of its loop, with `n`
  counting the iterations; `push` keeps a coefficient or drops one that
  is zero; `as` is `add_scaled` on forms; `sums` is the loop over the
  facts, skipping zero weights; and `accepts` is what `check` tests before
  it returns `Ok`: non-negative weights, the negated claim
  `-1 - claim`, the weighted sum, a constant `c` with `c + 1 <= 0`. The
  model admits more than the code (any order of variables, sums with a
  zero weight), which only makes the theorem stronger.

The theorem: `accepts fs cl ws wc`, `sat fs x` (every fact is
non-negative at `x`) and `val cl x + 1 <= 0` give `false`. The proof
(1,687 steps, checked in under a second) shows that a merge evaluates to
`a + w * b` by induction on its iterations, and that a weighted sum of
non-negative facts stays non-negative by induction on the facts. Its
ring identities come from a prover that normalizes both sides to sorted
sums of monomials and writes each rewrite as a step; like the rest of the
certificate's construction (`lib/proof/cert.jh`), it is not trusted. A
checker without the test of the sum's sign, or of any weight's, is not
proved by the same certificate, and neither is a merge that adds the
coefficients of two different variables.

What was left before the theorem is about the code itself:

1. **Adequacy.** Done ([`agda/`](../../agda/Adequacy.agda)). What the
   schematic checker establishes is that the goal holds in every model
   of the rules: Horn's Agda development proves each form of a
   certificate sound in any set of ground judgments closed under the
   rules and supported by them (each member is the conclusion of a rule
   instance whose premises are members), not only for derivability, the
   least such set. Induction is on sorts, whose ground terms do not
   depend on the model, and inversion needs only the support.
   `Adequacy.agda` gives a model in an ordered commutative ring: `eq`,
   `le` and `false` are equality, order and falsity of values, and every
   other judgment holds when the rules derive it from true comparisons,
   which is what `emit-horn`'s rules say of a run of the code. The rules
   that conclude a comparison are the ring's axioms, the defining
   equations of `look`, `ev` and `val`, and `efq` rules, and each holds
   in the ring; Agda checks by evaluation that no other rule of the
   theory concludes one, and rejects the theory with a rule `le z1 z0`
   added. The theory reaches Agda as the checker parses it:
   `proof.schematic.agda` writes it, numbered as the checker numbers it,
   and `agda/theory.jh` builds it from `emit-horn`'s rules as
   `refine.check` does. `Integers.agda` shows the integers (differences
   of naturals) are such a ring, with a small normalizer to Horn form for
   the identities. The theorem: when `check` returns `Ok` for facts `fs`,
   claim `cl` and weights `ws`, no integer point makes every fact
   non-negative and the claim negative. A point (sort `X`) is built by
   `pt` from the values of finitely many variables; `X` had no
   constructor before, and a sort without ground terms makes every
   statement about its values hold vacuously. `nix flake check` runs it
   (`agda/check.sh`, which also checks the certificate in Agda, a few
   minutes).
2. **The code.** Done ([below](#the-proof-of-the-code)): the rules
   `jihoo emit-horn` writes for `linear.jh` give `accepts` when `check`
   returns `Ok`.
3. **Compile time.** The check runs as compiled code in the test; at
   compile time it exceeds the interpreter's million steps (0.6, step 3).

### The code as Horn rules

The soundness proof is about a model of `check`, and step 6.6.3 ties it to
the code: `jihoo emit-horn` ([`horn.jh`](../../compiler/horn.jh)) states
in Horn rules what a function's MIR computes, and a proof in Horn then
shows that `check` returning `Ok` gives `accepts`. Like `vc.jh`, the
translation is trusted: it says what MIR means.

It runs each path of a function symbolically, from the entry or a loop
head (a target of a back edge) to a return or a loop head, and writes one
rule per path. A function `f` is the predicate `fn.f(args, result)`; a
loop head `K` is `fn.f@K(n, live locals, result)`, which holds when the
function, from `K` with those values, returns that result after passing
loop heads at most `n` times (the fuel the proof inducts on). Values are
terms: integers are exact ring expressions (a checked `+` that overflows
traps, and a path that traps, panics or reaches `unreachable` has no
rule), comparisons become `le` and `eq` premises, a bool that leaves a
path becomes `B.tt` or `B.ff` case by case, structs and enums are
constructors (a variable is replaced by its constructor where a field is
read, and a `switch` on a discriminant takes one rule per variant), a
shared borrow is the value it borrows (nothing changes it while it
lives), and a mutable one is the place, which `push` updates. `Vec` is a
list, with `len`, `nth` and `snoc` relations that say what `std`'s `Vec`
does; that `std` does it is assumed, as the verifier assumes `std`'s
`ensures`. `overflowing_mul(a, b)` is `(a * b, false)` or `(anything,
true)`, so `linear.jh` uses it rather than the bit tricks it had.

What is outside the fragment is an error, never an approximation. A
loop head's state is the locals that may be read before they are set
from there on; within a path, `len` and `index` of the same arguments
give one result (they are functions), and a path that takes a comparison
and one that contradicts it (its negation, or `<` against `==`) has no
rule. A struct argument is its constructor of new variables. `check`
and the five functions it calls are 126 rules.

### The proof of the code

[`lib/proof/refine.jh`](../../lib/proof/refine.jh) proves, from those
rules, the model and the ring axioms:

```text
fn.check (Goal.mk fs cl) (Certificate.mk ws) (Ok m), sat fs x,
val cl x + 1 <= 0  ⊢  false
```

that is, when the compiled `check` accepts a certificate, no point
satisfies its facts and negated claim. It is 36,631 steps with 45
inductions, built in under a second; `lib/proof` checks it, and so does
Horn's own checker. Its parts:

- **Lists**: for each of `linear.jh`'s list sorts, lemmas about lengths,
  `nth` and suffixes (`sfx l i s`: `s` is `l` without its first `i`
  elements), proved by induction on lists; and appending.
- **`add_scaled`'s loop**, by induction on the fuel of its head: from
  indices `i`, `j` and the output so far, the result is the output
  followed by a merge (`ms`) of the two suffixes. Each pass is a lemma of
  its own (from the left, the right or both, pushing a term or dropping
  a zero), and every rule of the loop head is either one of those passes,
  its end, or a path whose comparisons add up to a contradiction (the
  proof finds the combination). Then a call returning `Some` gives `as`.
- **`check`'s loops**: the weights loop leaves non-negative weights, the
  sum loop leaves a sum whose rest is `good`, and both feed `accepts`.

Horn certificates cannot take a derived fact apart (only a hypothesis is
inverted), so what a loop has left to do is a predicate whose
definition hides its witnesses (`ares`, `g80`, `g45`), and a lemma whose
hypothesis is that predicate takes it apart outside the induction.

The `verify` suite translates `check` and checks the proof, and also
translates two broken copies of `linear.jh`, one without the test of the
sum's sign and one without the test of the weights', whose proofs do not
go through. `check` now reads the next fact on every pass of the sum
loop, so that the proof knows it when its weight is zero.

What this rests on: the translation (`horn.jh`, trusted as `vc.jh` is) and
`std`'s `Vec` being a list as `len`, `nth` and `snoc` say. The certificate
itself is checked by Agda, running Horn's checker for implicational
certificates, which Horn's Agda development proves sound in every model of
the rules; [`agda/Certified.agda`](../../agda/Certified.agda) reads the
result in ℤ ([above](#the-checkers-soundness)), so neither `lib/proof`'s
checker nor Horn's Rust one is trusted for it.

The translation and `Vec` are tested against the code they describe
([`tests/horn/differential`](../../tests/horn/differential/check.py)):
`cases.jh` runs the compiled `check`, `Lin.add_scaled`, `add` and `mul` on
random inputs (certificates built to be accepted, then often broken: a
weight changed or negative, a form unsorted, numbers near the ends of
i128), and `check.py`, a Horn solver of its own in Python, enumerates what
the rules derive for the same inputs. What the code returns must be among
them, and the only value besides overflow results (`None`, an error,
which the rules' exact `add` and `mul` may always give); a result only the
rules give must be one exact arithmetic allows where an i128 overflowed,
which an exact model of `add_scaled` checks. The `verify` suite runs 321
cases. Of the 108 rules `emit-horn` writes for the code, their
derivations use all 62 that a run can reach; each of the other 46 has a
premise the run cannot meet (an index past its list's length, which the
loop's invariant excludes, a negative weight after the weights are
checked, a negative length). Of 64 random mutants of the rules, as a
translation bug would make them, the test catches every one that changes
a reachable rule so that it loses what the code returns; those it misses
only add derivations (a
weaker comparison, a premise dropped where a later `nth` still bounds
the index), are equivalent (a swapped comparison next to an equality),
or change a rule no run reaches. A search that does not end (a rule that
leaves a list unbound) fails after 10 seconds.

### Execution bridge for list primitives

[`agda/ListExecution.agda`](../../agda/ListExecution.agda) begins the
execution-to-Horn proof with the three list sorts used by `linear.check`:
terms, facts and weights. Its executable operations are finite-list
length, recursive lookup and appending one element. For every list of
well-sorted ground values, it proves that each operation's result derives
the matching `len`, `nth` or `snoc` judgment in `Adequacy`'s model. A
lookup's index may be any ground integer expression with the appropriate
value; it is not required to have the syntax of a canonical numeral.

The proof uses six rule schemas per sort. Agda checks that each schema,
including its premises and variable sorts, is present in the theory
generated from the current `linear.jh`. They are not additional axioms.
The `list-execution` Nix check regenerates that theory, checks concrete
integer examples and requires rejection of three incorrect generated
rules: an off-by-one length, an off-by-one index and a lost push result.

This establishes finite-list primitive correspondence, not a native
`std.Vec` memory model. Its representation, allocation, capacity bounds,
pointer accesses and borrowing still need a simulation into these lists.
The checker's MIR arithmetic, overflow, calls and control-flow translation
also remain to be connected before its execution implies the Horn
relation required by `Certified.check-sound`. Differential testing remains
a regression check, and this partial bridge does not complete the 0.5.0
execution-correspondence release gate.

### Typed backing storage and list refinement

[`agda/VecMemory.agda`](../../agda/VecMemory.agda) gives the list bridge
a typed backing-store specification. Its descriptor carries length and
capacity; backing cells can be initialized or uninitialized. A
representation relation identifies the initialized prefix with a list,
without treating spare cells as elements. It also permits zero-capacity
borrowed storage with a nonzero length, as used by `String.from_static`.

Reads coincide with list lookup. An in-place push can succeed only when
its write is inside capacity and reaches an existing cell; it appends the
element and preserves every other backing cell. Relocation copies the
initialized prefix into storage of the requested capacity. Short sources
or destinations cannot succeed, and constructive theorems give successful
relocation and push executions for every prefix with sufficient capacity.
`VecHornExecution.agda` composes these operations with the actual generated
`len`, `nth` and `snoc` rules for the checker's three list sorts.

The `vec-memory` Nix check regenerates the theory for both targets. It
checks the examples and requires proof rejection when reads expose spare
storage, pushes use a wrong position/capacity/length, or relocation loses
a prefix element or invents capacity.

The actual `std.Vec` implementation and the checker's list-processing MIR
loops still need a simulation into this specification. Allocation success,
byte/pointer layout, separation between allocations, borrow enforcement,
growth policy and bounded machine arithmetic remain explicit obligations.
The model's `reserve-to` describes a successful copying relocation, not
all branches of the library's `reserve` or allocator failure. This does
not complete the whole-checker execution correspondence.

### Execution bridge for scalar helpers

[`agda/ScalarExecution.agda`](../../agda/ScalarExecution.agda) defines
executable exact addition and multiplication with inclusive integer
bounds. Success gives an in-range exact value; rejection means the exact
value lies outside the bounds. The theorems quantify over the bounds, so
signed i128 is an instance rather than an enumeration of values.

The MIR intrinsic contract says a false overflow flag gives the exact
result. A true flag says that result did not fit, with an in-range wrapped
value. `linear.add` and `linear.mul` discard that value, returning `None`;
the semantic projection therefore leaves its bits unspecified.
`projection-correct` proves that this flag branch agrees, up to integer
equality, with the executable checked operation. `checked-execution` and
`intrinsic-execution` give Horn witnesses representing each helper's
result numerically. Agda finds the actual generated rules by their
premises, conclusions and variable sorts, without depending on their
fresh identifiers. The Horn model may additionally derive spurious
overflow rejections; this proves the execution-to-model direction.

The `scalar-execution` Nix check regenerates the theory and checks the
proof and concrete boundary cases, and rejects rules with the wrong
arithmetic operation or a missing overflow result. Independent tests in
`tests/horn/scalars.py` read signed and unsigned boundary constants and
solve switch cases for both targets, also in the ordinary `verify` suite.
They found two bugs in numeral translation: taking i128's minimum's
magnitude overflowed in the compiler, and upper-half u128 bit patterns
were interpreted as negative values. Both now have regressions.

This does not yet prove observable wrapping behavior or the LLVM
implementation of overflowing intrinsics. The checker's general MIR
paths, calls and memory operations still need a simulation before the
whole execution-to-Horn theorem can be composed with its checked
soundness certificate. The source-to-MIR and MIR-to-LLVM boundaries remain
as stated in the roadmap.

### Execution of exported MIR graphs

[`agda/MirExecution.agda`](../../agda/MirExecution.agda) defines scalar
MIR execution over local frames, with copies, tuple fields, Option
construction, lifetime markers, jumps, boolean switches, overflowing
intrinsics and direct calls. Invalid reads/projections and stopped blocks
have no returning execution. Direct calls run the selected function's
graph in a fresh frame and resume with its result; the call relation
contains that execution derivation. It can describe arbitrary finite
executions and recursive calls. `wp-sound` proves finite symbolic
execution sound, with its fuel limiting the proof rather than the
execution relation. `Paths` and `paths-sound` also support inductive
invariants at selected blocks: each finite proof follows a path to a return
or an invariant, and executing an annotated block must re-establish these
conditions. Induction on a returning execution proves the postcondition
without fuel or a termination premise. Direct calls still require their
actual execution derivations. Proofs for recursive programs remain further
work.

[`agda/export-mir.jh`](../../agda/export-mir.jh) loads and compiles the
current `linear.jh` with two appended direct callers and an accumulator
loop, performs borrow/drop checking and serializes the actual MIR objects. It preserves every block,
statement and terminator of the selected functions, checks frame/graph
bounds, signatures and supported types, and rejects unsupported operations.
It is a trusted data serializer, not a certified translation of the
compiler frontend or an untrusted certificate producer.

`MirCorrespondence.agda` checks metadata and evaluates these exported
graphs in Agda. It proves every helper return has the intrinsic's flag
projection and constructs executions for all permitted intrinsic outcomes.
Callers compose their actual callee's execution proof. Those results have
numerical representations in the actual generated helper and caller Horn
rules, whose complete schemas and variable sorts Agda checks. `InI128`
specializes the intrinsic contract to signed i128. The wrapped result
still need not be modeled bit for bit because the helpers discard it on
overflow, which is now established by their exported control flow.

[`agda/MirLoopCorrespondence.agda`](../../agda/MirLoopCorrespondence.agda)
connects an inductive invariant to the actual exported `mir_loop` graph.
Starting with an in-range accumulator, the loop repeatedly adds a fixed
step, and returns the previous accumulator when the intrinsic reports
overflow. Every returning execution gives an in-range value whose next
addition is out of range. Its invariant also carries a numerical Horn
representation of the accumulator and a history that composes the
generated loop rules back to the function's entry. The proof checks the
entry, back-edge and exit schemas and their variable sorts; the back-edge
rule adds `fuel1`, and the exit starts at `fuel0`. No fixed iteration
bound is imposed. Every finite sequence of permitted intrinsic outcomes
also constructs an actual graph execution. The theorem is partial
correctness: a zero step need not terminate, and no termination result is
claimed.

The `mir-execution` Nix check regenerates data for both targets, checks
positive returning executions, and rejects changes to the operation,
overflow return, direct callee, local lifetime and caller rule. It also
requires rejection of an incorrect loop operation, return, accumulator
update, overflow branch or Horn step, and a missing Horn exit. Positive
examples exercise zero and multiple back edges, both overflow directions,
numerically equal integer representations and a cycle without a returning
execution. An unsupported wrapping operation must fail export. Its output
retains each target's MIR data, theory and Horn rules for review.

The proof depends on the serializer faithfully reading MIR and on the
stated MIR intrinsic contract. Other MIR operations, invariants for the
checker's list-processing loops, borrow/pointer and `Vec` memory semantics,
observable wrapping and the LLVM
intrinsic implementation remain separate obligations. This does not
establish execution correspondence for the whole checker or preservation
from source to MIR and from MIR to LLVM.

### Slices

The last of step 5 was slicing, `s[lo..hi]` of a `str`, slice, array,
`String` or `Vec`. It is built into the compiler rather than `std`, so
there was no contract to state; two things kept its checks:

- **The lowering.** Slicing checked `0 <= hi <= len` and `0 <= lo <= hi`
  as `hi < len + 1` and `lo < hi + 1` unsigned, and the two `+ 1` could
  overflow: nothing bounds a `str`'s length below 2^63 - 1. It now
  compares `hi <= len` and `lo <= hi` as `u64`s, which is the same test
  (a negative bound is above every length once cast) with nothing to
  overflow, and fewer instructions.
- **The length's range.** The slice's length is `hi - lo`, a form over
  other variables, so the length variable took that form and lost its
  range: the model did not know that `s[1..]` of a `str` of at least two
  bytes is not empty, since `s.len - 1` may be -1 as far as its terms say.
  A length given a form whose terms do not bound it now becomes a new
  variable equal to the form, whose range says it is not negative, as for
  every length the model takes from a view.

`tests/verify/slices.jh` slices after a length test, indexes into a
slice, and slices in a loop; every check is proved but a bound that may
be past the end. On the compiler, the lowering removes 109 checks, and of
the 2,675 bounds and overflow checks left, 975 are proved: 1,700 are kept
instead of 1,799.

### Verification in parallel

Before verification can run in every build, it has to cost about as much
as the borrow checks. Each function's obligations are proved
independently of the others' (what a proof rests on is decided afterwards,
for the whole program), so they are proved on several threads, the
costliest functions first, as the borrow checks are. That alone took
`jihoo verify compiler/main.jh` from 25 to 4.7 seconds on 20 threads, but
its peak memory from 1.6 GB to 8.8 GB: each obligation copied its path's
facts, and inference held every goal of a round until the round ended, so
the few largest functions, proved at once, each held hundreds of
megabytes. The generator now proves each obligation as it makes it and
keeps only the verdict and what the proof rests on (`vc.PROVE`);
inference's rounds build only the goals of the facts they test, and stop
building a fact's once one of them fails (`vc.INVARIANTS`); the
generation that records a small function's paths to its panics builds
none (`vc.LIFT`). The verdicts are the same, check for check, on the same
source; verification takes 3.5 seconds and 530 MB.

### Unproved contracts are errors

With verification cheap enough, every command that generates code runs
it: `build`, `run`, `test`, `emit-llvm` and `emit-obj` prove the program
and remove the proved checks, and `--no-verify` keeps every check and
proves nothing. An unproved contract is a compile error, as the
principles above say it must be, at the clause: an `ensures`, a written
`invariant`, a call that does not meet its callee's `requires`, a writer
that does not keep a type's invariant, and a `requires` on a function
that code outside the program may call (exported, the entry, a destructor
or used as a value), which nothing proves. `check --verify` reports the
same errors, and `jihoo verify` exits with status 1 when there are any.

A clause counts as unproved when it is not valid in the sense above:
also when its own proof succeeds but rests on an assumption that does
not hold. Such a clause's message says what it rests on (a `requires`
that some call does not meet, an `ensures`, a loop's invariant, a type's
invariant), and it is reported only when no clause fails on its own,
since proving those may prove it. One case the checks needed was a
`sink` parameter that the body assigns: `ensures` reads its value on
entry, but at a loop head nothing related that value to `requires`. A
cut point now assumes `requires` of the parameters' values on entry, in
the variables that hold them, which nothing assigns.

`tests/fail` has a case per kind (`unproved_*.jh`, marked `// verify`,
built with `emit-llvm` and checked with `check --verify`): a wrong
`ensures`, a call that does not meet a `requires`, an invariant that does
not hold on entry, one that an iteration does not preserve, one an
off-by-one loop breaks, a writer breaking a type's invariant, and an
exported function with a `requires`. The `verify` suite runs `tests/run`
with `--no-verify` and compares with the ordinary, verified run. The
compiler built by itself this way, without its proved checks, passes the
whole test suite.

Making them errors found that `std`'s contracts did not all hold in
`--release` builds, where `+` wraps: `Vec.reserve` computed `len + n`
with it, so a huge `n` made the sum negative and `reserve` returned
without room, against its `ensures`; and `File.read` added the count the
system returned to the length unchecked. `reserve` now returns at once
when `n <= cap - len` (which cannot overflow), adds with `+%` and panics
when the sum wraps below `len`, and `read` panics if the system read
more than it was asked. Both modes prove every instance, and the `verify`
suite checks that `jihoo verify --release compiler/main.jh` reports no
unproved contract. With `reserve`'s shorter fast path the compiler proves
1,145 of its 2,681 bounds and overflow checks.

### Semantic check-removal specification

[`agda/CheckRemoval.agda`](../../agda/CheckRemoval.agda) starts the
verification-condition and check-removal proof required for 0.5.0. Its
small-step semantics describes a graph of assertions, checked primitive
operations, branches, jumps, returns and traps. `vc` constructs local
conditions from a proposed invariant at every program point and a mask
of checks to remove. A removed guard must hold in every invariant state;
each possible successful step must preserve the next invariant. A
return establishes the postcondition. A retained check may still fail.

When all these conditions hold, the original and erased graphs have
matching steps from invariant states, in both directions. The proof
preserves every finite trace, including observable effects, and the
entire final state or retained failure. It works on cyclic graphs
without a fuel bound or a termination assumption. Primitive operations
may change arbitrary state nondeterministically: their continuation
condition must cover every transition, which prevents reusing a fact
after an opaque write without proving it still holds.

[`agda/CertifiedRemoval.agda`](../../agda/CertifiedRemoval.agda) connects
this guard condition to `Certified.check-sound`: if the generated Horn
relation for the checker accepts, the path's facts hold in every
invariant state, and failure of the guard makes the claim negative, the
guard always holds there. Continuing to the next invariant remains a
separate obligation. This composition uses the certificate Agda checks,
not a trusted prover or jihoo's Horn checker.

`nix flake check` checks these theorems. The `check-removal` check also
checks an observable countdown loop, arbitrary writes and retained
failures, and requires Agda to reject conditions that remove a false
guard, preserve an invalid invariant after a write, omit a branch or
return without establishing a postcondition.
`nix develop .#proofs` supplies the same tools and pinned Horn input.

The specification is not yet connected to the implementation's
conditions in `obligations.jh` and `vc.jh`, or all erasures in `verify.jh`.
Checked primitives are defined as guarded unchecked operations; relating
this to exact machine arithmetic, overflow and memory is still a proof
obligation. Execution-to-Horn correspondence, contract and recursive-call
dependencies, mutable borrows, type invariants, incomplete analysis,
panic removal and call retargeting remain required for 0.5.0. Neither
these proofs nor self-verification tests establish preservation from
source to MIR or from MIR to LLVM; those are separate obligations and
LLVM remains trusted.

## Open questions

- **Syntax.** Settled for functions and loops
  ([contracts](../language/contracts.md)), with fields and `.len()`; left
  are where proofs that need lemmas name them, and invariants on `for`
  loops over iterators. `||` and `!` make a clause a disjunction of
  conjunctions, at most 8: assumed, it is a disjunction on the path like a
  bool's; to be proved, the path and every alternative failing must be
  impossible.
- **Places.** Integer fields of locals and of borrowed parameters are
  variables ([above](#fields-panics-and-calls)); a `Vec`'s elements, and
  fields reached through a raw pointer or a field that is itself a borrow,
  are not. Type invariants ([below](#type-invariants)) say what holds of
  the fields of every value of a struct.
- **Calls.** Modular: a call assumes the callee's `ensures` after proving
  its `requires`, and proves a small callee's panics away by itself.
  Functions too large to lift need `requires` the callers meet, or
  contracts that are the first users of 0.6's lemmas.
- **Integers.** Fourier–Motzkin is complete over the rationals, not the
  integers: a goal that needs parity or rounding is lost (never wrongly
  proved). Cutting planes or a bounded integer search fix that later.
- **Invariant inference.** Untrusted candidates (the loop condition, the
  initial values, bounds of indices) kept only when they check: most loops
  over `0..n` should need no annotation.

## Plan

The [roadmap](roadmap.md#6-verification-05) lists the steps and their
completion criteria.
