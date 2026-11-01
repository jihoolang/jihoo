# Design: verification (0.5) and mathematics (0.6)

Status: research. Nothing on this page is in the compiler yet; the first
experiment is [jihoo-proofs/obligations](https://github.com/jihoolang/jihoo-proofs/tree/main/obligations).

## Goal

jihoo 0.5 proves, while compiling, that a program's checks cannot fail and
that its functions meet their contracts. A proof costs nothing at run time:
it is checked and then erased, and a check that is proved is removed, so a
verified program is faster than the same program unverified.

jihoo 0.6 makes the proofs themselves a jihoo library: lemmas about
integers, sequences and the program's own data, proved by induction and used
by 0.5's contracts. Mathematics beyond what programs need grows from there,
as a library on compile-time evaluation, not as a change to jihoo's type
system: jihoo stays a systems language that is good at running a proof
kernel.

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
| The checker (linear; later the Horn kernel) | yes | it accepts the proof |
| The obligation generator | yes | it states what MIR means: a wrong rule proves a false thing |
| MIR itself and `check.jh` | yes, already | obligations assume a well-borrowed program |
| Where the checker runs: compiled into `jihoo`, or in `interp.jh` | yes | |
| Provers, invariant inference | no | everything they say is checked |

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
an invariant proves nothing, which is what invariant inference (step 4 of
the plan) is for. The runs found bugs only in the tools: the checker and
the generator now keep every number within bounds where i128 arithmetic
cannot overflow, give up on a function after 2,000 paths, and stop a path
that comes back to a block instead of unrolling the loop; a function they
gave up on proves none of its checks.

The finding about cost decides where the checker runs. A compiler pass can run the
checker as compiled code, outside the interpreter's budget; library proofs
(0.6) run in the interpreter and need it to be faster or their limit to be
chosen by the program.

## Open questions

- **Syntax.** `requires`/`ensures` on functions, `invariant` on loops,
  `old(x)` for an `inout` parameter's value on entry, and where proofs
  that need lemmas name them. v0 had contracts; their syntax is a starting
  point, not a constraint.
- **Places.** MIR reads `_1.1` (a slice's length) and loads through
  pointers; the model treats each place as a variable while nothing can
  change it, which the borrow kernel's loans can justify.
- **Calls.** Modular: a call assumes the callee's `ensures` after proving
  its `requires`. `std`'s `Vec.index`, `Vec.push` and `str` slicing need
  contracts first, and those contracts are the first users of 0.6's lemmas.
- **Integers.** Fourier–Motzkin is complete over the rationals, not the
  integers: a goal that needs parity or rounding is lost (never wrongly
  proved). Cutting planes or a bounded integer search fix that later.
- **Invariant inference.** Untrusted candidates (the loop condition, the
  initial values, bounds of indices) kept only when they check: most loops
  over `0..n` should need no annotation.

## Plan

The [roadmap](roadmap.md#6-verification-05) lists the steps and their
completion criteria.
