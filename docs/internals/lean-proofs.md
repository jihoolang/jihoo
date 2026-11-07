# Lean proof boundary

The first mechanized step toward 0.6 is an arithmetic evidence fragment in
`proofs/Jihoo/Arithmetic.lean`. It is a separate declarative specification inspired
by the [core specification](core-spec.md), not a translation of `compiler/core.jh`.
It does **not** prove the dependent kernel, its normalization algorithm, ownership,
lowering or whole executables sound.

## What is proved

Expressions contain free variables, natural literals, addition and subtraction.
A valuation assigns a natural number to every free variable. Propositions are
`Lt(a, b)` and `Eq(a, b)`, interpreted as natural-number comparison and equality.
An evidence context is a list of such propositions.

- `Expr.eval_subst`: simultaneous first-order substitution agrees with valuation
  substitution.
- `Conv.sound`: every derivation of the selected syntactic conversion rules
  preserves the expression's value, for every valuation.
- `Conv.subst`: these conversion derivations survive first-order substitution.
- `Formula.holds_subst`: proposition substitution agrees with its semantics.
- `Derives.sound`: evidence derived from a context is true in every valuation
  satisfying that context. The proof is by induction on a syntactic derivation;
  truth of the conclusion is not an assumed typing rule.
- `no_closed_false_lt`: no derivation in the empty context proves `Lt(0, 0)`.
- `certified_sub_add`: evidence of `Lt(b, a + 1)` justifies `(a - b) + b = a`.
- `certified_index_lt`: derived bounds evidence implies the corresponding
  natural-number bound. This is only the arithmetic premise of memory safety,
  not a theorem about machine addresses or heaps.

The example module checks nested conversion, open assumptions, equality transport,
and the maximum u64 boundary, and proves that unrestricted subtraction cancellation
and a closed equality between zero and one are impossible in this fragment.

## Correspondence and differences

`Expr.var`, `lit`, `add` and `sub` abstract `Var`, `Natural`, `UAdd` and `USub`.
Unlike the core's graph, these are trees. Their free variables have natural indices;
there are no binders, so this is not the kernel's de Bruijn substitution theorem.
The Lean literal type is unbounded `Nat`. Core literal nodes are u64, but symbolic
core sums denote mathematical naturals. They must not be modeled by wrapping
`UInt64`: for example, `ZeroLe` at the largest u64 still establishes
`Lt(0, a + 1)`. Runtime overflow traps require a separate semantics.

The evidence constructors correspond to assumptions, `Refl`, closed `Decide`,
`ZeroLe`, `LtAdd`, `LtCancel`, `LtLe`, conversion and `Transport` specialized to
first-order `Lt`/`Eq` proposition families. Instantiating a family replaces variable
zero and leaves other variable numbers unchanged; it is not beta reduction of a
core lambda. Closed `Decide` takes a Lean proof of a numeral comparison, which is
computable and checked by the Lean kernel, not an oracle for open propositions.

`Conv` is an equational theory, not `normal` or `identical`. It includes symmetry,
transitivity, congruence, commutativity and associativity of addition, zero removal,
numeral arithmetic and `(a + b) - b = a`. These equations are sound in naturals.
There is no claim that every such equation converts in the resource-bounded
implementation or that every implementation conversion is represented here.
Numeral rules need not respect the implementation's folding and overflow limits.
The evidence field of `USub` is omitted, and subtraction is total natural truncated
subtraction. The core additionally requires evidence ruling out underflow. That
requirement is essential for the separate `certified_sub_add` theorem; unrestricted
`(a - b) + b = a` is deliberately absent from `Conv`.

Consequently this model does not prove proof-irrelevant ordering in `compare`, or
that removing an evidence child preserves the typing of a core term. It proves a
sound arithmetic foundation on which that correspondence can later be established.

## Reproducing the checks

The project pins Lean 4.34.1 in `proofs/lean-toolchain` and uses only its bundled
standard library, with no downloaded Lake packages or mathlib dependency.

With that Lean toolchain and Python 3 on `PATH`:

```sh
bash proofs/check.sh
```

With the repository's pinned Nix inputs:

```sh
nix build .#checks.x86_64-linux.lean-proofs -L
# On an aarch64 host, use checks.aarch64-linux.lean-proofs.
nix flake check -L
```

The existing two-target CI runs `nix flake check`, including this derivation. The
Lean package version provided by Nix must match `lean-toolchain`; a toolchain
upgrade must update and recheck both rather than silently changing proof behavior.

`check.sh` rejects build warnings, checks the toolchain, and inspects the elaborated
axiom dependencies of all eight exported theorems in `Audit.lean`. Only Lean's
standard logical axioms (`propext`, `Quot.sound`, `Classical.choice`) are permitted.
The current proofs use `propext` and some use `Quot.sound`; no theorem requires
`Classical.choice`. No admitted proof or custom axiom is accepted as a dependency of these theorems. This still
trusts Lean's kernel and standard logical foundation, as well as the toolchain
used to run it. The theorem audit is an explicit list: add new public guarantees
to both that list and its expected count.

## Remaining obligations

There is no map from accepted core programs to `Derives` with a proved correctness
theorem. Full soundness requires the remaining term syntax, universes, ghost/code
positions, dependent functions, families and elimination, followed by preservation
and full consistency. Quantity rules need an execution model of ownership and
scoped borrows. Erasure and runtime normalization must be related to the pure model,
with traps specified, before lowering can be connected to a semantics of MIR.

Finite rejection, preservation and differential tests remain implementation
regressions. They are not replaced by these proofs, and they do not discharge the
missing correspondence. The [roadmap](roadmap.md#the-050-release-gate-for-the-native-core)
continues to distinguish these obligations and their trusted implementation boundary.
