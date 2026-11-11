# Compact MIR structural totality

`Jihoo.SizedMir.Structural.Typed` checks all nine constructors of
`SizedErasure.Term`, both comparison arms, and natural operand lets. Its rules
contain no calls to compilation, inference, evaluation, or MIR validation.
`Typed.infer` derives representation inference; `Typed.total` derives successful
`Linear.compile` for every local/block base and exit, given equal environment
lengths. `Typed.total_cost` derives exact local/block counts.

This is representation typing, not linear ownership typing. It permits repeated
free and requires existing source ownership proofs for runtime safety. Its
length-only operand relation is intentionally sufficient only for structural
construction, not generated-code validity.

## Checked regressions

`SizedMirStructuralChecks` contains a closed term combining allocation,
application, scalar lend, owned lend, both branch arms and free. Its typing and
structural success are proved; its concrete checked-entry success is kernel
reduced. Counterexamples show:

- A selected branch can execute successfully while an overflowing literal in
  the unselected branch causes structural compilation to fail.
- A natural result structurally compiles but fails the scalar return wrapper.
- A pointer-kind environment paired with an i64 operand structurally compiles
  a free but produces invalid MIR.

## Remaining gates (not proved here)

`SymbolicMirEntry` still requires `Entry.lowerProgram ... = some fragment`.
This change does **not** remove that premise or replace it with a certificate.
The following are separate unfinished proof obligations:

1. Connect symbolic source typing and computed compaction to `Structural.Typed`.
   Existing `SymbolicCoreTyping.Typing` has no owned-lend constructor, although
   `SizedCoreTyping.Typing` and the compact runtime support it. The semantic
   closing-instance branch rule types only the selected arm and cannot alone
   establish the new judgment for both arms.
2. Prove all generated blocks valid from typed operand correspondence, valid
   constants, `InputsBefore`, scalar result type and CFG placement bounds.
   Equal environment lengths alone do not provide this correspondence.
3. Discharge wrapper and ABI checks: return local zero has type i64; arguments
   use distinct nonzero supported scalar slots; input and generated storage fit
   512 locals/blocks; total statements fit 4096. Pointer arguments are not
   admitted by the existing entry ABI. Establish statement costs structurally
   (or derive their bound from other costs), rather than assume `valid code`.
4. Combine those results with explicit resource bounds into checked-entry
   lowering totality, then specialize the existing symbolic adequacy theorem.

No production checker, native compiler, MIR-to-LLVM, or full Core correctness
claim is made.

## Integration requested

Shared integration files were intentionally untouched. Add imports of
`Jihoo.SizedMirStructuralTotality` and `Jihoo.SizedMirStructuralChecks` to the
aggregate build; add their public theorems to the central axiom audit and adjust
its count. The default Lake module discovery can build these modules directly;
no library configuration change is required. Update shared status/roadmap only
after agreeing the explicitly partial scope above.
