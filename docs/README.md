# jihoo documentation

This directory is the source of the documentation website,
<https://jihoolang.github.io/jihoo/>. Each file is one page; this list is the
site's table of contents and sidebar, in order (`site/scripts/toc.mjs` reads it).
Links between pages are ordinary relative Markdown links, so the files read the
same on GitHub.

## Language

### Basics

- [A tour](language/tour.md)
- [Syntax](language/syntax.md)
- [Coming from Rust](language/from-rust.md)
- [Types](language/types.md)
- [Modules](language/modules.md)

### Memory

- [Values and ownership](language/ownership.md)
- [Borrowing](language/borrowing.md)

### Data and code

- [Structs, enums and patterns](language/data.md)
- [Generics and traits](language/generics.md)
- [Compile-time evaluation](language/comptime.md)
- [Contracts](language/contracts.md)
- [Dependent types](language/dependent-types.md)
- [Functions in dependent code](language/dependent-functions.md)
- [Type aliases in dependent code](language/dependent-aliases.md)
- [Parameterized dependent records](language/dependent-records.md)
- [Natural-index proof library](language/natural-proofs.md)
- [Bounded proof automation](language/proof-automation.md)
- [List proof library](language/list-proofs.md)
- [Lists with exact lengths](language/sized-lists.md)
- [Proof-bounded buffer ranges](language/buffer-ranges.md)
- [Runtime-selected collections](language/bounded-collection.md)
- [Materializing lists in buffers](language/list-buffer-transfer.md)
- [Bulk vector extension](language/vector-extension.md)
- [Reflection and derive](language/reflection.md)
- [Closures](language/closures.md)
- [Dynamic dispatch](language/dyn.md)
- [Iterator pipelines](language/iterators.md)
- [Errors](language/errors.md)
- [Data by index](language/data-oriented.md)
- [Threads](language/threads.md)

### Down to the machine

- [Unsafe code and C](language/unsafe.md)
- [Profiles and targets](language/profiles.md)

## Reference

- [Standard library](reference/standard-library.md)
- [Grammar](reference/grammar.md)
- [Builtins](reference/builtins.md)
- [Command line](reference/command-line.md)
- [Verified Core subset check](reference/verified-core.md)

## Internals

- [Architecture](internals/architecture.md)
- [Design: jihoo 0.1](internals/redesign.md)
- [Design: closures that own what they capture](internals/move-closures.md)
- [Design: verification and proofs](internals/verification.md)
- [Design: native dependent core](internals/dependent-core.md)
- [Core specification](internals/core-spec.md)
- [Lean proof boundary](internals/lean-proofs.md)
- [Graph artifact certificates](internals/graph-certificates.md)
- [Checked typing artifacts](internals/typing-certificates.md)
- [Core representation bridge](internals/core-bridge.md)
- [Self-hosting](internals/self-hosting.md)
- [Testing](internals/testing.md)
- [Roadmap](internals/roadmap.md)
