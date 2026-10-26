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
- [Reflection and derive](language/reflection.md)
- [Closures](language/closures.md)
- [Iterator pipelines](language/iterators.md)
- [Errors](language/errors.md)
- [Threads](language/threads.md)

### Down to the machine

- [Unsafe code and C](language/unsafe.md)
- [Profiles and targets](language/profiles.md)

## Reference

- [Standard library](reference/standard-library.md)
- [Grammar](reference/grammar.md)
- [Builtins](reference/builtins.md)
- [Command line](reference/command-line.md)

## Internals

- [Architecture](internals/architecture.md)
- [Design: jihoo 0.1](internals/redesign.md)
- [Self-hosting](internals/self-hosting.md)
- [Testing](internals/testing.md)
- [Roadmap](internals/roadmap.md)
