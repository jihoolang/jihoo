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
- [Types](language/types.md)
- [Modules](language/modules.md)

### Memory

- [Values and ownership](language/ownership.md)
- [Borrowing](language/borrowing.md)

### Data and code

- [Structs, enums and patterns](language/data.md)
- [Generics and traits](language/generics.md)
- [Closures](language/closures.md)
- [Errors](language/errors.md)

### Down to the machine

- [Unsafe code and C](language/unsafe.md)
- [Profiles and targets](language/profiles.md)

## Reference

- [Standard library](reference/standard-library.md)
- [Builtins](reference/builtins.md)
- [Command line](reference/command-line.md)

## Internals

- [Architecture](internals/architecture.md)
- [Design: jihoo 0.1](internals/redesign.md)
- [Testing](internals/testing.md)
- [Roadmap](internals/roadmap.md)
