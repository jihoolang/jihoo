---
title: Getting started
description: Install jihoo with Nix, then run and build your first programs.
---

## Install

jihoo is packaged with [Nix](https://nixos.org): the `jihoo` command, the
clang and lld it uses to finish programs, and the standard library.

Try it without installing:

```sh
nix run github:jihoolang/jihoo -- run hello.jh
```

Install it into your profile:

```sh
nix profile install github:jihoolang/jihoo
```

Or use it from your own flake:

```nix
{
  inputs.jihoo.url = "github:jihoolang/jihoo";

  outputs = { self, nixpkgs, jihoo }: {
    # jihoo.packages.<system>.default is the compiler;
    # jihoo.overlays.default adds `pkgs.jihoo`.
  };
}
```

jihoo compiles for x86_64 and aarch64 Linux.

### Without Nix

Each [release](https://github.com/jihoolang/jihoo/releases) has the
compiler for x86_64 and aarch64 Linux with its standard library. It needs
glibc and LLVM 21: libLLVM, clang to link native programs and lld for
freestanding ones. If they are not found under their usual names, set
`JIHOO_LLVM` to the shared library, `JIHOO_CC` and `JIHOO_LD`.

```sh
curl -L https://github.com/jihoolang/jihoo/releases/download/v0.1.1/jihoo-v0.1.1-x86_64-linux.tar.gz | tar xz
jihoo-v0.1.1-x86_64-linux/bin/jihoo run hello.jh
```

### From source

```sh
git clone https://github.com/jihoolang/jihoo
cd jihoo
nix build                       # bootstraps the compiler: ./result/bin/jihoo
./result/bin/jihoo run examples/hello.jh
```

## Your first program

A program starts at `main`. `jihoo run` compiles it and runs it;
`jihoo build` leaves the executable.

```jihoo title="words.jh"
import std.env
import std.fs

fn main() -> i32 {
    let args = env.args()
    if args.len() < 2 {
        eprintln("usage: words <file>")
        return 2
    }
    let text = match fs.read_file(args[1]) {
        Ok(t) => t
        Err(e) => {
            eprintln(e)
            return 1
        }
    }
    var counts = Map(String, i64).new()
    for line in text.as_str().lines() {
        for w in line.split(" ") {
            if w.len == 0 {
                continue
            }
            match counts.get_mut(w) {
                Some(n) => n += 1
                None => {
                    counts.insert(w.to_string(), 1)
                }
            }
        }
    }
    println(counts.len())
    0
}
```

```sh
jihoo run words.jh -- notes.txt
jihoo build words.jh -o words && ./words notes.txt
```

## Where next

- [A tour](/jihoo/language/tour/) of the language;
- [Values and ownership](/jihoo/language/ownership/) and
  [Borrowing](/jihoo/language/borrowing/), what makes jihoo safe without a
  garbage collector;
- the [examples](/jihoo/examples/hello/).
