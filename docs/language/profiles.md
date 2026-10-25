# Profiles and targets

A program is compiled for one of two profiles, chosen by its root file:

- **native** (the default): linked with the C library. `std.sys` uses
  `malloc`, `write` and the other libc functions, and C functions can be
  called directly.
- **freestanding** (`#![freestanding]` at the top of the root file): no C
  library. `std.sys` uses Linux system calls and its own allocator, and the
  result is a small static executable. The whole standard library works the
  same.

```jihoo
#![freestanding]

fn main() {
    var v = Vec(i64).new()
    v.push(42)
    println(v[0])
}
```

A freestanding program starts at `_start`, which the compiler writes: it
records the arguments for `env.args()`, calls `main` and exits with its
result.

## Targets

jihoo compiles for x86_64 and aarch64 Linux. `--target aarch64` (or
`x86_64`) compiles for the other machine; freestanding programs need
nothing else for that, native ones need the other machine's C library.

A module can have a file per target, per profile, or both
([Modules](modules.md#files-per-target-and-profile)): `std/sysno.x86_64.jh`
and `std/sysno.aarch64.jh` hold each machine's system call numbers.
