# Modules

Each file is a module. `import a.b` loads `a/b.jh` and binds its last name,
`b`; `import a.b as c` binds `c`. Modules are looked for next to the
importing file, then in `-I` directories, `JIHOO_PATH`, and the standard
library.

```jihoo
import std.fs
import geometry as geo

fn main() {
    let text = fs.read_file("input.txt").unwrap()
    let p = geo.Point { x: 1, y: 2 }
}
```

- Items are private to their module unless marked `pub`; struct fields
  too.
- The standard library's modules see each other's private items.
- Imports may form cycles; items are checked when they are used, in any
  order.
- The prelude (`std/prelude.jh`) is seen by every module: `Option`,
  `Result`, `Vec`, `String`, `Map`, `Box`, the standard traits, `print`,
  `println`, `panic`, `sort`.

## Files per target and profile

`import a` prefers, in order, `a.<target>.<profile>.jh`,
`a.<profile>.jh`, `a.<target>.jh` and `a.jh`, where the target is `x86_64`
or `aarch64` and the profile `native`, `freestanding` or `uefi`
([Profiles](profiles.md)). This is how `std.sys` talks to libc in one
profile, to the kernel in another and to firmware in the third, with one
interface.
