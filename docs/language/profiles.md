# Profiles and targets

A program is compiled for one of three profiles, chosen by its root file:

- **native** (the default): linked with the C library. `std.sys` uses
  `malloc`, `write` and the other libc functions, and C functions can be
  called directly.
- **freestanding** (`#![freestanding]` at the top of the root file): no C
  library. `std.sys` uses Linux system calls and its own allocator, and the
  result is a small static executable. The whole standard library works the
  same.
- **uefi** (`#![uefi]`): a UEFI application, which firmware starts before
  any operating system. The result is a PE32+ image (`.efi`); `std.sys`
  uses the firmware's boot services ([below](#uefi)).

Module attributes follow the normal token and comment rules: spaces or line
breaks between `#!`, `[`, `freestanding` and `]`, and leading block comments,
do not change the selected profile.

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
result. It also writes `jihoo_clone`, which starts a thread on a new stack
for [`std.thread`](threads.md#profiles). What the C runtime would provide, LLVM's helpers for 128-bit
division and float conversion, comes from `std/rt.jh`;
functions nothing calls are left out of the executable.

## UEFI

```jihoo
#![uefi]

fn main() {
    println("Hello from UEFI")
}
```

`jihoo build hello.jh` writes `hello.efi`, linked by lld's COFF linker
(`JIHOO_LD` with `-flavor link`) as an EFI application; `--target aarch64`
builds one for ARM64 firmware. Copy it to `EFI/BOOT/BOOTX64.EFI` (or
`BOOTAA64.EFI`) on a FAT disk, or start it from the UEFI shell. `jihoo run`
does not run UEFI programs.

The compiler writes the entry point, `efi_main(image, system_table)`: it
keeps both for `efi_image()` and `efi_system_table()`, calls `main`, and
returns its exit status as the image's EFI status: 0 for 0, otherwise the
code with the error bit set, so that the shell's `%lasterror%` shows the
code. A trap ends the image with status 132, as it would end a Linux
program with SIGILL, instead of halting the firmware.

The standard library's `std.sys` writes standard output to the firmware's
console (`ConOut`) and standard error to `StdErr`, converting UTF-8 to
UCS-2 and line breaks to CR LF, and allocates from the boot services'
memory pool. There are no files, processes, threads or program arguments;
those calls fail with `ENOSYS`, and `std.thread` is not available. Everything
else (`Vec`, `String`, `Map`, formatting, closures, `dyn`) works as in the
other profiles.

[`std.uefi`](../reference/standard-library.md#uefi) describes the system
table, the boot and runtime services and the text consoles, with helpers
for the common calls. Calls through the firmware's function pointers are
`unsafe`:

```jihoo
#![uefi]

import std.uefi

fn main() {
    var t = unsafe { zeroed(uefi.Time) }
    unsafe { (*uefi.runtime_services()).get_time(&t, null) }
    println(t.year)
}
```

UEFI uses the Microsoft x64 calling convention on x86_64, so `extern fn`,
`export fn` and C-compatible `fnptr` types follow it there; on aarch64 it
is AAPCS64, as on Linux. Each image also defines the memory functions,
`__chkstk` (which Windows conventions call before a frame larger than a
page) and `_fltused`. C code linked in must be compiled for the same
convention, for example with
`clang -target x86_64-unknown-windows -ffreestanding -c`.

## Embedding in another system

An object built with `jihoo emit-obj --lib` has no entry point and can be
linked into a program of another operating system, a kernel included.
Failed checks and panics still have to stop somewhere: by default
`jihoo.panic`, which the object keeps to itself, writes the message with
Linux's `write` system call (UEFI's console in `#![uefi]`) and traps. A
[`#[panic_handler]`](errors.md#panic-handlers) takes its place, so that the
object reports a bug through the host's own functions and calls no system
service by itself:

```jihoo
#![freestanding]

extern fn host_panic(msg: *u8, len: i64) -> never

#[panic_handler]
fn on_panic(msg: str) -> never {
    unsafe { host_panic(msg.ptr, msg.len) }
}

export fn checked_byte(bytes: *u8, count: i64, index: i64) -> u8 {
    unsafe {
        let view = make_slice(bytes, count)
        view[index]
    }
}
```

Bounds checks stay, and with `--release` too. `#![freestanding]` keeps the C
library out: the object then refers to the `extern fn`s it declares, here
`host_panic`, and to `memcpy`, `memmove` and `memset`, which the host
provides as it does for C code, since C compilers call them the same way.
It defines LLVM's helpers for 128-bit arithmetic (`std/rt.jh`) as global
symbols. The rest of `std.sys` still means Linux, so allocation (`Vec`,
`String`, `Box`) and input and output make Linux system calls; such a
library uses what does not allocate (slices, `Option`, `Result`, iterators
over borrowed data) and calls the host through `extern fn`s. `nm` on the
object shows what it needs.

## Targets

jihoo compiles for x86_64 and aarch64 Linux, and UEFI on both machines.
`--target aarch64` (or `x86_64`) compiles for the other machine;
freestanding and UEFI programs need nothing else for that, native ones need
the other machine's C library.

A module can have a file per target, per profile, or both
([Modules](modules.md#files-per-target-and-profile)): `std/sysno.x86_64.jh`
and `std/sysno.aarch64.jh` hold each machine's system call numbers, and
`std/sys.uefi.jh` is the UEFI profile's operating system.
