# Stability marks

The specification branch moves at roughly a hundred commits a day. That is
the language being built, not the language being unstable — but a project
choosing Oak for a multi-year system needs to know which surfaces it may
build on today and which are still being designed. This document marks
each source-level surface, and states what a mark commits the project to.
STATUS.md tracks *what exists*; this document tracks *what will stay*.

## The three marks

| Mark | Commitment |
| --- | --- |
| **frozen** | The surface changes only with a migration note in the owning spec file's `## Changes` section, and never within a minor version of a module that depends on it. Programs written against it keep compiling. |
| **stabilizing** | The shape is settled; details (spelling of a keyword, a diagnostic code, a bound) may still move. Changes are announced in the owning spec file and the design log, and existing programs are migrated in the same change. |
| **direction** | Specified as intent only, or implemented as a first increment whose surface is expected to change. Build against it knowingly. |

A mark applies to a source surface — what a program can write — not to the
compiler's internals, which move freely.

## Marks by surface

| Surface | Spec | Mark | Notes |
| --- | --- | --- | --- |
| Declaration shape `name: (params): T = body`, block bodies, `pub`, `pub(opaque)` | `10-syntax.md` §3, `83-modules.md` §6 | frozen | |
| `?` conditionals and match expressions; no `if`/`else` | `10-syntax.md` §3a, `30-adts-patterns.md` | frozen | |
| Fixed-width integers: total wrapping `+ - * / %`, explicit narrowing (`_trunc_`, `_saturating_`, `_checked_`, `_bits_`), one-signedness comparisons | `20-types.md` §11.1 | frozen | checked/trapping arithmetic forms (`#110`) join as stabilizing when merged |
| Records and structs, layout introspection, `static_assert` | `40-records.md` | frozen | |
| Sum types, generic ADTs, monomorphized generic functions | `30-adts-patterns.md`, `20-types.md` §11.2 | frozen | |
| Views and spans, lexical v1 lifetimes, `view(&x)`/`span(&x)`, call-local exclusivity | `50-borrowing.md` §1–§7 | frozen | |
| Region-indexed borrowed returns | `50-borrowing.md` §8c | stabilizing | first increment landed 2026-09-10 |
| Modules: `package`, `import`, `oak.mod`, semver at module granularity, per-module profiles | `83-modules.md`, `82-package-semver.md`, `85-discipline.md` §1 | stabilizing | qualified stdlib package views are new |
| Strings and UTF-8 validity | `70-strings.md` | frozen | |
| Derived declarations (`derive.equal/hash/compare/format`) | `30-adts-patterns.md`, `compiler/derive.go` | stabilizing | |
| Typed test commands (`derive.test_generate/encode/decode`), `oak test` flags, artifact and campaign formats | `110-testing.md` | stabilizing | artifact schema is versioned; the runner rejects other versions |
| Simulated storage, crashes, scheduling adapters (`SimDisk`, `SimProcess`, `SimSched`) | `110-testing.md` | stabilizing | landed 2026-09-10 |
| Effect clauses `effects { }` / `forbids { }` | `60-effects-allocation.md` §2 | stabilizing | v1 surface; parameterized effects are direction |
| Protocol declarations `Name: protocol = { ... }` | `112-protocols.md` | stabilizing | control graph plus data record; array-valued data is direction |
| Discipline profiles (`default`/`strict`), safe recursion, bounded loops, located assertions | `85-discipline.md` | stabilizing | |
| C FFI: `c.extern`, scalar and span boundaries, generated headers | `92-ffi.md` | stabilizing | |
| Portable SIMD (`simd.*` 128-bit unsigned, `F32x4`/`F64x2`), `arm64` library | `93-simd.md` | stabilizing | wider, signed, and x86-64 vectors are direction (`#111`) |
| Assembler units and the AArch64 surfaces | `94-assembler.md`, `95`–`101` | stabilizing | verification-driven; instruction coverage grows |
| Attributes other than the clauses above (layout `struct(packed)`, section names) | `40-records.md` §6b, `65-machine-memory.md` | stabilizing | no general attribute syntax exists; none is planned before the effect and protocol clauses settle |
| Parameterized effects, typestate-indexed handles, `via` parameter modes | `60-effects-allocation.md`, `112-protocols.md` §7 | direction | |
| IO port: caller-owned completion rings, `open`/`close`/`pread`/`pwrite`/`fsync`/`fdatasync`/`fsyncdir`, `replace io => iosim\|ionative` | `120-io.md` §8 increments 2–3 | stabilizing | `#106`; `iosim` and the portable `ionative` landed 2026-09-11 with `Oak.IoPort`; the ring shape is fixed by the io_uring increment to come |
| IO surface beyond the port (io_uring realization, registered buffers, sockets) | `120-io.md` §8 increment 4 | direction | `#106`; designed, no realization yet |
| Floating point beyond `f32`/`f64` arithmetic and the two float vectors | `20-types.md` §11.3 | stabilizing | |

## How marks change

A surface moves from direction to stabilizing when its spec section is
normative and an implementation exists; from stabilizing to frozen when it
has been used by a second project (the OS and the database count) for a
release without a change to its shape. A frozen surface is unfrozen only by
a design-log entry that says why and what the migration is. Marks are
reviewed whenever STATUS.md gains a row.
