# Executable Lowering and Backends

Oak's semantics are not defined by C, but the C backend is an important executable projection and cost-model oracle.

## 1. Backend-independent semantics

The typed/Semantic IR defines program meaning before a backend chooses concrete machine representation.

A backend must preserve:

- value semantics;
- control-flow semantics;
- ownership/effect constraints;
- integer behavior;
- ADT constructor distinctions;
- pattern-match selection;
- required layout/ABI constraints;
- safe bounds and pointer rules.

A backend may optimize representation only when those observations remain equivalent.

## 2. C as bootstrap/reference backend

Generated C should be intentionally straightforward and debuggable.

For systems code, a competent C programmer should recognize the expected machine shape:

```text
semantic record constraint -> erased after specialization; no runtime object required
natural struct             -> C struct / ordered fields
closed ADT                 -> tag + payload or proved equivalent compact representation
match                      -> switch/if branches
specialized fn             -> direct C function / inlineable code
view/span                  -> pointer + length representation
raw pointer                -> C pointer
fixed array                -> fixed storage
arena/slab                 -> explicit allocator calls/storage
```

C is not Oak's semantic definition and should not prevent future native/LLVM/etc. backends.

## 2a. Targets and cross builds

Status: implemented (`target`, `toolchain`; `oak build -target os/arch`;
`compiler/e2e_cross_test.go`, `Oak.Target`). Motivated by dbs ask 6
(`docs/notes/dbs-feedback-2026-09.md`): AArch64 and RISC-V are its only
targets, and a build must work from any developer machine.

Every build is a cross build; the host is only the default target. A
**target** is an operating system and an architecture spelled `os/arch`
as Go spells them: `linux/arm64`, `linux/amd64`, `linux/riscv64`,
`darwin/arm64`, `darwin/amd64`, the operating-system-less
`freestanding/{arm64,amd64,riscv64}` (a kernel, a hypervisor, a 64-bit
microcontroller), and the 32-bit microcontroller members
`freestanding/arm` (Cortex-M, Thumb) and `freestanding/riscv32`. The set is
closed; the 64-bit members are LP64 and the two 32-bit members ILP32 —
the two C data models `92-ffi.md` §2.4 admits — and the target's data
model decides Oak's machine-sized `int`, `uint`, `ptr`, `uptr`
(`Oak.Target.dataModel_lp64_or_ilp32`, `int_bits_32`, `ptr_bits`). The
target comes from `-target`, else `OAKOS`/`OAKARCH` (each defaulting to the
host's component, as `GOOS`/`GOARCH` do), else the host. A **processor**
(`-cpu`, else `OAKCPU`, else the target's default) is passed to the C
compiler as `-mcpu`: `cortex_m0`, `cortex_m3`, `cortex_m7`, `cortex_m33`,
… for Cortex-M (default `cortex_m4`); `generic_rv32`/`generic_rv64` — soft
float, matching the companion object — for freestanding RISC-V; the
toolchain baseline for hosted targets (`Oak.Target.defaultCPU`).

The compiler emits the same C translation unit for every target; what the
target decides is:

- **the assembler lane** (`94-assembler.md` §9): a `.oakasm` unit applies
  when its lane is the target architecture's (`arm64`, `rv64`; amd64 has
  none). One unit per lane may realize a signature — an `arm64` and an
  `rv64` unit side by side, the target picking. A unit of another lane
  yields to the declaration's Oak fallback body, which then compiles as an
  ordinary function; without a fallback the build fails closed at compile
  time with the lane and the target named, never in the C compiler
  (`Oak.Target.unitApplies_iff`, `lanes_exclusive`). The Oak fallback body
  of an applying unit is emitted under the negation of the lane's
  preprocessor condition, so the C is still right when compiled for
  another architecture by hand.
- **the companion object**: Mach-O for Darwin, ELF elsewhere; an ELF for a
  hosted RISC-V target declares the lp64d float ABI its libc uses, a
  freestanding one lp64 (`Oak.Target.rv64FloatABI`). No object is written
  when no unit applies. Native body lowering (the AArch64 backend of
  `nativegen`) runs only for arm64 targets.
- **the C compiler** (`toolchain.Resolve`), in a fixed order, first match
  wins: `OAK_CC` (an executable taken as already targeting the platform,
  `OAK_CFLAGS` added); `cc` for the host target; `zig cc --target=…` —
  one compiler for every target, carrying musl, so a Linux cross build is
  static and hermetic; `clang --target=…` with `--sysroot=$OAK_SYSROOT`
  for a hosted target (skipped without one) or `-ffreestanding -nostdlib`
  for freestanding; a GNU cross compiler by prefix (`riscv64-linux-gnu-gcc`,
  `riscv64-elf-gcc`). Nothing found is a refusal naming what to install.
  The driver is an argv the tooling executes directly, never a shell. A
  resolved driver targets the requested platform, `OAK_CC` wins, the host
  resolves whenever `cc` exists, and with zig every supported target
  resolves from any host (`Oak.Target.resolve_targets`, `resolve_explicit`,
  `resolve_host`, `resolve_zig`).
- **linking**: Linux cross builds link statically (a binary that runs on
  any distribution); Darwin never does; a freestanding target compiles to
  a relocatable object (`name.o`) the user links with their own startup.
  `framework` manifest lines apply to Darwin targets, not Darwin hosts.

**Freestanding builds and the host boundary.** The object needs no libc:
`<math.h>` is included only when hosted (the float code needs `signbit`,
a compiler builtin otherwise; the transcendental functions are Oak code in
the standard library), and target constants (`c.const`) are refused. What
the object may still call is the **host boundary** — a closed list of C
symbols the kernel or firmware defines, and nothing else
(`Oak.Freestanding`):

| Hook | Who defines it | Used by |
| --- | --- | --- |
| `int64_t oak_host_write(int64_t fd, const uint8_t *buf, size_t len)` — weak | the host, optionally | every diagnostic a hosted build prints to stderr; `import("host")` (`stdlib/host.oak`) writes through it (a failed assertion, an arithmetic overflow, a NULL `c.fn_at`, a `c.cstr` without terminator, `c.argv_of`): one bounded line `oak: <what> at <file>:<line>` on fd 2, assembled from compile-time text and the source position, then the trap as before. Without the hook the path is the bare trap (`report_traps`, `report_delivers_iff`). |
| `int64_t oak_time_host_realtime_nanos(void)`, `int64_t oak_time_host_monotonic_nanos(void)` | the host | `import("timehost")`, the freestanding realization of the time port: `timehost_source`/`timehost_refresh` are `timenative`'s twins over the hooks instead of `clock_gettime` and `c.const`, so they compile on every member of the closed set, ILP32 included; the monotonic reading never moves backwards whatever the hook does (`hostRefresh_mono_le`). |
| `oak_io_host_open/close/pread/pwrite/fsync/fsyncdir/last_errno` | the host | `replace io => ionative`: the io port's native realization already crosses this boundary; `stdlib/native/oak_io_host.c` is its POSIX definition, and a kernel or firmware supplies its own (`120-io.md` §5). |

Beyond the hooks the object references only the compiler's runtime
library — `__aeabi_*`, `__udivdi3`, `memset`, the builtins every C
compiler emits — which the final link supplies (compiler-rt from zig,
libgcc from a GNU toolchain) beside the host's own startup and linker
script. Atomics never join that list:
the object ends with a per-carrier assertion that the target's C11 atomics
are always lock-free (`65-machine-memory.md` §6), so a `-cpu cortex_m0`
build of a program with a `u32` fetch-add fails in the C compiler rather
than pulling a locked `__atomic_fetch_add_4` from libatomic;
`-DOAK_ATOMIC_ACCEPT_LOCKED` in `OAK_CFLAGS` accepts the fallback
knowingly. A freestanding program prints through `import("host")`
(`stdlib/host.oak`: `host_write` hands a view to the hook below through a
null-checked shim) and manages bounded object storage through
`import("slab")` (`stdlib/slab.oak`; `60-effects-allocation.md` §7) — the
runtime-in-Oak item, both halves in Oak over the boundary and storage the
program owns; what it cannot do is grow storage, and it should not: Oak has
no hidden heap (§3). `compiler/e2e_mcu_test.go` is the shape: the Oak object, a vector
table or `_start`, a UART behind `oak_host_write`, a counter behind the
two clocks, linked and run under `qemu-system-arm -M mps2-an385`
(Cortex-M3) and `qemu-system-riscv32 -M virt`; the program reads the host
clock through `timehost`, and a deliberately failed assertion's message
arrives over the UART before the trap. Oak has no hidden heap (§3), so
there is no allocation hook to define.

`oak run -target os/arch` builds as `oak build` does and then executes the
program: directly for the host target; for a foreign Linux target through
a user-mode emulator — `OAK_EMULATOR` (its arguments from
`OAK_EMULATOR_ARGS`), else QEMU's `qemu-<arch>` or `qemu-<arch>-static`
on PATH — as one argument vector, the emulator, the static binary, the
program's arguments; the program's exit code is `oak run`'s. Without an
emulator the run is refused before anything is built, naming what to
install; a foreign Darwin target has no user-mode emulator, and a
freestanding build is an object for the user's own harness
(`Oak.Target.runWith_host`, `runWith_foreign`, `runWith_freestanding_none`,
`runWith_explicit`). `compiler/e2e_cross_test.go` runs the linux/riscv64,
arm64, and amd64 cross builds under `qemu-user-static` in CI, asserting
both the passing exit and that a failed assertion still fails under the
emulator. `oak install -target` places the executable under
`$OAKBIN/<os>_<arch>/`, as `go install` does. The build cache keys on the target, the driver's path and identity,
and the exact flag list (`115-tooling.md` §3.1), so one C built for two
targets never shares an entry. `oak test -target os/arch` builds a package's tests through the same
toolchain and reports each test `built`, not run; a freestanding target is
refused, since the test harness is hosted C. Not yet: running cross-built
binaries under an emulator from the tooling.

## 3. No hidden runtime

The backend may not silently introduce:

- heap allocation;
- garbage collection;
- reference counting;
- exception unwinding;
- interface vtables for static generic constraints;
- boxing to a dynamic object representation;
- hidden string/data copying;
- unbounded callback dispatch.

If a selected language feature requires such machinery, the semantic model must expose the corresponding representation/effect.

A semantic record/shape constraint specifically does not authorize the backend to invent a runtime dictionary, boxed record, or vtable. Specialization must resolve its required members against the concrete type.

## 4. Generics

Generic functions/types specialize by default.

Monomorphization should erase compile-time constraints and phantom parameters that have no runtime representation.

Specialization must preserve type/effect semantics and must not introduce dynamic dispatch merely for compiler convenience.

A future explicitly selected code-size/dynamic-dispatch strategy may exist, but it is a distinct representation choice.

## 5. ADTs

The ordinary representation is conceptually:

```text
tag + payload storage
```

A backend can select tag width from the number/representation constraints of constructors.

Payload defaults/metadata are not automatically discriminant values.

A compact enum-like representation is valid only when constructor payload semantics allow it and the representation mapping is injective over observable constructor values.

## 6. Records and structs

A **record** is semantic product/shape information. It may be consumed entirely at compile time and therefore may have no runtime representation at all.

A **struct** selects a concrete product representation policy. Plain `struct` selects Oak's natural ordered policy; target primitive representations must still be known before numeric field offsets and total size are resolved.

The compiler therefore treats these states distinctly:

```text
semantic shape only
representation policy selected
representation resolved
```

The backend may lower only from a representation state sufficient for the operation it is performing. It must fail closed rather than fabricate offsets or sizes.

Target layout computes sizes, alignment, padding and offsets from ordered struct fields plus explicit representation constraints. The backend must not derive representation field order from unordered maps.

FFI/wire/persisted layouts require explicit stable representation contracts rather than relying on incidental target ABI layout.

A shape constraint may be satisfied by concrete types with different layouts because shape satisfaction is about semantic members, not offsets. Specialization resolves field accesses against each concrete representation.

## 7. Integer semantics

Backend operations must implement Oak's specified fixed-width behavior exactly.

C undefined/implementation-defined behavior must not leak into safe Oak semantics. Code generation may need unsigned operations, explicit casts, intrinsics, checks, or helper routines to preserve Oak's rules.

The formal specification of overflow/division/shifts/conversions must precede relying on them for verification.

### 7a. Floating-point semantics

The same rule governs floating point (`20-types.md` §11.3): the backend realizes IEEE 754 round-to-nearest-even with subnormals, never reassociates, distributes, or contracts, and never enables a fast-math mode. The C backend emits `#pragma STDC FP_CONTRACT OFF` at the top of every translation unit that uses floating point (under clang, which honors the standard pragma; gcc does not implement it and never contracts in strict ISO mode, which the drivers select with `-std=c99`/`-std=c11`), spells `f32`/`f64` as `float`/`double`, emits literals as exact hexadecimal floating constants of the checked width so the C compiler performs no decimal conversion of its own, keeps `+ - * /` and comparisons as the plain C operators with every operation parenthesized so C's grouping is Oak's parse tree (`20-types.md` §11.3.3), requires `FLT_EVAL_METHOD == 0` of the target (the emitted unit fails to compile on a target that evaluates in excess precision, such as x87, rather than silently changing results), and lowers intrinsics to the correctly rounded C99 `<math.h>` functions (with its own helpers for the IEEE 754-2019 `min`/`max` and `totalOrder`). The `oak run`/`oak test` drivers pass `-ffp-contract=off` and link `-lm`; `-ffast-math`, `-Ofast`, `-ffinite-math-only`, and `-fno-signed-zeros` are never passed. Out-of-range float-to-integer conversions lower to range-checked helpers that trap, saturate, or report, never to C's undefined cast. The "no hidden runtime" rule of §3 extends to numeric semantics: the written expression is the executed expression.

## 8. Bounds

When the compiler proves an index/range safe, a backend may eliminate the corresponding dynamic check.

When safety is not proved, safe Oak must retain a defined check/failure path rather than compile to out-of-bounds undefined behavior.

## 9. Function values/closures

A plain function value may lower to a function pointer.

A function-typed record field (`Step: type = struct { run: (u32) -> u32
effects { } }`) is a plain function pointer member, pointer-sized and
pointer-aligned on the recorded LP64 target model and asserted like every
other field; a record literal stores the named function's C symbol. No
closure environment is ever stored (ml F4, the captured step).

A capturing closure requires an explicit environment representation whose storage lifetime has been established by ownership/effect analysis.

The backend may not silently heap-promote escaping captures.

A typed function literal (`10-syntax.md` §3c) is **lifted**: the backend
emits it as a top-level C function, spliced after the forward declarations
and before the first definition, and the expression is that function's
name. The lifted function is named `oak_0lit_<n>` in emission order — a
name beginning with a digit, which no Oak identifier can, so it never
collides with a program function. A binding inferred from a literal
(`inc := fn(x: u32): u32 = ...`) is a function pointer of the literal's own
signature. Nested literals are lifted while the outer body is emitted, so
their definitions precede it. There is no closure object and no
allocation; the only indirection is the pointer the program wrote.

## 10. Source/debug information

Backend output should preserve mappings from generated operations to canonical Oak source spans and stable semantic identities.

**Implemented:** every emitted function and statement is preceded by a
`// @source:` comment, and with `oak build -lines` (the `LineDirectives`
compilation option) also by a C `#line N "file"` directive naming its Oak
source line, so C compiler diagnostics and debuggers attribute generated
code to the Oak line that produced it. Spliced standard-library syntax is
not from that file and receives no directive; a generic specialization's
lines are its template's. Directives are off by default so the generated
C stands on its own lines for backend inspection, and the golden corpus is
recorded without them.

The compiler's source model should power:

- C `#line` / debug mappings where useful;
- DWARF/native debug metadata in future backends;
- diagnostics and IDE navigation;
- semantic debugger schemas.

## 11. Verification strategy

Backend verification proceeds in layers:

```text
semantic operation
  -> representation selection
  -> representation resolution
  -> lowering rule
  -> backend representation/code
  -> executable equivalence/property test
  -> formal refinement for critical rules
```

Early formal-refinement candidates:

- fixed-width integer lowering;
- natural struct layout calculation;
- semantic record-shape satisfaction;
- ADT tag/payload lowering;
- match lowering;
- view/span representation and bounds;
- erased phantom/proof parameters;
- effect-free generic specialization.

The C backend should maintain golden/compile/run tests in addition to formal models. Formal models do not replace generated-code testing.

## C identifier mangling

An Oak value or field identifier is emitted verbatim into C unless its
spelling is a C keyword (`short`, `signed`, `default`, `register`, …), a
leading-underscore name (reserved to the C implementation), or a name in
the emitter's own `oak_` namespace (`oak_assert`); those emit as
`oak_id_<name>` at every site — locals, parameters, globals, record field
declarators and accesses, designated initializers, `offsetof` operands,
match binders. Function names are not routed through this mapping: they
already carry the `oak_` (or package) prefix. The mapping is one function
(`codegen/identifiers.go`, `cIdent`) and idempotent, so nested emitters
cannot double-mangle. Oak keywords (`struct`, `type`) cannot be
identifiers at all, and Oak's own type spellings (`int`, `u32`) lower
through the type table, never through this mapping. Compiler temporaries
live in the reserved `__` namespace (`oak__scrutinee_0`, `__oak_tail_0`),
which user identifiers can never spell (`83-modules.md`), so the mapping
passes them through untouched.

## 9. Small helpers

Naming an operation must not cost a call. A private (not `pub`), named,
non-generic, non-method function with an Oak body that calls no user-defined
function, contains no loop, and spans at most twelve source lines is emitted
as a forced-inline helper (`OAK_INLINE`: C99 `extern inline` with the
always-inline attribute) in both its prototype and definition. The C
compiler then inlines every call at every optimization level, including
`-O0`, rather than by heuristic, while the external definition is still
emitted so the symbol remains available to linkers and assembly inspection. Exported, extern, and asm-backed functions
keep external linkage; recursive and looping functions are never marked, so
the C compiler is never asked to inline what it cannot. The judgment is the
discipline analyzer's call-graph and loop walk (`InlineHelperShape`), so the
backend and the recursion policy share one authority.

## 10. Owned arrays as values

An owned array `[N]T` is a value, and its C representation is a struct
carrying the array: `typedef struct oak_arr_T_N { T v[ N ]; } oak_arr_T_N;`
(`codegen/arrays.go`). The wrapper has exactly the raw array's size and
alignment, so record layouts and the emitted `sizeof`/`offsetof` assertions
are unchanged, and C's own struct semantics supply every copy the language
specifies: a parameter is the callee's own copy (no copy-in prologue), a
return is a copy, whole-array assignment and initializing a record field
from an array binding are plain assignments, and a tagged-union payload of
array type is stored and matched like any other. Element access spells
`.v` before the index and keeps its bounds check (`oak_index`, `oak_store`,
`oak_lv_idx` take the array member); `view(&a)` / `span(&a)` borrow `a.v`
with the static length; `a[lo:hi]` over an owned array is a compound-literal
view whose bounds are checked against the static length before the pointer
is formed, so a slice is a value in argument position too. A typed array
literal is a compound literal of the wrapper, `(oak_arr_u32_4){ { 1, 2, 3, 4 } }`,
in any expression position; a declaration initializer is the brace form. A nested
array `[N][M]T` is an array of wrapper values (`oak_arr_oak_arr_T_M_N`): a row
copied out is its own storage and a store through `grid[i][j]` reaches the
grid, each hop keeping its bounds check. The
typedef name mangles element spellings that are not identifiers (`_Atomic u32`,
`void *`, a nested `oak_arr_u8_16`); wrapper typedefs are placed before the
first record, union, global, or prototype that names them, and a type that
first appears inside a function body fails closed with an `OAK_UNSUPPORTED`
marker rather than emitting a typedef where C forbids one.

## 13. Methods on ADT receivers

A method `fn (h: Handle) merge(other: Handle)` on an ADT receiver lowers to
a C function taking the receiver as its first parameter, and a call
`h.merge(g)` lowers to a direct call of that function with `h` first — no
dispatch table, no thunk, no allocation. The type checker records the
resolution on the call (`InvocationExpression.ResolvedMethod`, the
`Type::method` identity) and the call keeps its dotted shape, so the
receiver never becomes an argument and explicit argument indices never
shift (`50-borrowing.md` §9, receiver authority). Methods are forward
declared with the functions, so definition order is free.

**Mangling.** The C name of `Type::method` is
`oak_<len(Type)><Type>_<method>` (with the package prefix every function
takes): `Handle::merge` is `oak_6Handle_merge`. The decimal length prefix
begins with a digit, which no Oak identifier can, so a method never shares
a symbol with a function (`Handle_merge` is `oak_Handle_merge`); and it
fixes where the type name ends, so `A_b::c` and `A::b_c` differ.
`Oak.MethodMangling` (`spec/lean/Oak/MethodMangling.lean`) proves both:
`mangle_injective` and `mangle_ne_ident`, over any injective digit-only
length rendering; decimal is one. Motivation recorded in
`docs/notes/roadmap-authority-resources.md` (asks, tier 1): receiver
contracts type-checked but could not execute compiled.

## 14. Protocol machines: tables and shift DFAs

The projected `name_legal`, `name_next`, and `name_run` of a protocol
without a data record carry a compiler-known lowering
(`FunctionStatement.Lowering`, set by the projection, never the parser;
`112-protocols.md` §2a). The backend emits the ordinary signature and, in
place of the Oak body, the table form:

```c
static const u64 oak_utf8_transitions[256] = { ... };   /* shift rows, one per byte */
oak_Utf8State oak_utf8_next( oak_Utf8State state, oak_Utf8Step step ) {
  u32 next = (u32)( ( oak_utf8_transitions[ step.payload.Byte ] >> state.tag ) & 63u );
  oak_assert( next != 48u ? oak_Bool_True : oak_Bool_False, "Utf8", 0 );   /* 48 = 6 * sink */
  oak_Utf8State result; result.tag = next; return result;
}
```

The table is emitted once at file scope, after the prototypes, and shared
by the three functions. The dense form is `static const u8 T[states+1][symbols]`
with the sink row mapping every symbol to the sink, so `run` needs no
check inside its loop. Nothing is allocated, nothing is dispatched
indirectly, and the trap sits exactly where the branch tree's assertion
sat.

This is the first instance of the roadmap's milestone 9, "proven facts
into predictable performance": the declaration is the simplest thing the
user can write, the compiler chooses the implementation the hardware
prefers for input-driven steps, and `Oak.Protocol` (`spec/lean/Oak/Protocol.lean`)
proves the table entry is the declared first-match target
(`table_target`), the sentinel is exactly illegality (`table_sentinel`),
the deferred batch check reports exactly the declared result
(`runSink_correct`), and the shift rows decode what they store
(`unpack_pack`, bit-blasted). The compile-time guard evaluator is checked
against the interpreter by differential tests over every state and symbol
(`compiler/e2e_protocol_lowering_test.go`). Measured: the emitted UTF-8
validator runs at 0.5 ns per byte, the hand-written shift DFA's speed, six
times the branch tree the same declaration produced before
(`benchmarks/state-machines/README.md`).

