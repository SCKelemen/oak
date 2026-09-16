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
… for Cortex-M (default `cortex_m4`); `generic_rv32+m`/`generic_rv64+m` — soft
float with the integer multiply, matching the companion object — for
freestanding RISC-V; the toolchain baseline for hosted targets
(`Oak.Target.defaultCPU`). A feature suffix extends a processor
(`generic_rv64+m+v` for the vector extension, `93-simd.md` §1.4). What
the processor does not guarantee a program may still use where it finds
it: a function's `dispatch { sve: f_sve }` clause selects a realization
once, before `main`, by a probe of the processor (`93-simd.md` §6).
Freestanding RISC-V objects are compiled with the medium-any code model
so they link at the user's address (RAM at `0x80000000` on the `virt`
machines). The asm lane reads the same processor: an rv64 unit that uses the
vector extension needs a `-cpu` with V, and units compress under C
(`94-assembler.md` §9).

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
  when no unit applies. Native body lowering (`nativegen`, `-native`) runs
  on the targets with a lane — AArch64 and RV64 — and lowers each body on
  the target's lane; a target without one compiles every body as C. With
  `-link oak` a program whose every body is lowered natively is linked by
  the Oak assembler into a static ELF executable (Linux and freestanding
  targets on both lanes) with no C compiler and no system linker
  (`94-assembler.md` §9). The C compiler's `-O` level (`oak build -O`,
  default 1) is a property of the mechanical layer — register allocation,
  scheduling, selection — never of the program's meaning: no level passes
  fast-math or contraction, and the `-O0` to `-O2` delta on a hot loop
  measures what the C compiler expressed that Oak has not.
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

A binding declared without a value is the zero of its type in every
backend (`20-types.md` §12.2 relies on it: the zero must satisfy every
refinement the type carries): the C emitter initializes a value-less
scalar with `0` and a value-less record, union, or owned array with `{0}`,
and never leaves a local's storage uninitialized — a value-less record
local that read as stack garbage was the one difference between the Go
bit-level decider and its Oak twin (`125-verification.md` §7) when the
twin was first run.

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

A record element read through a span or view (`s[i].field`) selects the
element in place behind the checked index; the C backend never returns a
record element by value from a helper, so a large state record behind a
span is read at the cost of the field, not the record
(`50-borrowing.md` §8e). The same holds for an aggregate element of an
owned array — a row of a `[N][M]T` grid, a record of a `[N]R` table: an
unproven `a[i][j]` or `a[i].f` bounds-checks the index and selects the
element by address (`a.v[ oak_lv_idx(i, N) ]`), never by value. The
ternary form (`oak_index`), which yields an rvalue and would copy the
whole element, is reserved for scalar elements.

## 8a. Constant globals

A top-level scalar binding (a fixed-width integer, float, or `Bool`) with a
constant initializer that no statement assigns, index-assigns, borrows
(`span(&g)`, `view(&g)`), or addresses anywhere in the program is emitted
as a C constant, `static const u64 page_size = 16384;`, never as a mutable
static: the C compiler then folds it, so `pa / page_size` is a shift and
`pa % page_size` a mask, where a mutable static would be a hardware
division (the OS pilot's R2). A global some statement writes stays a
mutable `static`, as does a global placed in a section
(`65-machine-memory.md`) and a measured constant (`60-effects-allocation.md`
§10b), which the load-time initializer `oak_measured_init` writes once
from the weak hook `oak_measured_value` after checking the declared
range; owned arrays and records keep their storage. Shifts in a
global initializer are the plain operator at the checked width, so
`(u32(0xFFFF) << 16) | u32(0xFFFF)` is a C integer constant expression
(R5); the checker has already bounded the shift count.

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

**Inlining as a source transformation.** The same rule is applied once
more, earlier: before the type checker runs, the code-emitting stages
(`EmitC`, `EmitNative`, `EmitExecutable`, `EmitNativeObject`) splice each
inlinable helper into its callers at the source level
(`compiler/inline.go`), so the extent facts in force at the call site prove
the helper's element accesses (`50-borrowing.md`, "Proof through a
helper") and neither backend emits a check for them. The transformation is
statement-level and visible in the emitted C: the helper's statements go
before the statement holding the call, its declared names are renamed into
the reserved `__inl<N>_` namespace — `__inl<N>_l_<name>` for the helper's
locals, `__inl<N>_a<i>` for copied arguments, `__inl<N>_r` for the result,
three spellings that cannot meet (a local named `a1` or `r` once collided
with the temporaries) — a plain
identifier argument substitutes for a parameter the helper never assigns
(so the caller's facts about it apply unchanged), so does an integer
literal — `u32(8)` as written, or a bare literal wrapped in the parameter's
type — so the merged body reads `v[u32(8) + u32(3)]` under
`len(v) >= u32(8) + u32(4)`, constant sums the extents checker folds and
proves (a temporary would leave `len(v) >= t + 4`, which proves nothing
about `v[t + 3]` since the sum may have wrapped; the hash package's
`crc32c_word_at` at its seven constant offsets is the case), a scalar
argument of any other shape is copied into a typed temporary, and the helper's tail
expression takes the call's place — directly when the call is a
statement's whole value, through a typed result temporary when it is an
operand. The pass refuses rather than reorders: nothing moves across a
short-circuit operator, a match arm in value position, a loop condition,
or a function literal; a call is not hoisted above a user-function call
this pass does not inline; a helper that declares `effects` or `forbids`
or takes a function value is never inlined, so the effect analysis
(`compiler/effects.go`) keeps the call graph and the value flows it reads;
a helper that writes through a span parameter
is inlined only where nothing else in the statement is evaluated; a helper
whose locals or copied arguments are not scalars, or whose tail holds a
block, stays a call where the C form would need a block in an expression.
A call the pass leaves is still a call to a forced-inline helper, so the
generated code is never slower than before — only sometimes still
checked. The semantic model, the language server, the Lean emitters, and
the prover see the program as written. An expression body (`f: (…): T =
expr`) is the one-statement block it denotes, as a candidate and as a
caller (it becomes a block when statements are hoisted into it), and the
pass runs in rounds: a helper that called only helpers is a leaf once
those are spliced into it, and the next round inlines it in turn — so an
accessor chain (`tkind` over `tword` over `term_at` over `state`, the
prover's shape) flattens to the element read it denotes. The rounds stop
when a pass inlines nothing new. A match arm in a helper's tail whose
body is a block holding one expression and nothing else (`c ? { a } | {
b }`, the source's habit) is that expression, so the tail holds no block
where the C form would need one; `cache_get`, `mask64`, and the one-line
conditionals inline where that shape had kept them calls. Three shapes are never candidates because
a later analysis judges them at the call: a helper declaring `effects` or
`forbids` (a node of the path a forbids report names), a helper with a
function-typed parameter (the argument's effect row is checked against the
parameter's at the call, `60-effects-allocation.md` section 2a), and a
protocol's via callable (the resource analysis admits a state's
construction only inside its transition, `112-protocols.md` section 5a).
The reserved names keep arguments and locals apart — `__inl<N>_arg<i>` for
a copied argument, `__inl<N>_l_<name>` for a renamed local — so a helper's
local named `a1` never meets the temporary of its second argument.

### 9.1 Optimization remarks, candidates, and admission

Executable-oriented compilation produces an `OptimizationReport`. Every
remark contains the function, transform, Passed/Missed/Analysis kind, an
explanation, and the facts used or missing. The report is output only: neither
an API consumer nor a later compiler pass can present a remark or a fact as
permission to transform code.

The planning substrate is `opt/`. Its transform registry orders proposal
generators by phase and records the proof kind and fact requirements of each.
The bounded beam search materializes, de-duplicates, measures, seam-checks, and
validates candidates through a lane-supplied driver. Static target costs guide
selection but are never correctness evidence. The identity is always retained
as the final fallback. Beam pruning also keeps the cheapest ungated candidate
when possible, so a later verifier-gated machine transform cannot evict an
independently admitted optimization. Checker-driven refinement may narrow a
refused candidate, and verifier-gated transforms cannot ship on a trusted
(unchecked) verdict.

The first source and native rules are:

| Transform | Admission | Validation | Observable effect |
| --- | --- | --- | --- |
| `source.inline.leaf.v1` | the private-leaf, effect, evaluation-order, and borrow-shape decision above | the executable-oriented program passes ordinary checking | the call is beta-reduced; caller extent facts can remove checks in the helper body |
| `source.canonical.bool.v1` | a built-in Bool identity after type checking and monomorphization; every non-literal operand remains exactly once, and no literal token is mutated | a fresh checker accepts the changed monomorphic program; the original specializing checker retains fact authority | double negation, `&&`/`\|\|` identities, and identity Bool comparisons are absent for every backend; literal negation waits for typed OptIR |
| `source.canonical.integer.v1` | a zero/one identity whose checked result and retained operand have the same exact fixed-width integer type; floats, widening expressions, and user-defined operators are excluded, and the non-literal operand remains exactly once | the same cloned post-specialization recheck | redundant `+ 0`, `- 0`, `* 1`, `/ 1`, `\| 0`, `^ 0`, and shifts by zero are absent for every backend |
| `elide-guards` | the exact accesses carry checked extent facts | the guardless assembly passes the lane seam checker and the selected body passes the native validation policy | per-access bounds guards are absent only where independently admitted |
| `optir-emit` | a verified post-GVN/DCE/LICM CFG changed at least one operation and lies in the selector's closed vocabulary | target-neutral coloring succeeds; the selected assembly passes the seam checker and receives a proven or witnessed semantic-verifier verdict, never a trusted one | generic SSA cleanup and invariant motion affect shipping AArch64 code |

The native lane proposes its strength reduction, guard elimination, flag reuse,
invariant motion, vector homes, reduction unrolling, MachineIR reallocation and
promotion, and late cleanup through `opt.Search`. A refused composition is not
reinterpreted as permission for one of its parts: each alternative is a
separate candidate and every selected body passes the ordinary seam checker.
Transforms marked verifier-gated are set aside when equivalence is not judged,
at worst selecting the checked identity lowering.

`Compilation.Optimizations()` requests the executable-oriented source pass and
returns the remarks; native remarks are included when native bodies are enabled.
Plain semantic `Check()` does not optimize and reports no remarks, so tooling and
proof extraction continue to observe the program as written. Each future rule
must add an admission-negative test, a semantics test, and a generated-code or
instruction-count test. Cross-language speed claims require named benchmark
corpora, target/toolchain versions, and statistical results; an optimization
remark alone is never such a claim.

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
(`benchmarks/state-machines/README.md`). A machine with a `data` record
keeps the branch tree deliberately: measured on the same harness, a
candidate-line table (the first candidate line per `(state, step)`, the
group's guards tried in order) steps a nine-line guarded machine in 4.55 ns
against the tree's 4.10 — the guards over the record are data-dependent
branches in either shape and the table adds an indirect jump — so the
compiler-known lowering applies to machines whose guards are decided at
compile time.

A mixed-symbol machine (`112-protocols.md` §2a: payload-less steps beside
steps whose guards read a `u8` or `u16` payload) computes its symbol
before the lookup from three more file-scope tables: `bases[tag]`, the
step's first symbol; `classes[]`, one flat byte table holding every
step's payload classes (one entry for a step without a classed payload);
and `offsets[tag]`, the step's region in it. The payload is read from
every classed member of the step's union and the tag selects one
(`payload = step.tag == 1u ? (u32)step.payload.Byte : payload;` per
classed step, a `csel`, never a branch), then
`sym = bases[tag] + classes[offsets[tag] + payload]`. The step type's
constructors zero the value before storing the tag and payload
(`ADTType.ZeroInit`) so every such read finds defined bytes. Measured on
a nine-symbol machine, the emitted form steps in 1.0 ns against the
branch tree's 3.7–4.0 and 2.8 for a `switch` on the tag choosing a
per-step class table (`benchmarks/state-machines/` workload E).

## 15. Evaluation order

`10-syntax.md` §3d fixes left-to-right evaluation within an expression;
C fixes nothing of the kind, and the operands of `oak_add_u32( a, b )`
and the arguments of every call are evaluated in whatever order the C
compiler prefers. The backend closes the gap at every statement position
(`codegen/sequence.go`):

- **Groups.** The operands of an operator, the receiver and arguments of a
  call, the elements of an array literal, the fields of a record literal,
  the operands of an index and the bounds of a slice form one
  *unsequenced group*: siblings C may reorder.
- **Sensitivity.** A member is *effectful* when it contains a call the C
  compiler may move — a program function, a method, an extern, an atomic
  or runtime builtin, or any callee the backend does not know — and
  *sensitive* when it is effectful, or reads a global, or reads a
  variable an effectful sibling may write through a span, an address
  argument or a method receiver. Casts, conversions, checked arithmetic,
  float intrinsics, `len`, borrow constructions, layout queries and plain
  reads no sibling can write are pure and stay inline.
- **Sequencing.** When a group has two or more sensitive members, each is
  evaluated into a temporary `T oak__seq_N = member;` before the
  statement, in source order — a member's own inner temporaries first —
  and the statement reads the temporaries. `T` is the type the checker
  recorded for the member (`TypeChecker.ExpressionTypeAt`, keyed by
  position so lowering's rewrites keep it); a member with no C spelling
  falls back to `__typeof__`, which the golden corpus keeps at zero.
- **Conditional contexts.** Nothing is hoisted out of a match arm or the
  right operand of `&&`/`||`. When one of them needs sequencing, the
  construct is emitted in statement form — `T t;` then `if ( c ) { ...
  t = a; } else { ... t = b; }`, with each arm sequencing its own
  operands — and the statement reads `t`. A `while` condition that needs
  sequencing becomes `for ( ;; ) { temporaries; if ( !( cond ) ) {
  break; } body }`, so its operands are re-evaluated every iteration in
  order.

The lowering is proportional to the risk: a program with at most one
effectful operand per group emits exactly the C it did before. The
differential test `compiler/e2e_evaluation_order_test.go` holds the
interpreter and the compiled C to the specified value for every
construct above and for the expression that exposed the gap.

## 16. The optimization system

The rules a backend optimization obeys, restating `05-ergonomics-and-cost.md`
"The mechanical backend" for the compiler's own passes. The design note is
`docs/notes/optimization-2026-09.md`.

Executable-oriented compilation has an explicit specialization boundary.
Cheap transforms that reduce generic source run before type checking and
monomorphization; transforms that need concrete types and values run after the
first successful type check has produced the monomorphic program. A changed
post-specialization program is checked again before any backend consumes it.
The specializing checker remains the authority for template ownership,
resource, extent, and per-expression facts: a post-specialization rewrite may
reuse those checked nodes and facts, but a fresh check cannot manufacture their
provenance after the templates have been erased. When prior normalization has
exposed a mangled generic-ADT name, the validation clone alone receives the
matching monomorphic declaration synthesized from the specializing checker's
recorded instantiation and the declared template through the ordinary checked
type-substitution routine. It neither accepts candidate-invented type names nor
adds the validation declaration to the emitted program.

The target-independent middle-end substrate is `optir/`. Its primary form
retains scalar operations, explicit effects and facts, structured `if` regions,
and pre-test `while` regions with explicit loop-carried values. Its canonical
CFG projection represents joins and loop recurrences as typed block arguments.
Projection is deterministic and fails closed through an independent verifier
for definitions, dominance, same-block order, reachability, terminators, edge
arity/types, Bool conditions, and return types. `Compilation.OptIR()` connects
the ordinary checked semantic model to this substrate for concrete scalar
functions: fixed-width integers, Bool, unit, local assignments, structured
branches and short-circuiting, exhaustive Bool matches, pre-test loops with
explicit carried locals, value-preserving integer widening, and effect-marked
calls. Unsupported memory, methods, kernels, protocol lowerings, and richer
algebraic forms are per-function refusals, never partial projections.

The SCCP analysis validates its operation vocabulary before computing exact
constants and executable CFG edges. Its folds use Oak's exact fixed-width
signed/unsigned arithmetic and trap boundaries rather than host or target
arithmetic. A separate, bounded transform consumes only exact independently
recomputed evidence to replace known closed total-pure results, select known
branches, remove unreachable blocks, and clean SSA blocks/trampolines. It
preserves effectful and trapping operations and independently verifies its
output. Dominance-scoped GVN and fixed-point DCE then produce another verified
CFG from a closed vocabulary of total pure scalar operations. Plain
copies share a value number; exact commutative integer/equality operations and
inverse order comparisons receive one canonical key. Result types and ordered
attributes remain exact, and any unknown attribute disables operand
normalization. Proof facts move only when valid at the retained dominating
definition. Calls, traps, memory, synchronization, unknown operations, and
every explicitly effectful operation remain roots. The first region-memory SSA
substrate consumes explicit checked region metadata beside operation effects.
It gives each region deterministic entry/definition/join versions, expands an
opaque call to a clobber of every declared region, handles loop phis, and binds
its independently recomputed evidence to exact CFG and metadata fingerprints.
Missing or inconsistent Mod/Ref information fails closed. It is analysis-only:
dead-store elimination and load forwarding still wait for memory projection
from checked Oak plus their own legality transforms. `Compilation.OptIR()` returns
the original CFG, SCCP evidence and rewritten CFG, later candidates, and each
deterministic report. Its
loop analysis reports dominators,
back edges, natural-loop structure and nesting, canonical preheaders, and typed
affine loop-carried recurrences. A unique continuation comparison is normalized
around the induction value; an exact constant trip count is reported only when
fixed-width range reasoning proves that every update through loop exit avoids
wrap. Symbolic, multi-exit, and wrapping cases remain unproved rather than
borrowing mathematical-integer semantics. Its LICM candidate runs after
GVN/DCE and moves only closed total-pure operations whose operands are
available at a canonical preheader. It does not speculate division, remainder,
shifts, calls, memory, effects, unknown operations, or relational/path-local
facts; a result-local `checked.type` fact may move because it is identical to
the SSA result type. The cloned output is independently verified and carries a
deterministic movement report. A changed post-LICM CFG is now an AArch64 or
RV64 native candidate. Target-neutral SSA liveness/interference analysis assigns
abstract colors; dead block parameters may share a color only with one another,
while live and conditional-edge values remain distinct. A deterministic
target-neutral spill planner partitions high-pressure SSA values between colors
and typed/aligned abstract stack slots, never spills ABI precolors, and
independently verifies interference and safe slot reuse. It does not yet insert
loads/stores, so both selectors still refuse remaining pressure.

Each selector maps colors to caller-saved registers, destroys block arguments
with edge-local parallel copies, and selects the closed Bool and
8/16/32/64-bit total-integer vocabulary. AArch64 narrow values are normalized in
W registers. RV64 maintains the psABI's canonical sign-extended 32-bit
representation and explicitly zero-extends `u32` when widening to `u64`; Bool
and narrow ABI inputs are canonicalized before use. Both selectors also admit a
first closed call slice: the target must be a known direct Oak function, with
zero or one matching Bool or 8/16/32/64-bit scalar argument and exactly one
matching scalar result. Its OptIR operation must carry exactly `EffectCall` and
one nonempty `callee` attribute, with no other effect or attribute metadata.
Because every allocatable color is caller-saved, every other non-unit value
must be dead across the call. An admitted calling body uses a sixteen-byte
frame to save and restore AArch64 `x30` or RV64 `ra`, moves the optional
argument and result through the target ABI register, and reapplies the target's
Bool/narrow normalization to the returned value. Unknown, indirect, method,
generic, external, multi-argument, or multi-result calls refuse the candidate,
as do other effects, traps, memory, stack parameters, unfamiliar operations,
or remaining pressure. The abstract spill plan still emits no loads, stores,
or frame layout, so it is not composed with this call frame yet.

A target-independent block-layout analysis assigns neutral branch weights
except for loop continuation/backedges, which receive a qualitative 8:1
preference. Its exact-fingerprint proposal is a verified permutation and never
changes CFG edges. The AArch64 selector consumes only the order: unconditional
branches to the next block disappear, and a copy-free conditional uses
`cbz`/`cbnz` with the preferred successor as fallthrough. SSA edge copies remain
explicit. The direct lowering remains the identity,
and `optir-emit` is verifier-gated: it ships only after seam admission and a
proven or witnessed semantic verdict against the Oak body; the evidence grade
is retained and reported rather than conflated with proof.

Compiler stages, analyses, candidates, and verification verdicts are not yet
one end-to-end dependency DAG, but the generic OptIR analysis chain and native
candidate path from materialization through selection now use the immutable,
versioned artifact graph.
Analysis and transform nodes name the exact input IR artifact, typed edges
state prerequisites, mutations create new versions, and invalidations follow
only affected edges. Cheap structural admission and costing precede expensive
verification because neither can authorize code; native selection now depends
on candidate, clean admission, cost, and verdict artifacts for every body it
may return. This is also the concurrency boundary: independent ready analyses
may run in parallel without sharing mutable IR. `opt/artifact.go` implements
derived versions, exact-once deterministic executors, cancellation, and the
process-local cache. Native proposal enumeration and linear source stages
remain outside the graph. The design is
`docs/notes/optimizer-artifact-dag-2026-09.md`.

1. **Licensed removals only.** The compiler removes a check, a guard, a
   copy, a reload, or a trap only on a fact it has proved: an index under
   its extent (§8), a value within its refinement, two spans that cannot
   overlap (`50-borrowing.md`), an alignment fact, a declared operator
   law (`20-types.md`), an effect row. Nothing is removed on a
   speculation, and an unproved case keeps its defined behavior.
2. **The mechanical layer is free.** Register assignment, instruction
   selection, and scheduling change neither meaning nor the costs
   `05-ergonomics-and-cost.md` makes visible; the backend may do them as
   it likes, on either lane, without a source spelling.
3. **Translation validated per body on the native lane.** A natively
   lowered body passes the seam checker and the verifier
   (`94-assembler.md` §9) whatever transforms produced it; a body they
   refuse is re-lowered without the transform, and the refusal is
   reported with the body. No optimization is trusted because its pass
   is believed correct.
4. **Facts cross the seam as facts.** A caller's proof reaches a callee
   only as a stated proposition on the callee's signature
   (`50-borrowing.md` extent propositions) or through inlining (§9);
   the native lane's checker admits an elision only from a fact it can
   read at the seam.
5. **Measured, with the verdict.** An optimization lands with the kernel
   rows it targets before and after (`benchmarks/native`,
   `benchmarks/kernels`) and the verifier's verdict for every body it
   touched; a row that moves while a verdict falls from proven is not a
   result. `-opt` keeps its one meaning (`115-tooling.md`): the C
   compiler's level, never Oak's.
6. **A win elsewhere is a gap here.** A case where C, Rust, or Zig is
   faster because it expresses something Oak cannot is filed as an
   expressiveness finding (`docs/checklists/performance.md` §0), never
   answered by a flag or a speculative pass.
7. **Candidates, not a pass order.** The native lane's transforms are
   proposals in a bounded candidate search (package `opt`,
   `compiler/native_search.go`; `docs/notes/optimizer-search-2026-09.md`):
   the plain lowering is the identity candidate and always in the search;
   each transform names the facts it consumes with the provenance it
   needs (`nativegen.Transforms`: check elision needs an index the
   typechecker proved, reduction unrolling the operator's associativity
   law), and proposes a configuration from a candidate; a static cost
   model orders the admitted bodies; the checker and the verifier judge
   them in that order; the first body to prove is kept, the plain
   lowering validated last and preferred only when nothing else earns
   as strong a verdict — so no body ships on a verdict weaker than the
   plain lowering earns, and an admitted body the model prices near the
   plain one is preferred to it on a tie. The search records an
   optimization report (`-opt-report`, `OAK_OPT_REPORT`): every
   transform taken with the fact that licensed it, every one set aside
   with the checker's or the verifier's reason, and the body's
   structural counts before and after. Cost is never correctness: a
   wrong estimate makes a body slower, and only the verdict decides
   what ships.

**The layers, and what checks each.** The system is three layers, each
verified against its input, the checks composing from source to silicon.

- **Layer A, body rewrites, one for every lane** (`94-assembler.md`
  §9.ag): transforms of the checked Oak body whose legality is a fact,
  not a machine — strength reduction of constant arithmetic, helper
  expansion, reduction unrolling, and the folds and idioms to come. Each
  rewrite carries its obligation: *decided*, proved per site by the
  bit-level decider as the theorem that the new expression equals the old
  on every input, or *law-backed*, a schema proved once in Lean and
  instantiated by a matcher. A site the decider does not prove is left as
  written. The rewritten body is what layer B lowers and the verifier
  judges, so "source equals rewritten body" is layer A's proof and
  "rewritten body equals instructions" layer B's.
- **Layer B, lowering and per-ISA optimization**: register homes,
  selection, addressing, pairing, if-conversion, peephole, on each lane's
  instruction stream, under the seam checker and the verifier; today a
  candidate search over the lane's transforms keeps the cheapest proven
  body (`docs/notes/optimizer-search-2026-09.md`).
- **Layer C, per-processor tuning**: cost tables keyed by the `-cpu`
  name, consumed by layer B's selection and scheduling; data, not passes,
  with no obligation of their own, since the verifier judges the tuned
  output and a wrong table costs speed, never meaning.

Layer A's rewrites are transforms of the search like the lane's own: the
identity candidate is the plain body, a transform proposes the rewritten
one, and the site theorems are proved once per body, not per candidate.
The `-verified` profile is the end-to-end mode: every body natively
lowered with a proven verdict, every layer-A rewrite applied decided or
law-backed — the layer applies nothing else, and reports the sites it
left as written — nothing left to C.
