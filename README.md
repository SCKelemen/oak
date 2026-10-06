# Oak

Oak is a systems programming language for embedded, freestanding, and hosted
software. Its priorities are **correctness, performance, and simplicity**:
explicit storage and effects, strong types and borrowing, and verification
that connects language laws to executable behavior.

The `specification` branch contains the working Go bootstrap compiler, an
Oak standard library, C and native ARM64/RV64 backends, an experimental Core
WebAssembly backend, and a growing verification toolchain with components
written in Oak. A fully self-hosted, end-to-end proved v1 toolchain is still
work in progress.

> **Start with the evidence.** [The specification](docs/spec/README.md) is
> normative; the [feature and verification matrix](docs/spec/STATUS.md) records
> what is specified, implemented, tested, modeled, proved, and refined.
> [Stability marks](docs/spec/STABILITY.md) describe source compatibility, and
> [target maturity](docs/targets.md) separates backend support from proof coverage.
> Older top-level design documents and historical examples may use superseded
> syntax or describe unimplemented designs.

- [Getting started](#getting-started)
- [Language essentials](#language-essentials)
- [Compilation and targets](#compilation-and-targets)
- [Standard library](#standard-library)
- [Verification and self-hosting](#verification-and-self-hosting)
- [Tools and tests](#tools-and-tests)
- [Repository guide](#repository-guide)

## Getting started

Build the CLI with the Go toolchain selected by [go.mod](go.mod), currently
**Go 1.27.1**. The default executable path also needs a host C compiler (`cc`);
`OAK_CC` selects a different one. Lean, QEMU, and the other formal/cross-target
tools are needed only for their respective workflows.

```sh
git clone --branch specification https://github.com/SCKelemen/oak.git
cd oak
go build -o build/oak .
./build/oak version
./build/oak help
```

Save this standalone program as `demo.oak`:

```oak
twice: (value: i32): i32 = value + value

main: (): i32 {
  answer: i32 = twice(21)
  answer == 42 ? 0 | 1
}
```

Build and execute it. This example reports success through exit status zero;
it does not print anything.

```sh
./build/oak build -o build/demo demo.oak
./build/demo

# Inspect the generated C.
./build/oak build -emit-c -o build/demo.c demo.oak

# Run a package from the repository.
./build/oak run examples/modules
```

Flags precede positional arguments. `oak build` accepts a source file or
package directory; `oak run` takes a package directory. The original
`oak file.oak` form writes C beside the input. Running `oak` without arguments,
or `oak repl`, starts the REPL.

## Language essentials

Oak uses declarations such as `name: (parameters): Result = expression`,
block bodies, and `? ... | ...` conditionals. Functions do not need a `fn`
keyword, and current control flow uses `?` rather than `if`/`else`.

- **Values and types:** fixed-width integers, `Bool`, `f32`/`f64`, nominal
  records, algebraic data types, pattern matching, generics, and refinement
  types. Errors and absence are represented by ordinary ADTs.
- **Storage and borrowing:** `[N]T` owns an array, `[]T` is a read-only view,
  and `[*]T` is a writable span. Borrowing checks exclusivity, regions, and
  lifetimes; raw pointer operations require the explicit unsafe boundary.
- **Resources and effects:** resource parameter authority, typestate,
  effect clauses, and discipline profiles make ownership and allowed
  operations part of the checked contract.
- **Modules:** directory packages inside an `oak.mod` tree, explicit `pub`
  visibility, qualified imports, sealed signatures, and checked public-API
  snapshots for module-level semantic versioning.
- **Systems and compute:** C FFI, atomics, portable SIMD, typed assembly
  units, and a constrained kernel language with C and Metal realizations.
- **Specifications in code:** `theorem` declarations, protocol state
  machines, invariants, and temporal properties consumed by `oak prove`
  and the TLA+ projection.

For example, a writable borrow can end before the same array is read:

```oak
package main

sum: (values: []u32): u32 {
  total: u32 = 0
  i: u32 = 0
  while i < len(values) {
    total = total + values[i]
    i = i + 1
  }
  total
}

main: (): i32 {
  data: [4]u32 = [4]u32{ 1, 2, 3, 4 }
  {
    writable: [*]u32 = span(&data)
    writable[0] = 10
  }
  sum(view(&data)) == 19 ? 0 | 1
}
```

Use fixed-width types for wire formats, ABI contracts, and layout-sensitive
data. On current C/native targets, `int`/`uint` are **32-bit**, including
64-bit targets; `ptr`/`uptr` track pointer width. The 32-bit MCU targets use
32-bit pointers. See the [type rules](docs/spec/20-types.md) and
[target data model](target/target.go).

The [syntax](docs/spec/10-syntax.md), [borrowing](docs/spec/50-borrowing.md),
[effects](docs/spec/60-effects-allocation.md), and
[module](docs/spec/83-modules.md) chapters define the exact supported contracts.

## Compilation and targets

The compiler checks source types, borrowing, effects, and discipline, then
uses semantic and optimization IRs to drive its backends. The default C path
emits C and invokes an external compiler. Native ARM64 and RV64 paths add
Oak's lowering, register allocation, scheduling, assembler, and per-body
semantic validation. Backend admission and verification coverage vary by
program and target.

| Target | Current route |
| --- | --- |
| `darwin/arm64`, `linux/arm64`, `freestanding/arm64` | C and Oak-native ARM64/AArch64 |
| `linux/riscv64`, `freestanding/riscv64` | C and Oak-native RV64; instruction extensions depend on the selected CPU |
| `darwin/amd64`, `linux/amd64`, `freestanding/amd64` | C through an external compiler; no Oak-native x86-64 verifier |
| `freestanding/arm`, `freestanding/riscv32` | C through an external compiler; MCU execution fixtures under QEMU |
| `core/wasm32` | Experimental direct scalar Wasm emission and independent byte/type validation |

`-target os/arch` selects a target; `OAKOS` and `OAKARCH` provide defaults.
Cross-compiling through C needs a suitable toolchain, such as Zig, cross Clang
with a sysroot, or a GNU cross compiler. Cross-running a Linux package needs
QEMU or `OAK_EMULATOR`. See [backend rules](docs/spec/90-backend.md) and
[toolchain configuration](docs/spec/115-tooling.md).

For the scalar `demo.oak` above, these commands produce native Linux ELF
executables using Oak's assembler and linker, without a C compiler or system
linker:

```sh
./build/oak build -verified -target linux/arm64 -o build/demo-arm64 demo.oak
./build/oak build -verified -target linux/riscv64 -o build/demo-rv64 demo.oak
```

`-native` attempts native lowering within an ordinary build. `-link oak`
requires all bodies to lower natively and uses Oak's linker; the freestanding
route emits an object, while `-link oak-image` emits a freestanding image.
`-verified` implies Oak linking and requires every body to receive a `proven`
verdict, refusing C fallbacks and `trusted` or `witnessed` bodies. This is a
**scoped compiler admission policy**, not a proof of the complete compiler,
linked image, loader, runtime, or hardware. The
[assembler specification](docs/spec/94-assembler.md) defines its limits.

The same standalone scalar example can be emitted as Wasm:

```sh
./build/oak build -target core/wasm32 -o build/demo.wasm demo.oak
```

The [Wasm profile](docs/spec/91-wasm.md) supports scalar functions and control
flow, with explicit refusals for unsupported forms. It currently has no memory,
host imports, WASI, or Component Model ABI; `-verified` is refused. For this
standalone-file path, keep the example free of a `package` declaration.
The [local browser playground](playground/README.md) compiles and executes
this subset. Wasm byte validation and execution tests do not establish
source-to-Wasm refinement or parity with the native proof chains.

Metal output is a separate [kernel surface](docs/spec/56-kernels.md), not a
general-purpose `os/arch` target.

## Standard library

The standard library is implemented in Oak and shipped with the compiler.
Prefer qualified package imports such as `import("bytes")`, `import("json")`,
and `import("time")`; `import(std)` remains the flat bootstrap compatibility
surface. The implemented core currently uses `Option[T]`; the architecture's
`Optional[T]` naming is still migration direction.

Current areas include:

- Explicit-storage bytes, endian codecs, bitsets, buffers, array lists,
  collections, concurrent rings, arenas, and slabs.
- Strings, Unicode, normalization, grapheme segmentation, JSON and other
  encodings, numeric text, paths, URIs, and UUIDs.
- Math, SIMD-related operations, tensors and reductions, and hashing
  including SHA-256, BLAKE3, and CRC-32C.
- [Time and calendar operations](docs/spec/114-temporal.md), RFC 3339,
  durations, host and simulated clocks, and capability-based IO/object-store
  interfaces and realizations.

The [architecture](docs/spec/75-standard-library.md) separates freestanding,
capability, and target packages. The [library guide](stdlib/README.md)
documents current APIs; the [verification inventory](stdlib/VERIFICATION.md)
records package-specific tests, public/reference oracles, Lean extractions,
proved laws, benchmarks, and remaining gaps. Neither the complete v1 package
set nor universal proofs of all library functions are finished.

## Verification and self-hosting

Save a theorem as `laws.oak`:

```oak
add_commutes: theorem (x: u32, y: u32) { x + y == y + x }
```

```sh
./build/oak prove laws.oak
./build/oak prove examples/verification_quantum.oak
```

`oak prove` reports `decided`, `refuted`, `proved`, or `open`, together with
the evidence or reason. Its paths include finite enumeration, bit-level
reasoning, checked SAT certificates, and Lean projection/checking. Protocol
declarations also produce invariant and liveness obligations and can be
projected to TLA+ for TLC. See the
[verification contract](docs/spec/125-verification.md) and
[protocol specification](docs/spec/112-protocols.md).

| Component | Current implementation and boundary |
| --- | --- |
| Compiler | The working bootstrap compiler and driver are written in Go. A complete compiler written in Oak, with bootstrap and correctness proofs, remains a v1 goal. |
| Solver and verification environment | [prove/solver](prove/solver/) contains Oak-written BDD/CNF engines, a SAT solver, certificate/model checkers, and driver components compiled by the Go seed. This is partial self-hosting, not a fully proved prover stack. |
| Proof-checking kernel | [internal/lrat](internal/lrat/) is the small Go LRAT acceptance kernel; [lrat.oak](prove/solver/lrat.oak) is the Oak implementation. Lean work covers specific production guards, initialization/deletion invariants, and extracted RUP operations; complete checker, framing, extraction, and compiler refinement remain separate obligations. |
| Assembler and linker | Production tooling remains in Go. [asm/selfhost](asm/selfhost/README.md) implements selected ARM64/RV64 relocations, named text-object linking, and minimal ELF64 writing in Oak, with execution tests and scoped model evidence. It is not yet a complete self-hosted assembler/linker. |
| Machine-level chain | ARM64 and RV64 have encoding, relocation, instruction/memory-model, and correspondence work, including Sail/Lean bridges and differential execution. Full source-to-loaded-image closure remains open on both targets. |

The [verification chain](docs/spec/126-verification-chain.md) records the
assumptions between source, checking, lowering, assembly, objects, and execution.
Model theorems, finite correspondence checks, tests, and universal implementation
refinement are different evidence. Native equality certificates currently have
audit-only coverage; they must not be read as authority for every compiler
verdict. The [status matrix](docs/spec/STATUS.md) is the detailed evidence map.

## Tools and tests

The CLI includes `build`, `run`, `install`, `vet`, `test`, `prove`, `protocol`,
`list`, `doc`, `fmt`, `env`, `version`, `clean`, `completion`, `repl`, `lsp`,
and module/dependency/API commands under `mod`. `oak fmt` is a parse-preserving
whitespace canonicalizer, not a general reflowing pretty-printer. The
[VS Code extension](editors/vscode/README.md) connects the language server.

```sh
./build/oak vet examples/modules
./build/oak test -run '^TestEpoch$' examples/time
./build/oak test -list examples/testing
```

`oak test` supports unit tests, generated properties, fuzz targets, shrinking,
corpus replay, and bounded deterministic simulations. See the
[runner guide](testrunner/README.md) and [testing contract](docs/spec/110-testing.md).

For compiler development, run from the repository root:

```sh
# Short mode skips selected expensive corpora and emulator sweeps.
go test -short -timeout 30m ./...

# Full local suite; an explicit timeout is needed for the compiler package.
go test -timeout 90m ./...

# Formal specification, with the pinned Lean toolchain installed.
(cd spec/lean && lake build)
```

Optional external-tool tests may skip locally when their tools are absent.
The workflows under [.github/workflows](.github/workflows/) define the CI
toolchains and required evidence, including sharded Go tests, Lean, Sail,
model checking, Wasm engines, and cross-target execution. A local short pass
does not substitute for those gates.

Performance claims belong with reproducible measurements: see
[BENCHMARKS.md](BENCHMARKS.md), [native workloads](benchmarks/native/README.md),
[standard-library results](benchmarks/stdlib/RESULTS.md), and
[JSON/simdjson results](benchmarks/json/RESULTS.md). Each result has a workload,
target, toolchain, and semantic contract; it is not a language-wide ranking.

## Repository guide

| Location | Purpose |
| --- | --- |
| [docs/spec](docs/spec/README.md) | Normative language/tooling contracts, stability, and verification status |
| [compiler](compiler/), [semir](semir/), [optir](optir/) | Compilation pipeline, semantic representation, and optimization IR |
| [codegen](codegen/), [nativegen](nativegen/), [machine](machine/), [wasm](wasm/) | C/Metal, native machine, and Wasm emission |
| [asm](asm/), [asm/selfhost](asm/selfhost/README.md) | Production assembly/verification/linking and Oak bootstrap components |
| [stdlib](stdlib/README.md) | Embedded Oak library sources and API guide |
| [prove](prove/), [spec/oak](spec/oak/) | Theorem machinery, Oak solver, and laws stated in Oak |
| [spec/lean](spec/lean/), [spec/sail](spec/sail/), [spec/lean-sail](spec/lean-sail/README.md) | Formal models, proofs, extractions, and ISA bridges |
| [testrunner](testrunner/README.md), [examples](examples/), [compiler/testdata](compiler/testdata/), [golden](golden/README.md) | Test tooling, examples, and conformance fixtures |
| [playground](playground/README.md), [editors/vscode](editors/vscode/README.md) | Local browser prototype and editor support |
| [docs/checklists](docs/checklists/README.md) | Correctness and performance review checklists |

When changing a feature, update its normative contract, implementation, and
relevant tests/proof evidence together. Change claimed verification states
only with evidence review; the status inventory is mechanically checked.
