# The Oak Assembler: Typed Abstract Assembly Units

This chapter fixes the design of Oak's assembler. The baseline is Go's
assembler — one abstract assembly language over per-architecture
instruction sets, function-shaped, integrated with the normal build — with
the parts Go leaves untyped made typed, and with lower-level control
available where systems code needs it. The instruction-function layer
(`92-ffi.md` §3, `93-simd.md`) is already normative and implemented; this
chapter governs the next layer: **whole functions written as instruction
sequences**. **v1 is implemented** (§7 lists exactly what landed and what
is pending); the design sections remain normative for the rest.

## 1. Position

- Assembly lives in **`asm` translation units** (`name.arm64.oakasm`),
  never inline in Oak function bodies — the same rule as C
  (`92-ffi.md` §1). An Oak file declares the typed interface; the asm unit
  provides the body for a named architecture. The build system selects the
  unit matching the target, or the Oak fallback body if one is declared.
- An asm function is **function-shaped**: it has exactly the declared Oak
  signature, receives arguments per the Oak calling contract, and must
  return through it. There is no open-coded fall-through between asm
  functions.
- The assembler is an **abstract assembler** in Go's sense: mnemonics and
  operand order are the architecture's own (what the ARM ARM documents),
  but frame layout, symbol references, and calling-contract plumbing go
  through typed pseudo-operands rather than raw offsets.

## 2. Surface: the same declaration form

An asm function is declared and defined with Oak's ordinary declaration
form — the interface is a function type, the definition is an instruction
block. The Oak side declares the interface (definition-less, legal exactly
when an asm unit or an Oak fallback provides the body):

```oak
add_asm: (left, right: u32) -> u32
```

The architecture unit (`add.arm64.oakasm`) repeats the **identical**
signature and supplies the instruction sequence as its definition:

```oakasm
add_asm: (left, right: u32) -> u32 = {
  push left
  push right
  add
}
```

Rules:

- **Signature identity**: the asm unit's signature must match the Oak
  declaration token-for-token after normalization; a mismatch is a
  compile-time error naming both sites. The signature is the contract — the
  caller never knows or cares that the body is assembly.
- **Named operands**: parameters and asm-local names are first-class
  operands. The assembler performs register binding for named values; the
  operand-stack shorthand above (`push`/`add` popping two, pushing one) is
  sugar over the same bound values, for bodies where explicit register
  choice adds nothing. The final stack value (or the named result) is the
  return value, checked against the declared return type.
- **Explicit registers when it matters**: a body may pin names to
  registers with the register types of §3 (`bind x0 = left`), and from that
  point the width and clobber discipline of §3 applies. Mixed bodies are
  legal; the assembler refuses ambiguous bindings rather than guessing.
- **One function, one unit**: each asm function body lives in exactly one
  unit per architecture. The build selects `name.arm64.oakasm` for an
  AArch64 target, another architecture's unit for its target, or the Oak
  fallback body; a target with neither is a build error, not a silent stub.

## 3. Register types

Registers are values of **register types**: nominal, zero-cost types known
to the assembler's checker. They exist so that an asm unit is checked, not
trusted, at its seams. v1 register classes for AArch64:

| Type | Class | Members |
| --- | --- | --- |
| `arm64.X` | 64-bit general register | `x0`–`x30` |
| `arm64.W` | 32-bit view of a general register | `w0`–`w30` |
| `arm64.V` | 128-bit vector register | `v0`–`v31` |
| `arm64.SP` | stack pointer (singleton) | `sp` |
| `arm64.Flags` | condition flags (singleton) | `nzcv` |

Rules the checker enforces inside an asm unit (whether names were bound explicitly or by the assembler):

- **Binding**: each parameter of the Oak signature is bound to its
  contract register with its class type (`a: i64` arrives in an `arm64.X`;
  a `simd.U8x16` arrives in an `arm64.V`). The result must be produced in
  the contract result register. Bindings are written, not inferred, so the
  unit is readable without knowing the contract by heart — and checked, so
  it cannot be wrong.
- **Width discipline**: an instruction taking `arm64.W` operands cannot be
  handed an `arm64.X` binding, and vice versa; `wN`/`xN` aliasing of the
  same physical register is tracked (writing `w5` clobbers the `x5`
  binding's upper half — the checker knows).
- **Clobber declarations**: every register the body writes beyond its
  bindings is declared. Writing an undeclared register is an error;
  declaring callee-saved registers adds the save/restore obligation to the
  frame contract.
- **Flags are a register**: instructions that set or read `nzcv` say so in
  their instruction-table entries, and a conditional consuming flags must
  be dominated by a producer with no intervening clobber — checked, the
  way value dataflow is.
- **No hidden memory**: memory operands go through declared frame slots or
  through pointer parameters that arrived typed. Stray absolute addresses
  are not expressible.

The register types also appear (read-only) in Oak's diagnostics and
tooling, but they are **not** first-class in ordinary Oak code: an Oak
function cannot declare an `arm64.X` local. They exist at the asm boundary
only, which is what keeps them zero-cost.

## 4. Lower-level than Go

Where Go's assembler stops, Oak's continues, in declared and checked form:

- **Explicit register binding** (`bind x0 = a`) instead of frame-symbol
  indirection for arguments.
- **Flags dataflow** as in §3 — Go treats flags as invisible; Oak checks
  them.
- **Barriers and ordering**: `dmb`/`dsb`/`isb` and load-acquire /
  store-release instruction forms are first-class table entries whose
  memory-order effects tie into the machine-memory model
  (`spec/lean` machine-memory foundation).
- **System registers**: reads of counter/ID registers (`mrs`) are table
  entries with declared effects; writes are behind a per-unit `system`
  capability declaration.
- **Prefetch and cache maintenance** as effect-annotated instructions.

Everything remains within the abstract-assembler frame: no raw encodings,
no undeclared side effects, no self-modifying code.

## 5. Trust and verification

An asm unit is a **declared trust boundary** narrower than `c.extern`: the
signature is enforced by the checker at the seams (bindings, clobbers,
frame), the instruction semantics come from the per-architecture table, and
what remains trusted is the author's algorithm, exactly as with any
verified-boundary component. The roadmap for shrinking that trust:
instruction-table entries carry semantic definitions compatible with
`Oak.Intrinsics`/`Oak.Simd`, so straight-line asm bodies can eventually be
checked against a stated postcondition. Until the checker exists, the
`arm64.*` instruction functions are the supported way to reach specific
instructions — they need no trust beyond the compiler itself.

## 6. Relation to the instruction-function layer

The instruction functions of `92-ffi.md` §3 and `93-simd.md` are the
assembler's semantic anchor: each asm instruction-table entry that has an
instruction-function counterpart must cite the same semantics. A kernel
should be written with instruction functions first; an asm unit is the
escalation for register-allocation-critical or flags-critical inner loops,
not the default.

## 7. v1 implementation scope

Landed (`asm/` package; `Compilation.WithAsmUnit`; executed natively on an
AArch64 host — `compiler/e2e_asm_test.go`; laws in `Oak.Assembler`):

- **Units and stitching.** `.oakasm` units hold `name: (params) -> Ret = {
  ... }` blocks whose header is parsed by the Oak parser; each pairs with a
  definition-less Oak declaration of identical signature (structural
  comparison; mismatch, missing declaration, missing unit, and duplicate
  definitions are `asm`-phase errors). Body-less declarations are legal
  syntax only for this purpose.
- **Directives.** `bind <reg> = <param>` (written, never inferred; must be
  the AAPCS64 contract register at the parameter's width class — `w0` for
  `u32`, `x0` for `u64`, `v0` for `simd.*`), `clobber <regs>`, `frame N`
  (multiple of 16), `system` (capability for `mrs`/`msr`/`eret`), and
  `align N` (a power of two; the first sets the entry alignment).
- **Instruction table (AArch64).** `mov add sub adds subs and orr eor lsl
  lsr cmp ldr str ldp stp b b.<cond> bl ret eret mrs msr dmb dsb isb nop`,
  each with its legal operand forms, flag effects, memory effect, branch
  kind, and privilege requirement. Nothing outside the table is
  expressible.
- **The seam checker.** Width discipline with `wN`/`xN` aliasing; no read
  of a register that is not bound, written, `sp`, or a zero register (no
  uninitialized reads); no write outside bound registers, the result
  register, and declared clobbers; callee-saved `x19–x29` refused as
  clobbers (save/restore obligations pending); flags consumers dominated by
  a producer with labels and calls invalidating; memory only through the
  declared `sp` frame, with the static sp displacement tracked through
  pre/post-index and `add/sub sp` and every access bounds-checked against
  `[-frame, 0)`; displacement agreement at every label, 0 at every `ret`
  and at every branch to another function; `bl` requires `clobber x30` and
  invalidates caller-saved state; `align` regions whose instruction bytes
  exceed their stride are refused, and an aligned region is an **entry
  point** (fresh state, displacement 0 — the vector-table shape); no
  unreachable instructions, no fall-through past the end, no `ret` from a
  `never` function, `eret` only from `never`/unit results.
- **Emission.** The Oak declaration emits an ordinary C prototype; the
  block emits a top-level `__asm__` under the prototype's C symbol
  (`OAK_ASM_SYMBOL` applies the target's user-label prefix, so Mach-O and
  ELF both link), numeric local labels (`1:`/`1b`/`1f`, assembler-local on
  both object formats), `.balign` for entry and region alignment. A
  non-AArch64 target fails closed with `#error`.
- **Executed:** `add_asm`, a trap-frame save/restore of `x0–x17` as pairs
  under `frame 160`, a flags/label loop, and a 2 KiB-aligned sixteen-entry
  `eret` vector table (assembled, its extents checked statically).

- **Typed pointer memory.** A span (`[*]T`) or view (`[]T`) parameter of
  fixed-width elements crosses as its `{base, u32 len}` pair and binds
  both registers explicitly — `bind x0, w1 = frame` (the base pointer,
  then the 32-bit length; the upper half of `x1` is padding the contract
  never defines, so only `w1` is ever consulted). Memory through the base
  (`ldr x9, [x0, #8]`) is admitted only under a **dominating bounds
  guard**: `cmp w1, #N` immediately followed by `b.lo <fail>` proves
  `len >= N` on the fall-through path, and the checker then proves each
  access `[off, off+size)` lies within `N * elem` bytes
  (`Oak.Assembler.span_access`). Guards die at labels, at calls, and on
  any write to the base or length register; a span base is never moved
  (no pre/post-index); stores through a view are refused; a comparison
  of `x1` is not a guard. This is the bounds-check doctrine made explicit
  in assembly: the runtime check is written by the author, its dominance
  is verified by the checker, and the offsets under it are proven.
- **Callee-saved obligations.** `x19`–`x30` carry the caller's values on
  entry (readable without a write), may be written only after being
  **saved** into the declared frame (a `str`/`stp` from the still-untouched
  register records its absolute slot), and every `ret` requires each
  written callee-saved register **restored** from that same slot (`ldr`/
  `ldp`, matched by absolute address relative to entry sp, not by textual
  offset) with no write after the restore. `bl` in a returning function
  requires the link register saved first (`stp x29, x30, [sp, #-16]!`) —
  the call clobbers it, so the same restore obligation covers it before
  `ret`; never-returning functions keep the clobber-only rule.
- **Oak fallback bodies.** A declaration may carry both an Oak body and an
  asm unit of identical signature: the asm block emits under
  `__aarch64__` (and not `OAK_PORTABLE_INTRINSICS`), the compiled Oak body
  under the complementary condition, so programs with asm units build on
  non-AArch64 hosts and the Oak body is the portable semantics the asm
  must agree with — the differential-witness convention of `93-simd.md`
  extended to hand-written assembly. Without a fallback, a non-AArch64
  target still fails closed with `#error`.
- **`address_of(f)`** yields the `u64` code address of an asm-backed
  function and nothing else — the `VBAR_EL2` install path
  (`arm64.write_vbar_el2(address_of(vectors))`). Ordinary Oak functions
  have no exposed address.

Pending: the operand-stack shorthand
(`push left / push right / add`); the semantic
verification of straight-line bodies against `Oak.Intrinsics`.
