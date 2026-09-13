# Design note: runtime processor-feature dispatch

**Status: design settled and first increment landed, 2026-09-13.** The
dbs pilot's ask 7 ("vector dispatch across AArch64 feature levels and RVV
behind one deterministic interface") had three parts; the realizations —
NEON, RVV, SVE, portable — landed as build-time choices under `-cpu`
(`docs/notes/dbs-feedback-2026-09.md`, ask 7). This note settles the part
that was still open: choosing between realizations **at run time**, on the
processor the program finds itself on, without giving up the properties
the rest of the language holds — one meaning, no hidden state, pay for
use, checkable claims. The normative text is `93-simd.md` §6.

## The question

A binary built for `linux/arm64` at the toolchain baseline (`generic`,
ARMv8.0-A) runs on a Graviton 3 with SVE, a Neoverse V2 with SVE2, and an
Apple M-series core with neither. Today the SVE realization of the
scalable API is selected by `-cpu generic+sve`, which produces a binary
that faults on the M-series. The pilot wants one binary that uses SVE
where it exists and NEON or the portable loop where it does not, and
wants the choice to be **deterministic**: the same processor, the same
realization, every run, with nothing chosen per call.

## What is settled

**1. The body is the meaning; realizations are a claim.** A function
declares its realizations in a clause beside its effect clauses:

```oak
count_sevens: (xs: []u8) -> u32 dispatch { sve: count_sevens_sve } = {
  ...the portable body...
}
```

The body is what the interpreter runs, what the Lean extraction sees,
what `oak prove` reasons about. Each realization is an ordinary function
of the identical signature; naming it in the clause is the author's claim
that it is observationally equal to the body — the same kind of claim as
`laws { associative }`, on the author's authority, checked by the
differential harness (below), never assumed by the verifier. Effects are
the union of the body's and every realization's, so a realization cannot
hide an allocation behind a feature the checker did not run on.

**2. Features are a closed catalog tied to an architecture.** `sve`,
`sve2` (AArch64), `rvv` (RISC-V V). A slot for another architecture is
inert on this target — not compiled, not consulted. Adding a feature is a
catalog entry in `semir` (its architecture, the C preprocessor macro
that means the build baseline already guarantees it, the function
attribute that enables it for one function, the probe bit) plus its
probe; it is a language change and reviewed as one.

**3. Where the probe runs.** Once, before `main`, into one word.
The C backend emits `oak_cpu_features` (a `static u64`) and
`oak_cpu_init()`, called first thing in the emitted `main`. A library
built for a C host (no Oak `main`) gets `oak_cpu_init` as a constructor
on hosted targets and as an exported function the host calls on
freestanding ones; an uninitialized word reads as "no features", which
selects the body. The probe by target:

| Target | Probe |
| --- | --- |
| `linux/arm64` | `getauxval(AT_HWCAP)` bit `HWCAP_SVE` (22); `AT_HWCAP2` bit `HWCAP2_SVE2` (1) |
| `darwin/arm64` | `sysctlbyname("hw.optional.arm.FEAT_SVE")`; absent reads as 0 |
| `freestanding/arm64` | `MRS ID_AA64PFR0_EL1` bits [35:32] (SVE); `ID_AA64ZFR0_EL1` bits [3:0] ≥ 1 (SVE2). Needs EL1 or higher, which a kernel has |
| `linux/riscv64` | `riscv_hwprobe` (syscall 258), key `IMA_EXT_0`, bit `V` (2) |
| `freestanding/riscv64` | none: `misa` is M-mode only. `rvv` is available only when the build guarantees it |

**4. The static rule.** When the build baseline already guarantees a
feature (`__ARM_FEATURE_SVE` under `-cpu generic+sve`; `__riscv_vector`
under `+v`), the dispatched function *is* that realization: no probe bit
is consulted and no branch is emitted. Runtime dispatch is only ever the
difference between the baseline and the processor.

**5. How a call is lowered.** No function pointers. The dispatched
function's body begins with one branch per slot, in clause order, on the
feature word — `if (oak_cpu_features & OAK_CPU_SVE) return f_sve(args);`
— and then falls into its own body. The word is a loaded constant after
`oak_cpu_init`; the branch is predictable and the C compiler may hoist it
out of a loop that calls the function. Kernels and other contexts that
forbid indirect calls are unaffected.

**6. One translation unit, two lowerings.** Every realization named in
an `sve` slot is emitted with `__attribute__((target("sve")))` and in
**SVE mode**: its scalable-API locals are the sizeless `svuint8_t` family
and its helpers the `__sve`-suffixed copies, which the backend emits
beside the baseline helpers when the program has such a slot (guarded by
`__has_include(<arm_sve.h>)`, so a toolchain without SVE support builds
the program with the slot inert). The mode is decided by the slot, not by
inspection of the body: a function is SVE-realized because the program
says so. RVV slots work the same way (`target("arch=+v")`, `__rvv`
helpers). The locality rule of the scalable API (OAK-S0401) is what makes
this sound: sizeless values never cross a function boundary or land in a
record, so a realization's types are its own business.

**7. How the interpreter mirrors it.** The interpreter has one portable
semantics and no processor. It carries a feature set (`evaluator.Features`,
default empty), set by a test or the REPL; with `sve` in the set, a call
to a dispatched function runs the `sve` realization's Oak body instead of
the function's own. Since the scalable API is extent-independent
(`Oak.Simd.chunked_*`), the realization has a meaning in the interpreter
too, and the two runs are the **differential check** of the claim in (1):
`interpretChecked` with and without the feature, and the native run under
QEMU with `sve-max-vq` set, must agree. The test in
`compiler/e2e_dispatch_test.go` does exactly that, and the C-side shape is
pinned by `codegen/aarch64_dispatch_test.go`.

**8. What is proved.** `Oak.Dispatch` (Lean): selection is a function of
the available features and the clause (`select`), it yields the body when
no slot's feature is available (`select_none`), it yields the body or a
listed realization and nothing else (`select_mem`), and when every
realization denotes the body's function, the dispatched function denotes
it too (`dispatch_sound`). The claim itself — that a realization is equal
to the body — is what the differential harness checks; the theorem says
that is the only thing left to check.

## What is not settled

- **A wider vocabulary.** `crc`, `sha2`, `aes`, `lse`, `dotprod`, `i8mm`,
  and the RISC-V `zba`/`zbb`/`zvbb` are natural entries; each needs its
  attribute spelling, its probe bit, and a realization worth writing.
- **Per-call-site selection** (a hot loop that hoists the branch itself)
  is deliberately not offered: the C compiler hoists a branch on a
  loaded constant, and a program that wants it explicit can dispatch the
  whole loop.
- **GCC.** `arm_sve.h` under GCC needs `#pragma GCC target("+sve")` around
  the include; the toolchain is clang (zig cc), and the emitted C says so
  in a comment at the include.
- **An `OAK_CPU_FEATURES` override** to restrict the probe from the
  environment was considered and rejected: it would make the selection a
  function of something other than the processor. The interpreter's
  feature set, the QEMU vector-length knob, and `-cpu` cover testing.
