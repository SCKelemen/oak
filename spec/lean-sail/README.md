# Oak ↔ Sail RISC-V bridge

The Sail RISC-V model is the ratified golden model of the ISA. This lake
project imports its Lean export and proves that the RV64 semantics Oak's
assembler verifier transliterates (`spec/lean/Oak/RiscV.lean`) agree with
the model's own definitions, instruction by instruction, for the subset
the verifier decides (`docs/spec/94-assembler.md` §9).

The bridge lives in its own project because the Sail export pins Lean
v4.29.0 while Oak's specification uses a newer toolchain. The Oak
definitions it checks are restated verbatim in `OakSailBridge/RiscV.lean`;
`asm/rv64_sail_bridge_test.go` fails if they drift from
`spec/lean/Oak/RiscV.lean`, and runs `lake build` here when the export is
present.

Generating and building the export (once; it is large). The export needs
Sail built from git: the opam release 0.20.2 emits Lean that does not
compile, and a `libsail` pinned from git needs `sail_maker` pinned from
the same checkout (its build runs `sail_maker embed`). In one Sail
checkout: `opam switch create sail-dev 5.2.1`, `opam pin add -n .`
(every package, `sail_maker` included), `opam install sail_maker libsail
sail sail_lean_backend`. Then, with that switch active
(`opam exec --switch sail-dev -- …`):

```sh
git clone --depth 1 --branch 0.14 https://github.com/riscv/sail-riscv external/sail-riscv
cmake -S external/sail-riscv -B external/sail-riscv/build
cmake --build external/sail-riscv/build --target generated_lean_rv64d   # ~30 min
python3 spec/lean-sail/patch-export.py                                   # see Status
cd external/sail-riscv/build/model/Lean_RV64D && lake update && lake build   # ~6 min
cd ../../../../spec/lean-sail && lake update && lake build
```

`lake update` here matters: this project's manifest must resolve the
`Sail` library to the revision the export pins (lean-sail `v5`), or lake
recompiles the export's modules against the wrong library and fails in
`SpecializationV1`.

## Status (2026-09-13)

**The bridge builds against the import, execution bodies included.** With
Sail from git (`sail2` dba5f007, 2026-09-11) and sail-riscv 0.14, the
whole export compiles after `patch-export.py`, and `spec/lean-sail` proves:

- `OakSailBridge/RiscV.lean` — the data semantics: for each RTYPEW, RTYPE
  comparison and BTYPE operator, the Sail expression equals Oak's function
  of the register values (fifteen theorems against the export's own
  `sign_extend`, `zero_extend`, `bool_to_bit`, comparison operators and
  the library's shift helpers).
- `OakSailBridge/Execute.lean` — the bodies: `execute_RTYPEW`,
  `execute_RTYPE` and `execute_BTYPE` (`LeanRV64D/InstsEnd.lean`) each
  rewrite, through the monad laws (`SailM` is an `EStateM`) and the data
  theorems, to "read the two sources, write Oak's function of them" or
  "branch on Oak's `Br.holds`". Nothing about these instructions is read
  by inspection any more; what the theorems take as given is the register
  file (`rX_bits`/`wX_bits`) and `jump_to`.

`patch-export.py` is a pinned workaround for the Lean backend
(rems-project/sail#1729, open; sail-riscv's own `compile-lean` workflow
fails on master for the same reason). It repairs seven virtual-memory type
sites in `Defs.lean` (type-level predicates left in Sail syntax and never
defined) and, in `Vmem.lean`, three `SailM satp_mode`/`hgatp_mode`
ascriptions where a function shadows the type synonym and the termination
of the two-stage translation: Sail's measure is the constant 1000, so Lean
saw no decrease from the VS-stage walk into the G-stage translation; the
patch gives the eight mutually recursive functions a lexicographic measure
(stage rank, a rank along the call chain, the walk level) and a
`decreasing_by`. It touches no instruction semantics. Drop it when upstream
fixes #1729.

The export has moved since the restatement was written: prelude functions
live in `LeanRV64D.Functions`, `shift_bits_left`/`shift_bits_right` in the
lean-sail library (`Sail/Common.lean`), and the library is split into
modules; `asm/rv64_sail_bridge_test.go` reads them all. This project's
manifest must resolve `Sail` to the export's pin (lean-sail `v5`, see the
recipe), or lake recompiles the export against the wrong library.

`spec/lean/Oak/SailRiscVBridge.lean` keeps the verbatim restatement so
Oak's own project proves the data theorems without the export;
`TestRV64SailBridgeStubsMatchSail` fails if it drifts from the fetched
sources.
