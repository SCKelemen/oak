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
cd external/sail-riscv/build/model/Lean_RV64D && lake update && lake build LeanRV64D.Prelude
cd ../../../../spec/lean-sail && lake update && lake build
```

`lake update` here matters: this project's manifest must resolve the
`Sail` library to the revision the export pins (lean-sail `v5`), or lake
recompiles the export's modules against the wrong library and fails in
`SpecializationV1`.

## Status (2026-09-13)

**The bridge builds against the import.** With Sail from git (`sail2`
dba5f007, 2026-09-11) and sail-riscv 0.14, `spec/lean-sail` compiles and
its fifteen theorems are checked against the export's own definitions:
the prelude's comparison operators (`zopz0zI_s`, …), `sign_extend`,
`zero_extend`, `bool_to_bit`, and the library's shift helpers. The export
has moved since the restatement was written: prelude functions live in
`LeanRV64D.Functions`, `shift_bits_left`/`shift_bits_right` in the
lean-sail library (`Sail/Common.lean`), and the library is split into
modules; `asm/rv64_sail_bridge_test.go` reads them all.

**What still does not compile is the whole library.** The Lean backend
leaves type-level functions untranslated (rems-project/sail#1729, open):
`Defs.lean` applies `is_sv32_mode(k_v)` in Sail syntax inside the
virtual-memory type synonyms and never defines the predicates —
`patch-export.py` repairs those seven sites (nothing about instruction
semantics) — and `Vmem.lean` then fails on four sites of its own (the
`satp_mode` / `hgatp_mode` type synonyms shadowed by functions of the same
name, and a page-table-walk recursion whose termination measure the
backend states wrong). sail-riscv's own `compile-lean` workflow fails on
master for the same reason. So the bridge imports `LeanRV64D.Prelude`,
whose closure (Defs, the specialization, the library) builds cleanly and
holds everything the theorems name, rather than `LeanRV64D`; the
`execute_RTYPE` / `execute_RTYPEW` / `execute_BTYPE` bodies in
`InstsEnd.lean` are read by inspection as before. When upstream fixes
#1729, drop the patch, restore `import LeanRV64D`, and point
`TestRV64SailBridgeBuilds` back at `LeanRV64D.olean`.

`spec/lean/Oak/SailRiscVBridge.lean` keeps the verbatim restatement so
Oak's own project proves the same theorems without the export;
`TestRV64SailBridgeStubsMatchSail` fails if it drifts from the fetched
sources.
