# Original STR body: conditional execution boundary

`str_execution.sail` retains the complete pinned Arm
`memory_single_general_immediate_signed_postidx` declaration and body,
including its final writeback. It also retains the original general-register
bank/accessor, processor state, syndrome functions, and full exception union.
`lean/STRExecutionBridge.lean` proves the non-SP, no-writeback 64-bit STORE case
of that generated body. This is a callee-parametric theorem, not a theorem of
full architectural execution.

The feature query, not-tag-checked update, and memory call remain arbitrary
monadic callbacks. The theorem preserves their mutations, failures, and
ordering: operands and PSTATE are read after the feature prefix; a failing
memory call returns its actual resulting state. Other callbacks are retained
for the unselected instruction branches. No callback has a default successful
implementation. The 64-bit/8-byte theorem supplies the source constraints
erased from the generic Lean export.

The generated register set contains `_R`, `PSTATE`, `__LSISyndrome`, and
`SCTLR_EL2`, not the full architectural register set or `__defaultRAM` selector.
The sequential runtime has a byte map, but that alone does not implement Arm
memory. This is a separate generated model from
`Out`, with a distinct register type and full original exception union.
Neither a shared spelling nor the callback record proves a refinement between
these models. Instantiating real Arm callees requires a typed state
lifting/projection and exception correspondence (or a larger export).

## Original memory-callee execution

`lean/STRMemoryBridge.lean` also retains the complete original `aset_Mem`
body in this same generated state. `bindMemory` installs that callee in the
instruction's explicit callback, rejecting mismatched erased width/count
arguments; the composition theorem discharges the check for 64 bits/eight
bytes. The adapter does not additionally check the erased source size set;
the proved entry fixes size eight. Both original bodies remain unchanged. To export them together, only
the instruction's local cut declaration is named `oak_instruction_aset_Mem`;
its `Mem` overload still selects `boundaries.aset_Mem`. The concrete callee
retains its original name. Independent tests check this alias and wiring.

The aligned normal eight-byte theorem preserves the actual sequence:
`HaveNV2Ext`, the generated `SCTLR_EL2` read, `BigEndian`, conditional
`BigEndianReverse`, `AArch64_CheckAlignment`, and `AArch64_aset_MemSingle`.
In this pinned export the register read is eager even when NV2 is false and
the access is normal. Its presence is required **after** the feature callback;
a missing entry returns runtime `Unreachable` before the endian query.
That error is not an architectural Data Abort. No callback is assumed pure,
transactional, or successful. Distinct intermediate states prevent using
initial-state register facts after arbitrary callback mutations. The STR
composition starts this prefix after the original operand/syndrome operations.

The eager-read result is about this adapted sequential export, not a claim
about every original-model backend. The modern prelude has special handling
for effectful Boolean operators, and some originally pure cuts (including
`HaveNV2Ext`) are intentionally impure here. Original body retention alone
does not prove preservation across these adaptations; real-callee and
old/new-prelude correspondence remain required.

The final store's whole result, including failure and partial state changes,
is retained. Separate rules cover earlier callback failures and an unaligned
first-byte write that fails before the unpredictable-choice query or remaining
bytes. Poisoned fixtures check absent registers, alignment failure, conversion
effects, partial memory changes, and invalid erased widths. These are
conditional sequential-runtime proofs, not an architectural event or atomicity
claim. Exact axiom guards admit only Lean's standard logical axioms.

Remaining obligations include decoder/PostDecode execution, SP paths, actual
MTE/endian/alignment callees and `MemSingle`, translation/faults, architecture events and CAT/BBM
ordering, and composition with Oak-to-native simulation. In particular,
sequential RAM equality does not establish architectural ordering.

## Regeneration and audit

With Sail 0.20.2 and the repository's pinned original Arm model installed:

```sh
go run spec/sail/str_execution_regen.go --sail /path/to/sail
go test ./asm -run '^TestSailArmSTR64Execution|^TestSailSTRExecution' -count=1
```

The generator hashes the four upstream source files before extracting whole
declarations. `--output-dir DIR` writes a separate export plus raw Sail output
for comparison; it does not change the committed files. The only Lean framing
changes are imports/namespaces, opening `PreSail`, and adding the explicit
`Boundaries`/`MemoryBoundaries` parameters. Neither generated body is edited.
Independent tests compare the whole raw/framed artifacts, regenerate every
committed output, and reject source, callback-wiring, and framing mutations.
The formal Sail workflow requires these tests and builds the bridge.

Compatibility with the modern Sail prelude is explicit: `UInt`, `Zeros`, and
`__GetSlice_int` use modern helpers; division uses `Nat.div` on the source's
nonnegative/positive domain; enum equality uses the Lean runtime adapters.
The proofs concern this generated sequential runtime with its existing
trivial choice source. They are not a general old/new-prelude or
nondeterministic-runtime refinement.

`str_execution_vector.sail` is Sail 0.20.2's `lib/vector.sail`, with only the
unused `val signed` binding renamed to `val oak_signed_compat` to avoid a
collision with an original Arm local variable. Its unmodified SHA-256 is
`73855de7cdfbef3cc5ba22b64478d1ae031ad56fdc80a4dedc8fdfbb4db1218b`;
the generator and independent mutation tests check this exact adaptation.
Its original copyright/SPDX header is retained; [SAIL-LICENSE](SAIL-LICENSE)
contains the accompanying Sail distribution license. The derived Arm fragment
separately retains the original Arm license header.
