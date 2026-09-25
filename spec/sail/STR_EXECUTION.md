# Original STR body: conditional execution boundary

`str_execution.sail` retains the complete pinned Arm
`memory_single_general_immediate_signed_postidx` declaration and body,
including its final writeback. It also retains the original general-register
bank/accessor, processor state, syndrome functions, and full exception union.
The export includes the original `aset_Mem`, `AArch64_aset_MemSingle`, and
`IsFault` bodies and complete address, fault, and access descriptors.
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
the proved entry fixes size eight. Both original Sail bodies remain unchanged. To export them together, only
the instruction's local cut declaration is named `oak_instruction_aset_Mem`;
its `Mem` overload still selects `boundaries.aset_Mem`. The concrete callee
retains its original name. Independent tests check this alias and wiring.

The aligned normal eight-byte theorem preserves `HaveNV2Ext`, `BigEndian`,
conditional `BigEndianReverse`, `AArch64_CheckAlignment`, and
`AArch64_aset_MemSingle`. Normal accesses skip `SCTLR_EL2`: its read belongs
only to the enabled NV2-register branch. No callback is assumed pure,
transactional, or successful. Distinct intermediate states prevent using
initial-state facts after arbitrary callback mutations. The STR composition
starts this prefix after the original operand/syndrome operations.

### Explicit short-circuit repair

Sail 0.20.2's Lean backend emits Boolean operands containing nested monadic
lifts. Lean elaborates those lifts eagerly. A same-source effectful-register
probe confirmed that this differs from Sail's short-circuit semantics and its
Lem output. In particular, the previous uncorrected export read `SCTLR_EL2`
even for a normal access. A proof about that export alone was not proof of the
original source semantics.

The generator now repairs exactly two pinned conditions with explicit nested
monadic `if` expressions: the syndrome's EL0/EL1 test and the memory wrapper's
NV2/access-type/SCTLR/endian test. The latter skips the register read unless
both guards hold, and skips `BigEndian` when the NV2 endian branch is true.
The whole raw function export is hash-pinned; any new output requires a fresh
Boolean-site audit. Independent tests reconstruct both repairs and reject
guard removal, duplicate/omitted callbacks, wrong register bits, and any other
body edits. This is a finite compatibility repair, not a verified Sail compiler
or a general old/new-prelude refinement. Real-callee and full-state
correspondence remain required.

`lean/STRShortCircuit.lean` kernel-checks the conditional-action laws for
arbitrary states and errors, and counterexamples to the uncorrected eager
forms. The memory bridge separately checks the repaired concrete generated
callee, including missing-register and poisoned-endian cases.

The final store's whole result, including failure and partial state changes,
is retained. Separate rules cover earlier callback failures and an unaligned
first-byte write that fails before the unpredictable-choice query or remaining
bytes. Poisoned fixtures check absent registers, alignment failure, conversion
effects, partial memory changes, and invalid erased widths. These are
conditional sequential-runtime proofs, not an architectural event or atomicity
claim. Exact axiom guards admit only Lean's standard logical axioms.

## Original MemSingle execution

`lean/STRMemSingleBridge.lean` extends the conditional boundary through the
whole original `AArch64_aset_MemSingle` body. The old callback is locally named
`oak_memory_aset_MemSingle`; its `MemSingle` overload still selects
`memory.AArch64_aset_MemSingle`. A separate checked binding installs the
retained body without silently changing the previous cut. Deeper callees are
explicit `MemSingleBoundaries`, not successful placeholders.

The normal eight-byte factorization preserves the alignment assertion and
translation call before fault handling, shareability-dependent exclusive
clearing, access-descriptor construction, tag checking, and the final `_Mem`
call. Translation returns a full original `AddressDescriptor`; its physical
address includes all 52 address bits and the NS bit. No virtual-to-physical
cast or assumed fault-free descriptor substitutes for translation.

An arbitrary `AArch64_Abort` or `TagCheckFail` callback may return normally;
in that case the original body continues. Proving architectural non-return
requires a real implementation or an explicit premise. `ProcessorID` runs
before `ClearExclusiveByAddress`, and the three tag-path `ZeroExtend` calls
remain distinct effectful actions. Callback errors preserve their exact
partial state. These are sequential-runtime properties, not atomicity,
architectural fault delivery, or ordering theorems.

Remaining obligations include decoder/PostDecode execution, SP paths, actual
MTE/endian/alignment and deeper MemSingle callees, translation/faults, physical
memory routing, full-state refinement, architectural events and CAT/BBM
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
changes are imports/namespaces, opening `PreSail`, adding the explicit
`Boundaries`/`MemoryBoundaries`/`MemSingleBoundaries` parameters, and the two
short-circuit repairs described above. All other raw function-body bytes are
retained unchanged.
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
