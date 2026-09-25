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

The reduced state contains `_R`, `PSTATE`, and `__LSISyndrome`, not RAM or the
full architectural register set. This is a separate generated model from
`Out`, with a distinct register type and full original exception union.
Neither a shared spelling nor the callback record proves a refinement between
these models. Instantiating real Arm callees requires a typed state
lifting/projection and exception correspondence (or a larger export).

Remaining obligations include decoder/PostDecode execution, SP paths, actual
MTE and memory callees, translation/faults, architecture events and CAT/BBM
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
`Boundaries` parameter. The instruction's generated body is not edited.
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
