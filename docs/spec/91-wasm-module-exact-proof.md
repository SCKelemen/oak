# Extracted complete-Wasm writer: universal successful modules

`bitwise_module_exact` from `Oak.WasmBitwiseModuleExact` (in namespace
`Oak.WasmAssembler`) proves that the actual mechanically extracted
`wasm_bitwise_module` returns the complete independently specified named module
on every valid, sufficiently sized input. It does not assume a successful or
returning execution. `none` continues to mean extraction-fuel exhaustion,
whereas `some (0, dst)` is ordinary refusal.

## Exact contract

For arbitrary initial destination and name arrays, operation tag, and fuel:

- `1 ≤ op ≤ 3`, corresponding to AND, OR, and XOR;
- `1 ≤ name.size ≤ 256`;
- every name byte is nonzero and less than 128;
- `dst.size < 2^32`;
- the complete independently specified module length fits `dst.size`;
- `max (name.size + 1) 15 ≤ fuel`.

The actual extracted function returns exactly
`some (UInt32.ofNat bytes.length, writeBytes dst 0 bytes)`, where `bytes` is
`BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList`. This is the
existing mathematical `writeBytes`, not another executable module writer.
Its fitting-span laws establish every emitted byte at a genuine in-bounds
index, unchanged destination size, and the entire preserved original suffix.
The returned count's natural value is exactly `bytes.length`, without wrapping.

The independent byte specification lives in `Oak.BitwiseNamedModule`. It uses
canonical 32-bit unsigned LEB encodings of the actual name length and export
payload length, the fixed magic/version/type/function/export/code fields, the
entire arbitrary name, and `BitwiseFunction.functionBytes`. Its length is

`36 + name.length + nameLengthLEB.length + exportPayloadLengthLEB.length`.

The specification and loader proof have no dependency on the new module writer
proof. They use the pre-existing independent encoder, complete-section loader,
and bitwise-function semantics. The general loader accepts nonempty bounded
ASCII names; the actual writer's stronger non-NUL requirement remains explicit
in the writer theorem.

## Composition and bounds

The proof reuses the reviewed validation and name-copy inductions unchanged.
It establishes both extracted `wasm_uleb_size` results from canonical encoding
lengths, relates 64-bit helper encoding to 32-bit section encoding, and proves
all size and address conversions nonwrapping. Canonical lengths are at most
five bytes in the relevant 32-bit range. The actual profile has small complete
modules; a conservative proved length bound of 312 bytes suffices for all
representability obligations.

The actual fixed 22-byte header, export-length ULEB, export count, name-length
ULEB, name-copy loop, seven fixed trailing envelope bytes, and six assembled
function bytes compose into one contiguous exact write. The generated four
instruction records are shown equal to the existing bitwise assembly plan.
`assemble_admitted_exact` proves the actual final assembler call terminates
with the expected body, status, and count. The returned helper values are
derived, never assumed.

The explicit fuel bound covers all actual phases: validation and copying each
need `name.size + 1`; unsigned size helpers need 10; unsigned writes need 11;
the four-instruction two-pass assembler needs `4 + 11 = 15`. These are separate
calls receiving the extracted function's same fuel argument, so their budgets
combine by maximum, not by summing them.

Complete capacity plus representable destination size excludes dropped fixed
stores as well as helper/copy stores. Actual offsets are related to natural
indices before composition. `bitwise_module_bytes` additionally proves, for
every module-byte index, both that the returned array contains that index and
that its optional lookup is `some` of the specified byte. Neither an absent
lookup nor an array default can masquerade as successful byte equality.

## Public consequences

- `bitwise_module_exact`: universal exact successful actual execution.
- `bitwise_module_contents`: exact complete output list and untouched suffix.
- `bitwise_module_output`: exact returned prefix, destination size, and suffix.
- `bitwise_module_bytes`: genuine in-bounds equality for every module byte.
- `bitwise_module_admitted`: the actual reported prefix passes the existing
  `BitwiseModule.acceptsModule` profile check.
- `bitwise_module_success`: loading and invoking that same actual prefix
  succeeds for every pair of 32-bit arguments with the shared mathematical
  AND/OR/XOR result.
- `bitwise_module_fuel_independent`: every sufficient budget gives the same
  complete returned output.
- `bitwise_module_insufficient_capacity`: for otherwise-valid profile inputs,
  insufficient complete capacity returns zero and the original destination;
  this pre-write path needs `max (name.size + 1) 10` fuel.

The new capacity-refusal result supplements the earlier invalid-operation,
invalid-length, and malformed-name laws. This change does not claim one total
all-input module-writer equivalence theorem or a minimal fuel bound.

## Checks and unchanged trust boundary

The existing equipped `TestLeanWasmBitwiseModuleFaithful` gate still regenerates
and compares the mechanically extracted writer first. It then invokes `tools/wasm_module_proof/check.py`, which rebuilds the entire
19-module local source closure in a fresh isolated directory with official
Lean 4.33.1, one worker, `-t0`, and a 2048 MiB memory limit. It checks the exact
16-root axiom inventory and `WasmBitwiseModuleExactControls.lean` at trust zero,
without using candidate `.olean` files. The committed audit inventory and
controls, as well as every local source module, are hashed before and after
checking. The retained name-copy controls run separately. Its existing 106 finite
source/compiler correspondence claims remain unchanged and separate from the
universal proof: 48 whole-buffer successes, 24 admissions, 33 refusals, and one
fuel-exhaustion case.

New controls exercise name lengths 1, 123, 124, 127, 128, and 256; both LEB
transition boundaries; all three operation tags; exact fit; distinct spare
suffix bytes; too-small capacity; invalid inputs; exhausted fuel; and wrong
count/header/name/function/suffix mutations. Large success fixtures instantiate
the universal actual-writer theorem and use its proved frame law; small raw
execution controls remain direct kernel evaluation. This avoids evaluating
hundreds of imperative array updates repeatedly in one kernel proof. A quantified application checks
the public all-input execution interface. Guarded axiom inspections constrain
the exported refinement, frame, admission, invocation, and refusal theorems to
the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.

No Oak writer, extractor, generated helper prefix, generated writer, existing image/source admission checker,
or existing model semantics change. No `sorry`, added axiom, `native_decide`,
private checker, or finite name enumeration is used to prove the universal
claims. Arrays retain the existing disjoint-span extraction model. This is not
a source parser or full compiler proof, a source-identifier grammar theorem,
an external WebAssembly implementation theorem, or native ISA execution proof.
