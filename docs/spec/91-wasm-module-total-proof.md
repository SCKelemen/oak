# Extracted complete-Wasm writer: universal total outcomes

This is a separate follow-on to the successful-domain proof frozen at
`d2edc7da02a4e90b186397965a641c07830df12a` (tree
`d89c978d8094e13ecdd4819738d63a71b458ec78`). The prior Lean source, controls,
audits, writer, extractor, and checker are unchanged.

## Total API contract

`Oak.WasmAssembler.bitwise_module_total` quantifies over arbitrary destination
and name arrays, every `UInt32` operation tag, and every natural fuel value.
Its only premises are:

- `dst.size < 2^32`;
- `name.size < 2^32`;
- `257 ≤ fuel`.

It proves the actual extracted
`wasm_bitwise_module dst op name fuel = some (moduleResult dst op name)`.
There is no premise that the writer, a helper, or a loop returns.

`moduleResult` has no fuel parameter and does not call or inspect the extracted
writer. Its independent branches test:

1. Operation tag is 1, 2, or 3, as the interval `1 ≤ op ≤ 3`.
2. The actual natural name length is between 1 and 256.
3. Every actual name byte has natural value between 1 and 127.
4. The entire independently specified `namedModuleBytes` list fits the
   destination's natural size.

When all four conditions hold, it returns the exact module byte count and
`writeBytes dst 0 bytes`, with `bytes` supplied by the existing independent
`BitwiseModule.namedModuleBytes` specification. Otherwise it returns exactly
`(0, dst)`. The complete original destination is therefore retained on every
ordinary refusal, regardless of its original contents.

## Composition, order, and genuine bounds

The proof first splits on operation and natural length. An invalid operation
uses the existing early-operation theorem. An invalid natural length uses
`module_length_guard_iff` and the existing early-length theorem.
Representability makes the natural-to-`UInt32` length conversion exact,
including excluded lengths much larger than the uniform fuel budget. These
branches do not apply a scan theorem or assume that an arbitrarily large name
was scanned.

Only after establishing `name.size ≤ 256` does the proof invoke validation.
`module_name_bytes_iff` connects the independent natural-byte test to the
existing validator specification. Failed validation produces
`module_bad_name_witness`: an actual index `j`, a proof `j < name.size`, and
`name[j] = 0 ∨ 128 ≤ name[j]`. The existing indexed malformed-name refusal
theorem then derives the actual unchanged-buffer run. Neither an absent
lookup nor a `getD` default can supply that witness.

With valid bytes, complete capacity splits the two remaining cases. The
successful case invokes the frozen exact successful-module theorem; the
short-capacity case invokes its pre-write refusal theorem. Both derive all
actual helper outcomes. The old success theorem supplies the in-bounds byte
and frame laws, so the new `writeBytes` specification does not license dropped
stores or other out-of-bounds masking.

The uniform bound 257 covers validation and copying of every admitted name
(at most 256 bytes plus the final guard), as well as the smaller helper and
assembler budgets. It does not assert a minimal budget for each individual
input. Guard-only refusals still work at zero fuel.

## Consequences

- `bitwise_module_terminates`: every representable input has an actual returned
  result at sufficient fuel; extraction exhaustion is excluded.
- `bitwise_module_refusal_iff`: actual zero-count refusal with the original
  destination is equivalent to failure of the explicit four input conditions.
- `module_success_count`: successful counts are exact natural lengths without
  wrapping and are nonzero, so success cannot alias ordinary refusal.
- `module_result_size`: the returned destination always has the original
  allocated length, on both success and refusal.
- `bitwise_module_total_fuel_independent`: any two fuel values at least 257
  yield the same complete actual result for every representable input.

The existing successful-domain admission and invocation consequences remain
available unchanged. This follow-on does not broaden them to a source parser,
full compiler, arbitrary Wasm program, external Wasm implementation, native
ISA, source identifier grammar, or extractor-correctness theorem. The arrays
retain the existing disjoint-span extraction boundary.

## Controls and source validation

`WasmBitwiseModuleTotalControls.lean` tests both inhabited success and refusal
branches, all three valid operation tags, invalid tags 0, 4, and `2^32 - 1`,
empty and oversized names, byte boundaries 1/127 and 0/128/255, a late malformed
byte, exact capacity versus one byte short, and a 256-byte valid name at fuel
256 versus 257. The large exhausted-scan control uses a small structural
induction over fuel rather than repeatedly evaluating an imperative literal
array. Concrete names of length 257 and 4096 and a symbolic upper representable
length verify guard-only refusal at zero fuel. Mutation controls exclude an
always-refusing or silently truncating specification.

The new `tools/wasm_module_total_proof/check.py` is a superset gate. It leaves
the original gate implementation unchanged, reuses its fail-closed local-import
scanner and axiom-report parser, and fresh-builds the 20-module local closure
once with official Lean 4.33.1, one worker, trust zero, warnings as errors, and
a 2048 MiB memory limit. Its empty build directory is the complete `LEAN_PATH`;
no candidate `.olean` cache is imported. It checks both exact committed root
inventories (16 old successful-domain roots and 10 new total-outcome roots),
then both old and new control files. All local Lean inputs and both gate
implementations are hashed before and after checking.

Minimal existing Go gate wiring selects that superset. The existing extraction
comparison, name-copy controls, and 106 finite source/compiler correspondence
claims remain unchanged. Both Python negative-control suites run; the new
suite checks loss of old source coverage, changed/missing/duplicate/unexpected
root reports, forbidden axioms, and wrong toolchain versions.

Development checks reused the frozen successful-domain proof's checked
dependency `.olean` files with the official toolchain, compiling only the new
module and its controls/audit. That reuse is development evidence, not a fresh
source-closure check. Independent fresh-source validation of the exact frozen
follow-on revision must be recorded separately. No Go build or publication
is implied by the development checks.

No `sorry`, custom axiom, `native_decide`, private checker, returned-run
assumption, or finite enumeration replaces any universal result.
