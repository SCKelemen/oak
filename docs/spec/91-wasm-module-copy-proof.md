# Extracted complete-Wasm writer: exact name copy

`Oak.WasmBitwiseModuleCopy` proves a universal successful-copy contract for
`wasm_bitwise_module.loop2` in the mechanically generated
`Oak.WasmBitwiseModuleExtracted`. It imports the existing validation proof and
`Oak.WasmAssemblerBytes`; no writer, extraction, checking, or model semantics
change is involved.

## Contract and bounds

For arbitrary name and initial destination arrays, name position `pos`, and
fuel, the whole-copy theorem requires:

- `name.size < 2^32` and `dst.size < 2^32`;
- `pos.toNat + name.size ≤ dst.size`;
- `name.size + 1 ≤ fuel`.

It proves the actual extracted loop returns
`some (writeBytes dst pos.toNat name.toList, name.size.toUInt32)`.
`writeBytes` is the pre-existing mathematical list writer, whose exact indexed
contents, unchanged size, and suffix semantics were already established in
`WasmAssemblerBytes`. The new proof unfolds the generated loop one step at a
time and inducts on the remaining source suffix. It assumes no returning run.

The stronger `bitwise_name_copy_suffix_exact` starts after any consumed prefix
`pre`, writes precisely the remaining name suffix at `pos.toNat + pre.length`,
and needs only `remaining.length + 1` fuel. The final guard is included in both
budgets. Source index, destination address, and loop increments are related to
natural arithmetic at every step by `bitwise_name_copy_index`. Its conclusions
include actual source and destination bounds and nonwrapping u32 sums and
increments. The fit hypothesis rules out stores dropped by `setIfInBounds`;
the represented actual name length rules out `getD` defaults.

## Exported results

- `bitwise_name_copy_index`: safe source/store addresses and exact increments.
- `bitwise_name_copy_suffix_exact`: exact arbitrary remaining-suffix execution.
- `bitwise_name_copy_exact`: complete exact name copy and final index.
- `bitwise_name_copy_contents`: exact optional lookup at every index and unchanged
  destination size, including the entire untouched prefix and suffix.
- `bitwise_name_copy_suffix`: the copied name followed by the original suffix.
- `bitwise_name_copy_bytes`: each genuine source byte appears at an explicitly
  in-bounds output index; absent optional lookups cannot count as byte agreement.
- `bitwise_name_copy_frame`: equality of both the prefix before the copy and the
  suffix after it, for arbitrary nonuniform initial destination contents.
- `bitwise_name_copy_fuel_independent`: all sufficient budgets agree.

The byte-copy theorem intentionally does not require ASCII validity: the
complete writer validates that earlier, in the separately proved scan.

## Checks

`WasmBitwiseModuleCopyControls.lean` contains kernel-checked positive examples
for nonuniform prefix/suffix sentinels, partial source consumption, empty names,
exact capacity, and arbitrary byte values. Negative controls reject a wrong
prefix byte, copied byte, suffix byte, or final index. A missing final guard
returns `none`, distinct from ordinary refusal or a successful partial copy.
Two explicit excluded-domain controls demonstrate the raw array model's
out-of-bounds default read and dropped store; they are not safe-copy claims.
A quantified application checks the public theorem without evaluating a finite
output. Guarded axiom inspections permit only the reported standard Lean axioms
(`propext`, `Quot.sound`, and `Classical.choice` where used).

The existing `TestLeanWasmBitwiseModuleFaithful` gate now builds the copy module
and runs these controls. It still checks fresh extraction correspondence and
retains its existing, separate finite complete-module corpus. Official Lean
4.33.1 checks the proof and controls; no `sorry`, custom axiom, or
`native_decide` is introduced.

## Remaining boundary

This is a universal compositional result about the actual name-copy loop. It
is not yet a complete successful module-envelope theorem. The complete writer's
size arithmetic and capacity preflight, its fixed header/section stores, the
ULEB helper outcomes at their concrete offsets, and the final assembler call
must still be composed. Existing `WasmAssembler.assemble_exact` and
`BitwiseFunction.emitted_function_success` provide relevant separate ingredients;
they do not themselves discharge that composition. Full module output,
module admission, source compilation, and runtime behavior remain unclaimed.
Arrays continue to model disjoint Oak spans, with the existing compiler and
extractor correspondence boundary unchanged.
