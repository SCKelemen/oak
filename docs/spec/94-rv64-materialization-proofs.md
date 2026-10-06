# RV64 literal materialization proofs

`Oak.RiscVMaterialization` specifies and proves the signed 32-bit `li` expansion
implemented by `rv64SplitImmediate`, `rv64Base`, and `rv64Expand`. It complements
the [encoding](94-rv64-compressed-control-proofs.md) and
[layout](94-rv64-relaxation-proofs.md) proofs.

## Supported expansion

The current assembler accepts `li` values from −2³¹ through 2³¹−1. Values
outside that range are rejected before splitting. This is not a general
64-bit constant synthesizer.

| Condition | Expanded instructions |
| --- | --- |
| −2048 ≤ value < 2048 | `addi rd, x0, value` |
| Otherwise, low = 0 | `lui rd, high` |
| Otherwise | `lui rd, high; addiw rd, rd, low` |

Here `high = (value + 2048) / 4096` using floor division, and
`low = value − high × 4096`. The proofs connect these definitions to arithmetic
right shift and left shift, as used by Go. They establish exact reconstruction,
the signed 12-bit low range, the admitted upper range, and bounds showing that
all split intermediates fit in signed 64-bit arithmetic.

## Register semantics

The [RV64I specification](https://docs.riscv.org/reference/isa/unpriv/rv64.html)
defines LUI as a 32-bit upper-immediate result sign-extended to 64 bits. ADDIW
adds its signed immediate, keeps the low 32 bits, and sign-extends that result.
The model uses these bitvector operations and connects its word addition to
the existing `Oak.RiscV.addw` semantics.

This distinction matters near the positive endpoint. Materializing
`2147483647` uses upper part `524288` and low part `−1`. LUI first produces
`−2147483648`; ADDIW wraps the word result and obtains `2147483647`. Replacing
ADDIW with a 64-bit ADDI would produce the wrong value. Concrete Lean examples
record both outcomes.

The module proves, for every accepted literal:

- Expansion produces one or two instructions with encodable operands.
- Running the expansion produces the requested 64-bit sign extension,
  independently of the destination register's old value.
- LUI field masking and its 20-bit field concatenated with twelve zero bits
  give the same 32-bit word as the arithmetic model.
- Signed immediate field extension agrees with the admitted integer operand.
- Instruction-by-instruction register updates load the requested value into
  every nonzero destination, keep x0 zero, and preserve other registers.

These proofs use kernel-checked arithmetic and bitvector lemmas, without
native-evaluation or SAT axioms.

## Production evidence

`asm/rv64_materialization_lean_test.go` independently decodes and executes the
actual emitted byte stream for ADDI, LUI, ADDIW, C.NOP, C.LI, C.LUI, and C.ADDIW.
It checks every register afterward, with different initial sentinel values,
and checks expansion lengths, source/destination operands, and label placement.

The carry sweep covers every signed 12-bit remainder at ten upper-part
boundaries: 36,864 distinct valid literals, for x2 and x8, both with and without
RVC. That is 147,456 emitted function streams. A further 2,304 boundary streams
cover all 32 destination registers and all seven instruction forms.

The Lean oracle checks 436 production claims: split results, complete expansion
traces, actual compressed/uncompressed bytes executed by the Lean decoder,
and refusal of values outside signed 32-bit range, including host-integer
extremes. Decoder checks also reject truncated instructions, changed register
fields, and instructions outside the materializer subset.

```sh
cd spec/lean
lake build Oak.RiscVMaterialization
cd ../..
OAK_REQUIRE_RV64_LEAN=1 go test ./asm -run '^TestRV64Materialization' -count=1
```

The formal workflow requires the Lean oracle. Go-only environments still run
the byte-stream and register-state checks when Lake is unavailable.

## Remaining boundary

The expansion and register-value model are proved for all admitted literals.
Go-to-Lean refinement and encoder correspondence remain bounded evidence.
The small decoder is an oracle for this materializer subset, not a general ISA
decoder or an external Sail bridge. PC advancement, memory, traps, loading,
linking, and arbitrary 64-bit literal synthesis are outside this module.
