# Lean extraction

**Status: implemented subset.** `codegen/lean`, `oak build -lean out.lean`,
`Compilation.EmitLean`. The extraction is the roadmap's step 3 for the
verification experiment (`experiments/verification-poc`): a mechanical
translation of type-checked Oak into Lean 4 definitions, so that "this Lean
model is the Oak program" is a property of a small translator rather than of
a person reading two sources side by side.

## 1. What it is for

The experiment proves things about Lean models and relates them to compiled
Oak by running both on corpora. Before extraction, the model of the Oak
decoder was written by hand (`proof/OakText.lean`), and its fidelity to the
Oak source was an assumption checked only by corpus agreement. The extractor
produces `proof/OakTextExtracted.lean` from the same three Oak files the
compiler compiles. The remaining assumption between compiled Oak and the
extracted model is now "the compiler and this translator are correct", two
programs whose behavior is fixed and testable, and the hand-written model
becomes a proof intermediate whose relation to the extraction is itself
checkable.

## 2. The translation

The output is the shallow embedding the hand-written models use, so the
proofs written against them transfer.

| Oak | Lean |
| --- | --- |
| `u8` `u16` `u32` `u64`, `i8`..`i64` | `UInt8` .. `UInt64`, `Int8` .. `Int64` — wrapping arithmetic, the same widths |
| `Bool`, `()` | `Bool`, `Unit` |
| `[N]T`, `[]T`, `[*]T` | `Array T` — a value; a view is the array it views, a span is returned |
| `Name: type = struct { ... }` | `structure Name where ...` deriving `Repr, Inhabited, BEq` |
| `f: (p: T, s: [*]U): R` | `def f (p : T) (s : Array U) (fuel : Nat) : Option (R × Array U)` |
| local `x: T = e`, `x = e` | `let x : T := e`, `let x := e` (rebinding) |
| `arr[i] = v` | `let arr := arr.setIfInBounds i.toNat v` |
| `r.field = v` | `let r := { r with field := v }` |
| `arr[i]` | `arr.getD i.toNat zero` |
| `arr[lo:hi]` | `arr.extract lo hi` |
| `len(v)` | `v.size.toUInt32` |
| `u32(x)`, `i64(x)` | `x.toUInt32`, `x.toInt64` (or a typed literal) |
| `u32_trunc_u64(x)`, `u32_bits_i32(x)` | `x.toUInt32` — Lean's `toUIntN`/`toIntN` wrap and reinterpret exactly as the rows do |
| `u8_saturating_u32(x)`, `i8_saturating_i32(x)` | `if x > 255 then 255 else x.toUInt8`; the signed form clamps both ends |
| `a < b`, `a == b` | `decide (a < b)`, `a == b` — Bool throughout |
| `c ? { A } \| { B }` (statement) | `let (vars) ← if c then do A; pure (vars) else do B; pure (vars)` over the variables either arm assigns |
| `c ? a \| b` (value) | `if c then a else b` |
| `op ? \| 0 => a \| 1 => b \| _ => c` (integer constants) | `if op == 0 then a else if op == 1 then b else c`, in value and statement position; the last arm is the else |
| `while c { body }` | `def f.loopN (reads...) : Nat → Option (writes...)` with `0 => none`, recursing on the fuel |
| `g(args)` | `let (r, spans...) ← g args fuel`, hoisted before the statement; the span owners are rebound |
| `assert(c)` | `let () ← if c then pure () else none` |
| `E: type = A \| B: T` | `inductive E where \| A \| B (payload : T)` deriving `Repr, Inhabited, BEq, DecidableEq` (records derive the same four) |
| `Result[u32, E]`, `Option[Item]` | one inductive per instantiation the checker recorded, under its mangled name: `Result_u32_E`, `Option_Item` — the concrete tagged union the C backend emits (codegen/mono.go); templates are never emitted |
| `.B(x)`, `.Err(.Overlong)` | `(E.B x)`, `(Result_u32_E.Err E.Overlong)` — the type from the checked expression type, else the recorded variant resolution |
| `x ? \| .Ok(v) => a \| .Err(e) => b` (value) | `(match x with \| (.Ok v) => a \| (.Err e) => b)`; nested patterns, wildcards, and a whole-value binding as in the source |
| the same in statement position | `let (vars) ← (match x with \| (.Ok v) => (do ...; pure (vars)) \| ...)` over the variables the arms assign |
| a value-position arm with statements or calls | `let (r, vars) ← (if c then (do ...; pure (v, vars)) else (do ...))`, so nothing in an untaken arm is evaluated; arms that are plain terms stay a pure `if`/`match` |
| `a & b`, `a \| b`, `a ^ b`, `a << n`, `a >> n` | `a &&& b`, `a \|\|\| b`, `a ^^^ b`, `a <<< n`, `a >>> n` (see section 3 for the count) |
| `u8_checked_u32(x)` | `if x > 255 then Result_u8_Overflow.Err Overflow.Overflow else Result_u8_Overflow.Ok x.toUInt8` — the range test per signedness pair, then the wrapping conversion |
| `f[T]: (items: [*]T): ()` called as `f[u32](s)` | the checker's specialization `f_u32` (typechecker/genericfn.go), extracted like any function; the template itself is never emitted |
| `NAME: u32 = 16` at top level | `def NAME : UInt32 := (16 : UInt32)`, emitted when a function reads it; an initializer that calls a function fails closed |
| `TABLE: [256]u8 = [256]u8{ ... }` at top level, `[16]u32{ m[2], ... }` anywhere | `def TABLE : Array UInt8 := (#[...] : Array UInt8)`; an array literal is the Lean array literal, split into `++`-joined chunks of 128 beyond that length so a 2048-entry table elaborates |
| `view(&TABLE)` of a top-level constant | the constant's array value (a view is the array it views); `span(&TABLE)` would mutate the global and fails closed |
| `r.field[i] = v` | `let r := { r with field := r.field.setIfInBounds i.toNat v }` (one level of fields) |
| `^x` | `~~~x`, the complement over the operand's width |
| `subslice(v, start, n)` | `v.extract start.toNat (start.toNat + n.toNat)` — the window as the array it views (section 3 on the clamp) |
| `f32`, `f64` | `Float32`, `Float` — the host's binary32 and binary64 (section 3) |
| `1.5`, `0x1p-126` (a float literal) | `Float.ofBits (0x3FF8000000000000 : UInt64)`: the checker's own rounding of the text to its width (`typechecker.FloatLiteralValue`, correct from the exact value), spelled by bit pattern so Lean parses no decimal |
| `a + b`, `a * b`, `a / b`, `-x`, `a < b`, `a == b` on floats | the same operators on `Float`/`Float32`: one IEEE rounding each, `-x` the sign flip (`0 - x` would lose the sign of zero), comparisons and equality as IEEE (`NaN == NaN` is false) |
| `f64(x: f32)` | `x.toFloat`, exact |
| `f32_round_f64`, `fN_round_iM` | `x.toFloat32`, `x.toFloat`/`x.toFloat32` from the integer |
| `f64_bits_u64`, `u64_bits_f64`, `f32_bits_u32`, `u32_bits_f32` | `Float.ofBits`, `x.toBits`, and the `Float32` pair |
| `uM_saturating_fN`, `iM_saturating_fN`; `uM_trunc_fN`, `iM_trunc_fN` | `x.toUIntM`/`x.toIntM`: toward zero, clamped to the range, NaN to zero — the `saturating` row exactly; `trunc` traps out of range where this saturates (section 3) |
| `sqrt`, `abs`, `floor`, `ceil`, `round`, `is_nan`, `is_finite`, `is_infinite` | `Float.sqrt`, `.abs`, `.floor`, `.ceil`, `.round` (ties away from zero, as section 11.3.5), `.isNaN`, `.isFinite`, `.isInf`, and the `Float32` forms |

Functions are emitted callee-first. Every function takes `fuel : Nat` and
threads it to every loop and call; the corpus harness supplies a fuel above
any loop's iteration count, so `none` is a disagreement, never a pass.

## 3. The modeling choices, stated

Oak traps on an out-of-range read or write, on division by zero, on a
shift whose count reaches the operand width (`10-syntax.md` section 3b), and
on a `subslice` window that leaves its array. The extraction reads the
element type's zero, drops the write, divides to zero, shifts by Lean's
masked count, and clamps the window (`Array.extract` stops at the array's
end); a `trunc` conversion from a float that would trap out of range
saturates instead. This is sound for the direction the experiment proves — an Oak run
that produced a verdict took no trapping path, and on such runs the model
computes the same values — and it is what the hand-written models already
assume. A model of trapping as `none` would make every expression monadic;
the choice here keeps expressions pure and the proofs tractable.

**Floats are the host's.** `f32` and `f64` extract to Lean's `Float32` and
`Float`, whose operations are the compiled runtime's binary32 and binary64
IEEE operations — one rounding to nearest even per operation, no
contraction (each operation is its own call), subnormals kept — which is
what `20-types.md` section 11.3.3 fixes for Oak. Literals cross by bit
pattern, so Lean's decimal parser (which is not correctly rounded) never
takes part. What this does not give: `Float` is opaque to the kernel, so
`decide` cannot evaluate an extracted float program and the theorems about
float code stay against `Oak.Floats`, the abstract discipline model; the
extraction is the executable model an implementation is compared with, the
way the differential float witness compares the compiled C and the
interpreter. Intrinsics Lean has no exact counterpart for — `fma`,
`copysign`, `trunc`, `round_even`, `min`/`max` (2019 `minimum`/`maximum`),
`min_num`/`max_num`, `is_normal`, `total_order` — the `checked` rows into
integers, and the storage formats `f16`/`bf16`/`f8` fail closed rather than
approximate.

## 4. The subset, and what fails closed

Records and sum types of extractable fields and payloads, generic ADTs per
recorded instantiation; the fixed-width integers and Bool; arrays, views,
and spans of those; `while`; Bool conditionals, integer-constant matches,
and matches over variants in statement and value position, arms with
statements bound through do-blocks; calls to extracted functions (the
checker's specializations of generic templates included), `len`, `view`,
`span`, the widening constructors, the `trunc`/`bits`/`saturating`/`checked`
integer conversion rows, the bitwise operators and the complement,
`assert`, `subslice`; `f32` and `f64` with their literals, arithmetic,
comparisons, negation, the `round`/`bits`/`saturating`/`trunc` rows between
them and the integers, and the intrinsics of the table above; field
assignment and element assignment into a record's array field, one level
deep; array literals; top-level constants, including constant tables read
through `view`. The extraction closes over the roots'
callees, so a program that calls the standard library extracts the library
functions it reaches. Everything else — strings, generic templates
themselves, recursion, methods, extern functions, closures, the storage
float formats and the intrinsics named in section 3, `fma`, the `checked`
float rows, SIMD, FFI, assignment to a global — is an
error naming the construct. Nothing is approximated.

## 5. Where it runs

`experiments/verification-poc/proof/OakTextExtracted.lean` is generated and
committed; `TestLeanExtractionMatchesCommitted` regenerates it and fails on
drift (`OAK_LEAN_EXTRACT_UPDATE=1` rewrites it). `OakTextCompare.lean`
requires the extraction, the hand-written transliteration, the proved file
model, and compiled Oak to return one verdict on every corpus case and on
the replayed real certificate (729 cases at the time of writing). The opt-in
verification workflow and the certificate gate build and run it.

**The standard library.** `compiler/lean_stdlib_extract_test.go` extracts
whole packages — `varint`, `encoding`, `hash`, `random`, `uuid`, `float`
(the decimal text package, integer code over `f64` bit patterns), and `sort`
at `u32` — into `spec/lean/Oak/Stdlib/*Extracted.lean`, regenerating and
failing on drift the same way. A package's program is the core prelude
plus the flattened texts of its dependencies and itself (`stdlib.Flatten`);
the roots are the package's declarations plus a driver that instantiates
its generic templates (`sort_u32_span: (items: [*]u32): () {
sort_span[u32](items) }`), and `Compilation.EmitLeanRoots` closes over
their callees. The modules are imported from `spec/lean/Oak.lean`, so the
Lean job builds them. `FloatKernelsExtracted.lean` is the same test's
extraction of a program rather than a package: the ml shape of roadmap
item E4 — `dot_f32`, `sum_f32`, `sum_f64` in their stated left-to-right
order, `axpy_f32` into a span with its two roundings, `max_abs_f32`,
`widen_mean`, `quantize_u8`, `bits_roundtrip` — so a change to how floats
extract shows up as drift in a file a reader can compare with the source. Generated modules raise `maxRecDepth` and `maxHeartbeats`: an
unrolled compression function (SHA-256's sixty-four rounds) is one
definition with hundreds of binds, beyond the budgets sized for
hand-written code.

## 6. Theorems about the extraction

`proof/ExtractionScanner.lean` proves the scanner gate: `rup_token_scan`
states that on any text of at most 65536 bytes, from any cursor inside it,
with fuel above the text length, the extracted `rup_token` returns exactly
the token the proved `Scanner.scan` returns — kind, next cursor, start,
stop, magnitude, and sign — and that its five-word state has the model's
values. The proof follows the extraction's shape: one lemma per loop
(`loop1_spec` for whitespace against `countWhile space`, `loop2_spec` for
the word against `countWhile wordByte`, `loop3_spec` for the digits against
the bounded-decimal `walk`, including the pre-multiplication threshold
guard), then the assembly against `tokenAt` and `numeric`. Every `UInt32`
step is justified by a bound the guards establish, so no wrap occurs on
the paths the theorem covers; the axioms are `propext`, `Classical.choice`,
`Quot.sound` only. The scanner gate's corpus comparison remains as a
regression check, no longer as the evidence.

`proof/ExtractionDecoder.lean` proves the decoder. `CnfRel` states how
the extracted DIMACS loop's state — six `UInt32` counters, three bounded
arrays, the five-word scanner state, and the flags — represents the
model's `Cnf` record at a cursor: every scalar through `toNat`, every
array on the prefix its counter names, with the bounds the writes rely on
(a pending clause start below the pool length, the clause count below the
declared count, which the stage machine has checked against 256 by the
time it can write). `cnf_step` proves one iteration of the extracted loop
is one `cnfStep` of the model, on top of `rup_token_scan` for the token,
`rup_word_spec` for the `c`/`p`/`cnf` tests, and `rup_encoded_spec` for
the packed literal; `cnf_loop` runs it to `cnfLoop` with both fuels above
the remaining text. `ProofRel`, `proof_step`, and `proof_loop` do the same
for the LRAT phase, whose state adds the command table and the command
under construction (`CmdRel` relates the extracted record to the model's
`Command` field by field). `guard1_spec`/`guard2_spec` are the entry
guards, `cnfStart_rel` and `proofStart_rel` the two phase starts, and
`rup_text_check_spec` the assembly: on every pair of texts below the
`UInt32` range, with fuel above both texts twice over, the extracted
`rup_text_check` either returns `false` where the model's `layout` is
`none`, or calls the extracted `rup_stream_check` on arrays that represent
the model's `Layout` element for element (`LayoutRel`). Texts over the
65536-byte limit are covered too: both reject before scanning. Same
axioms as the scanner: `propext`, `Classical.choice`, `Quot.sound`.

What this buys: the decoder's corpus comparison is now a regression
check, and the one gap between the extraction's acceptance and
`OakTextRefinement.check_refines` is the stream checker — the extracted
`rup_stream_check` against `CertifiedStream.check` on a represented
layout.

The standard-library laws live next to the extractions, one file per
package, and are theorems about the extracted programs — so about the Oak
the compiler compiles, up to the extractor and the compiler being correct:

- `Oak/Stdlib/VarintLaws.lean`: the universal LEB128 round trip. `nbytes`
  and `byteOf` state the encoding in `Nat`; `size_loop`, `encode_loop`, and
  `decode_loop` relate the extracted loops to them by induction on the fuel,
  with every `UInt64`/`UInt32` wrap discharged by a bound the guards
  establish (`Nat.two_pow_add_eq_or_of_lt` turns the decoder's `|||` into
  the addition the invariant needs); `round_trip` assembles them for every
  `UInt64`, every destination of at least ten bytes, and every fuel above
  ten, `round_trip_all` closes the decided `roundTripHolds`, and
  `size_le_ten` bounds the encoding. The decided instances are kept as
  regression. Canonicity is proved as well (`canonical`): whatever
  `varint_decode` accepts at offset zero, the encoder writes back byte for
  byte with the same length. `decode_loop_any` runs the extracted decoder on
  arbitrary bytes and characterizes a successful exit — the value is the
  `groups` the consumed bytes spell, every byte but the last carries the
  continuation bit — and `nbytes_groups` identifies the length; the decoder's
  rejection of a zero final group after a continuation byte (`80 00` is
  over-long, `zero_padding_rejected`), added when the first version of this
  proof found the gap, is what makes the last group nonzero.
- `Oak/Stdlib/SortLaws.lean`: `sort_insertion_spec` — the extracted
  insertion sort returns a permutation (`Array.Perm`) of its input that is
  sorted (`SortedPrefix`), for every array below the `u32` index range and
  every fuel above twice its length, by induction over the two loops with
  `SortedExcept` (sorted but for one gap) as the inner invariant and the two
  stores shown to be `Array.swap`. Heap sort and `sort_span` are **not**
  covered: their extractions are unfaithful today — a loop body or `if` arm
  that changes the array only through a call does not return it, so the
  mutation is dropped (oak #186); `heap_extraction_gap` and
  `span_extraction_gap` are decided witnesses meant to stop compiling when
  the extractor is fixed and the file regenerated.
- `Oak/Stdlib/EncodingLaws.lean`: `hex_round_trip` — for every source below
  `2^31 - 2` bytes, either symbol case, a destination that holds exactly the
  encoding, and a decode destination that holds the source, `hex_encode`
  reports the encoded length and writes the symbols and `hex_decode` of them
  reports the source length and writes the source back; proved through the
  encoder's loop, both validation loops of `hex_scan`, and the decoder's
  loop, with the symbol and value tables read in the kernel
  (`decide +kernel`). Base64 and base32 have the RFC 4648 §10 vectors
  decided; their universal round trips and hexadecimal strictness remain.
- `Oak/Stdlib/RandomLaws.lean`: `random_next_spec` — the extracted step is
  the xoshiro256** reference `refNext` on the one-cell state; `random_below_lt`
  — a successful draw is below a non-zero bound; `random_range_mem` — a
  successful draw lies in `[low, high]`, including the full-range case.

All of these hold with `propext`, `Classical.choice`, and `Quot.sound` at
most; the kernel-decided facts use no axioms.

## 7. Next

- Fix the extractor's write set for spans rebound only through calls in
  loop bodies and `if` arms (oak #186), regenerate, and state the heap sort
  and pdqsort laws (`bit_length_some` is the first lemma they need); the
  universal base64 and base32 round trips and hexadecimal
  strictness (`hex_decode` accepts a string iff it is an encoding); the
  `uuid` version and variant bits against the extraction.
- The subset: strings and the text library, methods, and recursion;
  instantiations whose arguments are arrays or views; the `checked` float
  rows and `fma` once Lean carries them exactly.
The stream checker (`rup_stream_check` and the `rup_check` kernel under
it, seven and six loops, against `CertifiedStream.check`), which closes
the transfer of `check_refines` to the extraction; the string-level
corollary once `ByteArray.toList` has its data lemma; then the constructs
the verification programs need next (matches over records, the `checked`
rows), each added with its own fail-closed test. Integer-constant matches and the integer
conversion rows were added for the ml subset (op dispatch on constants,
`u64` index arithmetic narrowed to `u32`); the `checked` rows landed with
the standard-library round; `f32`/`f64` landed with the float round
(section 3), the storage formats and the inexact intrinsics still fail
closed.
