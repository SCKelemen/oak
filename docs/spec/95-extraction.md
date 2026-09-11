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

Functions are emitted callee-first. Every function takes `fuel : Nat` and
threads it to every loop and call; the corpus harness supplies a fuel above
any loop's iteration count, so `none` is a disagreement, never a pass.

## 3. Two modeling choices, stated

Oak traps on an out-of-range read or write and on division by zero. The
extraction reads the element type's zero, drops the write, and divides to
zero. This is sound for the direction the experiment proves — an Oak run
that produced a verdict took no trapping path, and on such runs the model
computes the same values — and it is what the hand-written models already
assume. A model of trapping as `none` would make every expression monadic;
the choice here keeps expressions pure and the proofs tractable.

## 4. The subset, and what fails closed

Records of extractable fields; the fixed-width integers and Bool; arrays,
views, and spans of those; `while`; Bool conditionals in statement and value
position; calls to extracted functions, `len`, `view`, `span`, the widening
constructors, and `assert`; field assignment one level deep. Everything
else — strings, ADTs other than records, matches over variants, generics
that survive checking, recursion, methods, extern functions, closures,
`subslice`, the explicit conversions, floats, SIMD, FFI — is an error
naming the construct. Nothing is approximated.

## 5. Where it runs

`experiments/verification-poc/proof/OakTextExtracted.lean` is generated and
committed; `TestLeanExtractionMatchesCommitted` regenerates it and fails on
drift (`OAK_LEAN_EXTRACT_UPDATE=1` rewrites it). `OakTextCompare.lean`
requires the extraction, the hand-written transliteration, the proved file
model, and compiled Oak to return one verdict on every corpus case and on
the replayed real certificate (729 cases at the time of writing). The opt-in
verification workflow and the certificate gate build and run it.

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

## 7. Next

The stream checker (`rup_stream_check` and the `rup_check` kernel under
it, seven and six loops, against `CertifiedStream.check`), which closes
the transfer of `check_refines` to the extraction; the string-level
corollary once `ByteArray.toList` has its data lemma; then the constructs
the verification programs need next (matches over records, the `checked`
rows), each added with its own fail-closed test. Integer-constant matches and the integer
conversion rows were added for the ml subset (op dispatch on constants,
`u64` index arithmetic narrowed to `u32`); `checked` conversions and every
floating-point row still fail closed.
