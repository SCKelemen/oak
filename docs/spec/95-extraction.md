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

Functions are emitted callee-first. Every function takes `fuel : Nat` and
threads it to every loop and call; the corpus harness supplies a fuel above
any loop's iteration count, so `none` is a disagreement, never a pass.

## 3. Three modeling choices, stated

Oak traps on an out-of-range read or write, on division by zero, on a
shift whose count reaches the operand width (`10-syntax.md` section 3b), and
on a `subslice` window that leaves its array. The extraction reads the
element type's zero, drops the write, divides to zero, shifts by Lean's
masked count, and clamps the window (`Array.extract` stops at the array's
end). This is sound for the direction the experiment proves — an Oak run
that produced a verdict took no trapping path, and on such runs the model
computes the same values — and it is what the hand-written models already
assume. A model of trapping as `none` would make every expression monadic;
the choice here keeps expressions pure and the proofs tractable.

## 4. The subset, and what fails closed

Records and sum types of extractable fields and payloads, generic ADTs per
recorded instantiation; the fixed-width integers and Bool; arrays, views,
and spans of those; `while`; Bool conditionals, integer-constant matches,
and matches over variants in statement and value position, arms with
statements bound through do-blocks; calls to extracted functions (the
checker's specializations of generic templates included), `len`, `view`,
`span`, the widening constructors, the `trunc`/`bits`/`saturating`/`checked`
integer conversion rows, the bitwise operators and the complement,
`assert`, `subslice`; field assignment and element assignment into a
record's array field, one level deep; array literals; top-level constants,
including constant tables read through `view`. The extraction closes over the roots'
callees, so a program that calls the standard library extracts the library
functions it reaches. Everything else — strings, generic templates
themselves, recursion, methods, extern functions, closures,
the floating-point rows, floats, SIMD, FFI, assignment to a global — is an
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
whole packages — `varint`, `encoding`, `hash`, `random`, `uuid`, and `sort`
at `u32` — into `spec/lean/Oak/Stdlib/*Extracted.lean`, regenerating and
failing on drift the same way. A package's program is the core prelude
plus the flattened texts of its dependencies and itself (`stdlib.Flatten`);
the roots are the package's declarations plus a driver that instantiates
its generic templates (`sort_u32_span: (items: [*]u32): () {
sort_span[u32](items) }`), and `Compilation.EmitLeanRoots` closes over
their callees. The modules are imported from `spec/lean/Oak.lean`, so the
Lean job builds them. Generated modules raise `maxRecDepth` and `maxHeartbeats`: an
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

`spec/lean/Oak/Stdlib/VarintLaws.lean` states the first law about a
library extraction: `roundTripHolds v` encodes `v` into a fresh ten-byte
buffer with the extracted `varint_encode` and decodes it with the extracted
`varint_decode`, and holds when the decoded value is `v` and the decoder's
`next` is the encoder's count. It is decided in the kernel for every
one-byte value (`round_trip_one_byte`, all 128), for the first value of
every encoding length from two to ten bytes, for the RFC example (`300` is
`AC 02`, `encode_300`), and for the largest `UInt64`; `overlong_tenth_byte_rejected`,
`truncated_rejected`, and `decode_stops_at_terminator` decide the canonical-form
rejections. These are kernel evaluations of the extracted program, not
corpus agreement, and they hold with no axioms. The universal statement
(every `UInt64`) needs an induction over the two loops and is stated as
remaining work in section 7.

## 7. Next

- The universal varint law: `∀ v, roundTripHolds v = true` by induction
  over `varint_encode.loop1` and `varint_decode.loop1` (the decided range
  covers every one-byte value and one value per longer length), then
  canonicity — a decoded value re-encodes to the same bytes — the same way;
  laws for `encoding` (each codec's round trip and strictness), `sort` (a
  sorted permutation), `random` (the reference xoshiro256** sequence), and
  `uuid` (the version and variant bits) against their extractions.
- The subset: strings and the text library, methods, and recursion;
  instantiations whose arguments are arrays or views.
The stream checker (`rup_stream_check` and the `rup_check` kernel under
it, seven and six loops, against `CertifiedStream.check`), which closes
the transfer of `check_refines` to the extraction; the string-level
corollary once `ByteArray.toList` has its data lemma; then the constructs
the verification programs need next (matches over records, the `checked`
rows), each added with its own fail-closed test. Integer-constant matches and the integer
conversion rows were added for the ml subset (op dispatch on constants,
`u64` index arithmetic narrowed to `u32`); the `checked` rows landed with
the standard-library round; every floating-point row still fails closed.
