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
| `g(args)` | `let (r, spans...) ← g args fuel`, hoisted before the statement; the span owners are rebound — and such a rebinding inside a loop body or a conditional arm is a write of that loop or arm, so the owner is in the tuple the helper returns (oak #186) |
| `s: [*]T = items[a:b]`, `s: [*]T = span(&buf)` (a writable window) | `let s := items.extract a b` plus `let s_lo : Nat := a`; after every statement that rebinds `s` (a store, a call), the window is written back — `let items := (items.extract 0 s_lo) ++ s ++ (items.extract (s_lo + s.size) items.size)`, or `let buf := s` for a whole span — transitively through nested windows, and the owner joins the enclosing write sets, because in Oak the window aliases the owner's storage |
| `assert(c)` | `let () ← if c then pure () else none` |
| `name: theorem (params) { e }` | the `def` of the function it is, then `theorem name_holds (params) (fuel : Nat) : name params fuel = some true` with the automatic script of `125-verification.md` §5; the module imports `Std.Tactic.BVDecide` when it states one |
| `E: type = A \| B: T` | `inductive E where \| A \| B (payload : T)` deriving `Repr, Inhabited, BEq, DecidableEq` |
| `R: type = struct { h: [8]u32, n: u32 }` | `structure R where ...` deriving `Repr, BEq, DecidableEq` with an explicit `instance : Inhabited R := ⟨{ h := Array.replicate 8 0, n := 0 }⟩`: the zero record an uninitialized `r: R` denotes, a fixed array field being its N zeroes rather than the empty array `deriving Inhabited` would choose (section 3) |
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

**Windows and records are values, made to agree.** A writable span is
an `Array` value, so a window of an owner (`items[a:b]`, `span(&buf)`)
would be a copy where Oak has an alias; the extraction restores the
agreement by writing every rebound window back into its owner after the
statement that rebound it (section 2), which is exactly the owner's state
the compiled program has, because the borrow checker forbids touching the
owner while the window is live. A record's default is its zero record with
every fixed array field at its declared length; with Lean's derived
`Inhabited` the fields would be empty arrays and every element store into
an uninitialized record would be dropped as out of range — SHA-256 hashed
an empty block until this was made explicit. Both were found by the
faithfulness check of section 5, not by the drift test.

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

**Faithfulness, executed.** `compiler/lean_stdlib_faithful_test.go`
builds one Oak module and one Lean driver over the committed extractions
from a fixed-seed corpus — the heap, pdq and insertion sorts, LEB128
encode and decode, hex and base64 round trips, xoshiro256** draws,
CRC-32C and SHA-256 — runs the compiled program and `lake env lean --run`,
and compares the two outputs byte for byte (336 lines). The drift test
says the committed text is current; this says the text means what the
compiled code does. It skips without a Lean toolchain and runs in the
Formal Verification workflow after the Lean build. It is what oak #186
needed: three faithfulness gaps (spans rebound through calls, windows never
written back, zero records with empty array fields) each passed the drift
test and each fails this one.

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

The standard library's per-package status — which packages extract, which
laws are proved universally, which are decided, what the faithfulness
harness covers, and the benchmark ratios — is kept as one table in
`stdlib/VERIFICATION.md`; this section holds the theorems themselves.

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

`proof/ExtractionRUP.lean` proves the RUP kernel under the stream checker.
`ScratchRel` states how the kernel's assignment bytes represent a model
`Scratch` on the declared variables (0, 1, 2 for unassigned, false, true;
unassigned above the count), `TableRel` how the 256-slot start, length,
and liveness arrays represent a `LiveTable.Table`. Each of the extracted
loops is proved against a function on lists — `rup_loop1_spec` zeroes the
scratch, `rup_loop2_spec` decides `slotOK` over the hints (`slotOK_db`
shows that is the model's `(db id).isSome` on a live slot),
`rup_loop6_spec` is membership in the clause's prefix, `rup_loop5_spec` is
`scan`, the clause walk with the kernel's stop-at-satisfied and
skip-duplicates behavior, `rup_loop3_spec` is `assume`, the negated-target
walk, and `rup_loop4_spec` is `walk`, the chain — and each list function is
proved to be the model's: `classify_of_scan` (the walk's outcome is
`ClauseClassifier.classify`, through a permutation of the unique
survivors), `prepare_spec` (`assume` clashes exactly when
`PropagationChain.prepare` does and otherwise yields its scratch), and
`chain_walk` (`walk` is `chain`'s `isSome`). `rup_check_spec` assembles
them: on the inputs the stream checker hands the kernel — a pool of at
most 4096 literals all below the variable count, the 256-slot tables, a
target and hints drawn from it, hints that are live slots, a 64-byte
scratch, fuel above 8800 — the extracted `rup_check` returns exactly
`(PropagationChain.check variables db target refs).isSome` for the live
table's database, the decoded target, and the one-based hint ids. Same
axioms again.

`proof/ExtractionStream.lean` proves the stream checker and closes the
chain. `StreamRel` states how the loop's state — the 256-slot tables, the
last addition id, the refutation flag — represents a `CertifiedStream.State`;
the seven loops are proved against list functions as before (the table
zeroing, the literal check against the model's pool guard, the initial
clauses against `LiveTable.initialTable` and the model's empty-clause scan,
the hint mapping as `refOK` over the reference slice, the clause copy as
`targetList` = `clauseAt`, the deletions as `clearAll`, which
`deleteIDs_clearAll` identifies with the model's sequential `deleteIDs`),
and the command loop is proved against `CertifiedStream.commands` one
command at a time through the model's own case split (`command_add_check`
and its siblings), with `rup_check_spec` discharging the kernel call: the
copied clause is the pool's clause, the mapped hints read back are the
reference slice, and the kernel's answer is `PropagationChain.check`'s.
`rup_stream_check_spec` states the result: on every layout the decoder can
hand over (`LayoutRel`, arrays inside the fixed capacities), with fuel
above 9100, the extracted `rup_stream_check` returns exactly
`CertifiedStream.check raw`.

`rup_text_check_sound` is the composition and the end of the chain: for
any pair of texts below the `UInt32` range, with fuel above twice both
lengths plus 9101, if the extracted `rup_text_check` returns `true` then
the model's layout of those texts exists and its initial database is
unsatisfiable — `CertifiedStream.check_sound` transported to the
compiler's extraction of the whole Oak program. Same axioms:
`propext`, `Classical.choice`, `Quot.sound`.

What this buys: the scanner, decoder, kernel, and stream corpus
comparisons are all regression checks now. What remains between the
compiled binary and the theorem is the extractor's fidelity to the
compiled program and the compiler itself, which the extraction lane's
own tests and the differential witnesses cover, and the string-level
corollary (the theorem is over byte arrays; `ByteArray.toList` lacks its
data lemma).

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
  stores shown to be `Array.swap`. `sort_heap_spec` — the extracted heap sort
  returns a sorted permutation for every array below `2^31` elements and
  every fuel above `3 n + 3`: `sift_loop_spec` keeps the heap edges above a
  floor except at the hole (`SiftInv`, with the hole's parent bounding its
  children once it has moved) and only permutes positions below `end`,
  `heap_build_spec` lowers the floor to zero, `heap_extract_spec` keeps a heap
  below a sorted tail that dominates it (`heap_root_max` moves the maximum
  out). For `sort_span`: `writeback_perm` — writing a permutation of the
  window `items[lo:hi]` back over it is a permutation of `items` for every
  `lo` and `hi`; `sort_span_small` — below thirteen elements the result is a
  sorted permutation (it is insertion sort); `sort_span_budget_zero` — with
  the depth budget spent the whole span is heap sorted, so the fallback path
  is a sorted permutation for every array below `2^31`. The pattern-defeating
  path beyond the threshold is decided on twenty-four-element sorted,
  reversed, all-equal, organ-pipe, few-distinct and sawtooth inputs and a
  budget of one on the reversed sixteen; its universal laws need the
  range-stack invariant and the in-bounds proof of every swap (the extraction
  drops an out-of-range store, so permutation itself depends on them).
- `Oak/Stdlib/EncodingLaws.lean`: `hex_round_trip` — for every source below
  `2^31 - 2` bytes, either symbol case, a destination that holds exactly the
  encoding, and a decode destination that holds the source, `hex_encode`
  reports the encoded length and writes the symbols and `hex_decode` of them
  reports the source length and writes the source back; proved through the
  encoder's loop, both validation loops of `hex_scan`, and the decoder's
  loop, with the symbol and value tables read in the kernel
  (`decide +kernel`). Hexadecimal strictness is proved as well:
  `hex_decode_ok_iff` — for every source below `2^32 - 4` bytes and a
  destination that holds half of it, `hex_decode` succeeds exactly when the
  source has even length and every byte is a hexadecimal digit (`AllDigits`),
  otherwise reporting `InvalidLength` or `InvalidCharacter`; the proof tracks
  bit four of the validation scan's accumulated `|||` (`Bit4`), which the
  value table sets on every non-digit and only there. `hex_decode_encode` —
  whatever the decoder accepts, re-encoding the decoded bytes in lower case
  writes the source back with its letters lowered (`lowerHex`), so the
  decoder accepts exactly the encodings, up to case. Base32 has the RFC 4648
  §10 vectors decided; its universal round trip remains.
- `Oak/Stdlib/Base64Laws.lean`: `base64_round_trip` — for every source below
  `2^31 - 8` bytes, either alphabet (standard or URL), padded or not, a
  destination that holds exactly the encoding (`encSize`), and a decode
  destination that holds the source, `base64_encode` reports the encoded
  length and `base64_decode` of its output reports the source length and
  writes the source back. `b64_encode_spec` characterizes the encoder's
  output position by position (symbols below `symCount`, pads after, the
  rest untouched) through the three-to-four group loop and its one- and
  two-byte tails; `unpadded_length_spec` shows the decoder's padding strip
  counts exactly the pads written; `b64_scan_spec` shows the validation
  scan's accumulated `|||` stays below 64 on symbols; `decoded_size_spec`
  and the group loop with its tails close the decode. The 24-bit word
  identities are bit-vector facts (`bv_decide`); the symbol tables are read
  in the kernel.
- `Oak/Stdlib/PercentLaws.lean`: `percent_round_trip` — for every source
  below the size limit and every keep set that holds no `%` (and no `+`
  when `+` decodes as a space), `percent_encode` reports the length of the
  blocks it writes (`encFrom`: a kept byte as itself, any other as `%` and
  two upper-case digits) and `percent_decode` of those bytes reports the
  source length and writes the source back. `kept_spec` relates the
  keep-set scan to `unres || anyFrom`; `percent_encode_loop` characterizes
  the encoder position by position; `decoded_size_loop` shows the
  validation scan stays valid on the blocks (every `%` has three bytes and
  two digits below sixteen); `percent_decode_loop` reads each block back,
  the two digits through `upper_digits_join'` (decided over the 256 bytes).
- `Oak/Stdlib/UuidLaws.lean`: for every one-cell generator state and every
  sixteen-byte destination, `uuid_v4_spec` — `uuid_v4` succeeds and the
  value reports version 4 (`uuid_version`) and the RFC variant
  (`uuid_variant`); `uuid_v7_spec` — for every timestamp below `2^48`,
  `uuid_v7` succeeds, reports version 7 and the RFC variant, and
  `uuid_v7_millis` recovers the timestamp; `uuid_format_parse` — for every
  sixteen-byte value, `uuid_format` writes exactly `textOf upper x` (two
  digits per byte in the requested case, hyphens at 8, 13, 18, 23) and
  `uuid_parse` reads it back to the value, in either case. Every loop in the
  package runs a fixed number of times, so the proofs unroll the extracted
  loops by simplification; the byte identities are `bv_decide` facts, the
  two table facts (a symbol decodes to its nibble, a symbol is never a
  hyphen) are read in the kernel over `Fin 256`, and writing every slot of a
  fixed-size destination in order is shown to yield a literal array
  (`overwrite36`, `overwrite16`) that the parser reads at literal positions.
- `Oak/Stdlib/RandomLaws.lean`: `random_next_spec` — the extracted step is
  the xoshiro256** reference `refNext` on the one-cell state; `random_below_lt`
  — a successful draw is below a non-zero bound; `random_range_mem` — a
  successful draw lies in `[low, high]`, including the full-range case.

All of these hold with `propext`, `Classical.choice`, and `Quot.sound` at
most; the kernel-decided facts use no axioms.

## 7. Next

- State the pdqsort laws beyond the insertion threshold and the exhausted
  budget: the range-stack invariant (ranges disjoint, everything between them
  in final position, every swap in bounds) over `sort_span_budget.loop1`,
  with `writeback_perm` and the heap and insertion laws as the leaves; the
  universal base32 round trip (the base64 proof's shape, with five-to-eight
  groups and four tail lengths); strictness for base64 (`base64_decode`
  accepts a string iff it is a canonical encoding) and for percent-decoding
  (accepted iff every `%` starts two hexadecimal digits) as
  `hex_decode_ok_iff` does for hexadecimal; the SHA-256 and CRC-32C extractions against
  reference definitions.
- The subset: strings and the text library, methods, and recursion;
  instantiations whose arguments are arrays or views; the `checked` float
  rows and `fma` once Lean carries them exactly.
The string-level corollary of `rup_text_check_sound` once
`ByteArray.toList` has its data lemma; then the constructs
the verification programs need next (matches over records, the `checked`
rows), each added with its own fail-closed test. Integer-constant matches and the integer
conversion rows were added for the ml subset (op dispatch on constants,
`u64` index arithmetic narrowed to `u32`); the `checked` rows landed with
the standard-library round; `f32`/`f64` landed with the float round
(section 3), the storage formats and the inexact intrinsics still fail
closed.
