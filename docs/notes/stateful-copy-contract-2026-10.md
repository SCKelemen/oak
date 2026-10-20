# Stateful copy: source closure, representation, and proof contract

## Status and scope

This is the proposed shared interface for the next bounded stateful slice, based
on local commit `05117599d8756c135aa9dfd406ef76bcdd0f10bd`, tree
`aa82145305a8149b1561ab6f4bb1ad0760632a01`. It changes no production semantics,
checker, acceptance profile, or proof. Its executable fixtures establish current
source/type/layout facts and record current refusals. They do not admit a copy
artifact or prove arbitrary-input execution.

The workload is one real, non-inlined call from `copy_checked` to the imported
`bytes.copy_into`. The callee returns its actual `Result[u32, bytes.CopyError]`;
the caller retains `len(src)` across the call and matches both the discriminant
and success payload to return a Bool. A scalar-only replacement for the callee,
an inlined copy loop, or a successful C fallback does not meet the future target
milestone. The finite C/interpreter checks below are explicitly source
correspondence evidence, independent of that direct-call requirement.

## 1. Frozen source and binding interface

The canonical caller is the complete file
`compiler/testdata/stateful_copy/main.oak`:

```oak
package main
import("bytes")

pub copy_checked: (dst: [*]u8, src: []u8): Bool {
  n: u32 = len(src)
  copied: Result[u32, bytes.CopyError] = bytes.copy_into(dst, src)
  copied ? | .Ok(count) => count == n | .Err(error) => false
}
```

This syntax is exercised through the real package loader and `Compilation.Check`,
not an audit-only sketch. The fixture module identity is
`example.com/stateful-copy-contract`, with `oak 0.1.0`. The package loader imports
the real embedded `bytes` package and requests the core prelude, not the
compatibility flat `import(std)` library.

The **source closure** must carry all of the following, not just a callee name or
digest:

1. Original caller bytes/path, module bytes and root package identity.
2. Original `stdlib/bytes.oak` and `stdlib/std.oak` bytes, resolved stdlib package
   identity, import edges, export/visibility decisions, and the core-prelude
   selection. Do not identify the dependency through a local package that happens
   to expose the same spelling.
3. The resolved declaration identity `bytes__copy_uinto`, resolved error identity
   `bytes__CopyError`, the checked parameter/result types, the `std` prelude's
   actual `Result[T,E]` template, and its instantiation with
   `[u32, bytes__CopyError]`.
4. The actual callee body and its typed nodes: the length binding, short-capacity
   guard, byte-indexed loop, and both Result constructors. Bind the caller's
   single call occurrence to this declaration and retain the post-call use of
   `n`. Bind builtin `len`, indexing, integer arithmetic and match semantics too.
5. The exact checked AST/authority and projected OptIR/CFG identities when those
   phases support this closure. Record compiler/extractor revisions and options,
   target description, and the distinction between loaded dependency bytes and
   the reachable executable closure.

The loader currently loads more declarations than the two reachable functions.
Those source files remain part of dependency identity; the future bounded
artifact must explicitly select and justify the two-function executable closure.
`ModuleInfo` records package/import/export facts but does not itself preserve
every original dependency byte. A future artifact manifest must retain those
bytes separately and rerun/reconcile resolution. A digest pins bytes; it does
not prove that parsing, package resolution, typing, borrowing or extraction
preserved their meaning.

Frozen SHA-256 identities:

| Input | SHA-256 |
|---|---|
| Caller file | `b7e0745da1b388e29c281c2f15d89ef4061ab33f1c5eb55f8dda7297d87f95f5` |
| `stdlib/bytes.oak` | `e4da6755200dbcfe409f9ec11ea928515d7fcd91838ba63e284d1c9f30603f7c` |
| `stdlib/std.oak` | `10bbc09408ba76fccbac59f06936411e29eff8b81777c788b2b77b8e57eaa0e7` |
| `BytesExtracted.lean` | `fab665c9cf89f45fca96fb4540b727fb3210db6e8b7f243ec9813f735b517631` |

`TestStatefulCopySourceClosure` checks embedded bytes against disk and these
dependency hashes, real module resolution, the production monomorphic
instantiation, the caller's live value and direct call, and the resolved callee
body against a fresh parse of the actual package. `TestLeanStdlibExtract/bytes`
regenerates the existing extraction and compares its complete bytes. The latter
still is a finite extractor consistency check, not a verified frontend theorem.

## 2. Concrete native representation

Derive this through `compiler.specializeInstantiations` using the checked
typechecker's `ADTInstantiations`, then `nativegen.Composites`, which uses
`adtLayoutOf` and `semir.TaggedUnionLayout`. Do not invent a monomorphic ADT in
the fixture. `Check` records generic ADT instantiations; the native production
path materializes their declarations in a separate step.

The instantiated type is `Result_u32_bytes__CopyError`.

| Value/type | Size / alignment | Concrete representation |
|---|---|---|
| `bytes__CopyError` | 4 / 4 bytes | u32 tag at byte 0; `DestinationTooSmall = 0`; no payload |
| Concrete Result | 8 / 4 bytes | outer u32 tag at byte 0; payload union at byte 4 |
| `Ok(count)` | all 8 bytes meaningful | outer tag 0; u32 count at byte 4 |
| `Err(DestinationTooSmall)` | all 8 bytes meaningful | outer tag 1; nested error tag 0 at byte 4 |

For the existing little-endian ARM64/RV64 lanes, one 64-bit aggregate chunk
contains `tag + 2^32 * payload`. Thus `Ok(n)` has chunk `2^32 * n`, and the sole
error has chunk `1`. This is **aggregate transport**, not permission to change
the source or OptIR result type to `u64`, discard a payload, or encode failure
as a count sentinel. The representation relation decodes both tags and requires
the nested error payload to be exactly its valid constructor.

Both parameters use two ABI slots: destination `(base, len)`, then source
`(base, len)`. Existing native lowering uses:

- ARM64: `dst = (x0, low32(x1))`, `src = (x2, low32(x3))`; bindings express the
  lengths as `w1` and `w3`. Result aggregate is one chunk in `x0`.
- RV64: `dst = (a0, low32(a1))`, `src = (a2, low32(a3))`; result aggregate is one
  chunk in `a0`, without a hidden result-buffer argument. Span-length padding
  above bit 31 is not length data. Production RV lowering zero-normalizes length
  copies with `slli`/`srli` by 32 before unsigned bounds comparisons. Do not
  conflate the composite's u32 length field with a standalone u32 psABI scalar.
- The caller's Bool is a separate return value; its decoded observation must be
  0/1 with the target's documented high-bit policy. The live `n` must survive
  the aggregate result's overwrite of the argument/result register.

`TestStatefulCopyConcreteLayoutAndNativeCall` directly lowers the actual checked
functions with both `nativegen` lanes and encodes them. It checks the concrete
layouts, parameter bindings and one real callee relocation in the caller.
It is inspection of current production output, not independently checked
execution of that output. The future target proofs must establish complete
transport, normalization, restoration and fetched control flow.

No Wasm ABI has been selected by this document. Before implementation, choose
and freeze a lossless transport of this same typed Result and two descriptors.
Packed i64 and multi-value are possible implementation choices, each requiring
its own type/module/lowering/decoder/execution proofs. Neither choice is
currently admitted or can be assumed from the native aggregate representation.

## 3. Shared semantic interface: relations, not a new copy function

Use `Oak.Stdlib.Bytes.Result_u32_CopyError`, `copy_into`,
`copy_into_spec`, `copy_short_atomic`, and `copy_empty` from the existing
extracted library. Use `Oak.ViewRefinement.View`, `WellFormed`, `indexAt`,
`index_guard_iff`, `index_in_backing`, `index_read_agrees`, and `store_agrees`.
The physical-memory relation is the missing adapter; it must not introduce a
second reference copy algorithm or an alternative IR.

The following are proposed **interface names**, not newly implemented types or
theorems:

- `CopyClosure`: the original/resolved/typed closure described in section 1.
- `ByteView`: an existing `View` plus live owner/provenance identity, owner base,
  target address width and read/write authority. `View.start` and `View.len`
  stay the existing natural-number fields, with explicit u32 length bounds.
- `RepresentsWindow M descriptor backing`: the owner bytes in byte-addressed
  memory `M` agree with `backing : Array UInt8`; the existing `View` is
  `WellFormed` for that backing. Its logical array is the corresponding
  `backing.extract start (start + len)`, with a proved size/read relation.
- `RepresentsCopyState`: both window relations, immutable allocation/provenance
  metadata, the pending caller/callee control point and live `n`, decoded ABI
  values, and a reserved scratch-frame footprint.
- `ObservesCopy`: the **existing extracted function's result and destination
  array**, caller Bool, and physical memory/frame consequences below.

Memory is byte-addressed and partial (e.g. addresses mapped to `Option UInt8`);
unmapped or uninitialized bytes are not silently zero. The representation
relation supplies actual initialized bytes for every logical source and
destination byte. A defaulting `Array.getD` is never a substitute for a machine
permission or initialization check. The adapter uses `index_read_agrees` and
`store_agrees` under their actual well-formedness and in-range premises.

### Invocation premises

For logical source and destination lengths `s,d`:

1. `s < 2^32`, `d < 2^32`. Both windows have live backing owners and initialized
   byte contents. `start + len ≤ backing.size` is an existing `WellFormed`
   premise; physical addresses correspond to those same owners/offsets.
2. Source has readable authority; destination has exclusive writable authority
   for the complete call. Their positive logical byte intervals are disjoint.
   A pair of disjoint views from one owner is included only if actual ownership
   admission supports those simultaneous authorities; physical disjointness
   alone does not manufacture an exclusive borrow.
3. Allocation/owner bases, view bases and endpoints are representable, and all
   sums used by the target are nonwrapping. For this bounded first contract use
   `base + start + len < 2^addressBits` as a conservative endpoint premise
   (natural arithmetic), in addition to the backing bounds. A broader top-of-
   address-space policy requires a separately justified endpoint representation.
4. Empty windows may be at the end of a live backing allocation, including
   nonempty backing. Their descriptor base must still be a valid representable
   in-owner or one-past pointer derived from that owner. They grant no byte
   access and need not designate a mapped byte at the one-past position. No
   arbitrary null, dangling or forged descriptor is admitted by `len = 0`.
   This invocation policy is deliberately more explicit than the value-level
   array theorem.
5. Native windows are mapped for the required reads/writes and disjoint from
   code, metadata and reserved stack frames; memory mapping and permissions
   remain stable. Wasm offsets and endpoints fit the current instance's linear
   memory as well as the address-width premise. Different calls share the
   same instance memory, never separate per-frame copies.
6. No concurrent mutation, volatile/MMIO effects, allocation, foreign callback,
   retained pointer, or mutation of descriptor/provenance metadata.
7. Native entry satisfies the target's stack alignment, return/link-register,
   callee-saved register and nonoverlapping frame-space premises. Define each
   caller and callee reserved frame from actual code; a generic “some scratch”
   exception is too weak. Inputs may be arbitrary valid bytes and runtime
   lengths satisfying these premises, not just the finite fixture arrays.

These are invocation premises, not established consequences of today's
frontend. `BorrowStateRefinement` and `BorrowRegions` supply useful model facts
but do not prove production end-to-end ownership. Either prove the exact
frontend/borrow/physical-authority join for this closure, or name it explicitly
in the final theorem's assumption/trust boundary. Do not hide it behind
`SourceChecked` or a caller-provided Boolean.

### Results and memory observations

Let `S,D` be the initial logical source/destination arrays obtained by the
representation relation. Let `R` and `D'` be the actual existing extracted
`copy_into D S fExtract = some (R,D')` result.

- If `s ≤ d`, then `R = .Ok s.toUInt32`, the caller returns true, and for every
  `k < d`, the final destination is `S[k]` when `k < s`, otherwise `D[k]`.
- If `d < s`, then `R = .Err .DestinationTooSmall`, the caller returns false,
  and `D' = D`. This is a valid invocation with a valid error result, not an
  admission refusal. Both size bounds are needed to turn the extracted
  wrapped-u32 guard into the natural-number comparison.
- If `s = 0`, return `.Ok 0` and true with no data read/write. Test empty source
  and destination windows separately, including one-past ends and surrounding
  canaries.
- All source bytes and all destination suffix bytes retain their initial
  contents. All data bytes outside the copied destination prefix retain their
  contents, except for the explicitly reserved native frame bytes.
- Native frame contents themselves need not be restored. SP, return behavior
  and required callee-saved state must be restored. The union of actual caller
  and callee scratch frames is the only extra write footprint; it is disjoint
  from both user windows. Thus even the short/empty path may perform stack
  stores while performing **no destination writes**.
- At the callee-return cut point, decode the complete concrete Result and
  relate it to `R`. At caller return, relate the Bool to matching that same
  Result and comparing the preserved `n` with its success count. Neither
  observation can stand in for the other.

The loop invariant is the existing copy proof's state embedded into this
relation: `0 ≤ i ≤ s`, copied destination prefix `[0,i)`, untouched destination
suffix `[i,d)`, unchanged source and external data, valid guards/addresses,
and preserved caller state at the applicable call cut points. At a body step,
`i < s ≤ d` establishes both byte accesses; `i + 1 ≤ s < 2^32` establishes
nonwrapping increment. Only the destination byte at index `i` changes.

### Fuel and termination

Keep distinct named measures:

- `fExtract`: existing extracted `copy_into` loop fuel. Success needs
  `s < fExtract`; `s + 1` is sufficient, including one final guard check.
  The short path succeeds at fuel 0; `copy_empty` needs at least 1.
- `fCaller`: any separate extracted caller/call-composition budget. Establish
  its relationship to the actual caller extraction; do not equate it with
  `fExtract` merely because both are Nat.
- `fTarget`: decoded instruction/small-step fuel including caller prologue,
  argument transport, callee entry, short/success branches, every byte iteration,
  epilogues and return. Derive per-path constants and per-iteration bounds from
  frozen emitted bytes. State a target-specific bound such as
  `Centry + Cguard + s * Cbody + Cexit` only after proving its constants.
- Encoder/linker/producer fuel and output capacity are separate again.

The well-founded copy measure is `s - i`; the extracted and target simulations
must relate it to their own fuel. Exhaustion is not a successful error result.
No arbitrary machine-fuel constant establishes termination for symbolic lengths.

## 4. Minimal extension of existing OptIR

Keep `optir.Function`, typed SSA values, `Region`, `While`, canonical CFG,
operation sites, checked fact/memory authority identities and direct calls.
Start from the raw checked projection. Do not add an intermediate IR or claim a
general optimization theorem as part of this slice.

An important refinement of the earlier audit: **u8 scalar values are already
accepted by `checkedOptIRType`**, and native OptIR selectors already contain u8
normalization and byte-width scalar/global loads/stores. Reuse them. The missing
join is typed spans, indexed partial memory and concrete Result, not the invention
of u8 arithmetic.

The minimal closed projection needs these operations/types:

| Existing or proposed projection | Required meaning |
|---|---|
| Existing u8, u32, Bool, integer constants/comparisons/addition | Reuse fixed-width semantics and normalization; prove increment nonwrap from the loop invariant |
| Two opaque typed byte-view parameters (`[*]u8`, `[]u8`) | Bind owner/view/authority identities and target-independent runtime length; no arbitrary pointer arithmetic |
| Proposed `view.length(view) -> u32` | Exact logical length from the descriptor relation |
| Proposed `memory.byte-load(view, u32 index) -> u8` | Checked `index < len`, authority/provenance/initialization, one-byte address and read footprint, explicit trap possibility |
| Proposed `memory.byte-store(span, u32 index, u8) -> ()` | Same guard and exclusive authority; changes exactly one byte; explicit write/trap effects |
| Concrete typed `Result_u32_bytes__CopyError` | Declaration/instantiation identity, not just a display string or opaque integer |
| Proposed Result constructors/projections | `.Ok(u32)`, `.Err(.DestinationTooSmall)`, outer tag test, success payload; error payload validity retained even when caller ignores it |
| Existing direct `call`, return, conditional and pre-test loop | Exact resolved target and signatures, effectful call, preserved `n`, actual Result value carried across the call |

Exact opcode spellings are provisional until the production frontend lane
implements/checks the small closed vocabulary. The semantic arities and
requirements above are the interface. Result payload projection must be
dominated by the matching variant, or be total with an explicit proof that the
inactive projection is never observed. No general ADT engine, allocator,
recursion, dynamic dispatch or arbitrary raw-pointer support is required.

`OpLoadRegion`/`OpStoreRegion` currently mean complete checked-region
read/replacement. They must **not** encode byte accesses to a whole span. Keep
checked `MemoryAccessID`/region identities, but add byte-index/address/width and
partial-write facts with physical-content semantics. Conservative call
summaries may mark “read source, may-write destination.” A may-write invalidates
dependent knowledge but does not prove a whole-region overwrite or justify
dead-store elimination of other bytes. Until refined analyses are proved,
refuse optimization passes on the new accesses or preserve them unchanged.
Do not weaken existing whole-cell exactness checks.

Existing `OptIRCallSummaryCertificate`, `OptIRMemoryAuthorityProjection` and
`OptIRMachineCallIdentity` can bind metadata and call occurrences. They do not
establish indexed byte semantics, runtime nonaliasing, dynamic call execution,
or ABI value preservation. The source lane must establish that join explicitly.

## 5. Current refusals and target boundaries

The source language accepts this caller and the real package. At this baseline:

- OptIR refuses `copy_checked` with
  `parameter dst has unsupported type [*]u8`.
- OptIR refuses `bytes__copy_uinto` with
  `return type Result[u32, bytes__CopyError] is outside the scalar OptIR subset`.
- The full package Wasm API first refuses a non-function declaration:
  `wasm: scalar profile supports function declarations only (got *ast.ADTType)`.
  This earliest refusal does not mean removing the declaration would suffice.
- `wasm.valueType` has no u8/span/Result mapping, memory effects are rejected,
  and the closed byte checker requires exactly sections 1/3/7/10. The current
  Lean Wasm state/module types lack linear memory. Byte-load/store instructions,
  memarg encodings and shared instance-memory call semantics are not yet there.
- `ResourceSemanticIR` explicitly implements the resource slice. `TypeModel`
  projects type declarations, with executable functions still in the checked
  AST path. Neither is an already verified whole-language middle end.

The Wasm lane must first propose a separately versioned closed memory profile:
one fixed unshared memory, explicit initial memory/host observation, no imports,
start, grow, bulk-memory or allocator; exact permitted memory section/export
shapes; byte bounds and overflow rules; concrete argument/Result transport.
This contract document creates no such profile and cannot authorize widening
the scalar checker.

For ARM64/RV64, direct production lowering/encoding is only the starting byte
shape. Prove byte instructions, comparisons, loops, call/return, frame bounds,
live values, Result transport and no-write short paths. Existing 64-bit stack
store laws do not prove byte-copy semantics. RV scalar upper-bit normalization
and descriptor-length normalization require their own explicit statements.

## 6. Acceptance gates for parallel lanes

These are ordered gates, with independent work possible after the interface is
agreed. Every lane returns a theorem/fixture name, exact source and output
identities, premises, refused cases, and any remaining trusted join.

1. **Source/extraction/authority lane.** Freeze the closure in section 1;
   typecheck the real caller; retain the actual direct call and concrete result.
   Regenerate the existing extraction. Prove the scoped source/extractor
   connection or explicitly retain it as trusted correspondence. Establish
   logical-window size/read/store composition from `BytesLaws` and
   `ViewRefinement`; separately establish or expose the production ownership/
   physical-authority premises. Do not add an axiom saying frontend/alias
   correctness simply holds.
2. **OptIR lane.** Implement the minimal production checked-AST projection
   above, retaining exact source/type/call identities and partial memory
   effects. Prove its execution relation to the shared contract. Existing
   scalar/whole-cell checkers stay strict. Invalid pointers, unsupported types,
   operations, calls and uncertified aliases remain refused.
3. **ARM64 lane.** Bind the real two-function body and relocation; prove
   fetched byte-load/store, loop/branch, complete aggregate return, `n`
   preservation, exact scratch footprint and restored call state for all valid
   inputs and sufficient proved target fuel.
4. **RV64 lane.** The same contract, with RV address and integer normalization,
   byte-width memory instructions, actual call/return/relocation and stack
   rules. State Sail revision, decoding/fetch and initialization assumptions
   separately; a theorem over supplied decoded instructions is not full fetch.
5. **Wasm lane.** Freeze its concrete ABI and closed memory profile first;
   implement/prove typed descriptor and Result lowering, load8_u/store8,
   shared linear-memory calls, exact section/opcode validation, bounds/traps
   and byte assembler encodings. Keep independent Core correspondence a
   distinct stated gate rather than inheriting it from a local subset model.
6. **Full-artifact/producer lane.** After body/module shapes are fixed, bind
   original closure, all code bytes, symbols, relocation targets, concrete
   ABI, entry/load mapping and complete envelope. Independently admit the same
   source closure on all three targets. Add scoped Oak assembler/linker/writer
   exactness, capacity/fuel success and refusal/frame laws for those envelopes.
   Preserve the existing strict bitwise profiles and identify the Go seed.

Universal target theorems must include success, short-error, zero-length,
unchanged source, unchanged destination suffix and external-frame properties,
with runtime lengths/bytes symbolic. Finite execution fixtures are supporting
regressions, not substitutes. Release claims must list target-specific external
Sail/Core boundaries; one target's stronger theorem does not elevate another.

### Mandatory positive and negative controls

- Positive: zero/one/multiple bytes, both zero lengths, one-past empty windows,
  equal/excess/insufficient capacity, nonzero offsets, high-bit bytes, full
  backing canaries and a live caller value across the real call.
- Structural negatives: changed caller/dependency bytes or package binding;
  wrong concrete Result identity/tag/payload/layout; absent/inlined/rebound
  call; wrong relocation; changed load/store width, address, loop guard or
  increment; wrong symbol/load mapping; unapproved Wasm imports/memory sections.
- Ownership negatives: overlapping or invalid source borrows rejected by the
  source/authority boundary where supported. A raw runtime descriptor violating
  the invocation premises is outside the theorem unless a separately proved
  entry validator rejects it. Do not claim an artifact checker sees arbitrary
  runtime aliasing.
- Valid short destinations must reach `.Err(.DestinationTooSmall)` without
  data writes; rejecting them at admission is a contract failure.

The existing 174-case bytes correspondence corpus can be reused for target
regressions. The new 21-case offset/empty-window corpus checks the caller observation and
every byte of source/destination backing in the interpreter and C. Neither is
a new implementation of `bytes.copy_into`.

## 7. Reproduction and non-claims

Run with the repository's pinned official Go toolchain and existing dependencies:

```sh
GOMAXPROCS=2 GOPROXY=off GOSUMDB=off GOTOOLCHAIN=local \
  go test -p=1 ./compiler \
  -run '^(TestStatefulCopy.*|TestLeanStdlibExtract)$/^(bytes|arm64|rv64)$' \
  -count=1 -v
```

No Lean file is added or changed, and no kernel recheck is claimed here. The
reused theorem statements above are source-inspected proof assets. The native
instruction fixture is a production shape/encoding check; the C test is a
source semantics regression; the source hash test is an identity check. None
is a universal compiler, middle-end, alias, native execution, Wasm memory,
linker, full-file admission, or external ISA/Core refinement theorem.
