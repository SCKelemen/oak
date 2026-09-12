# Roadmap: authority contracts, resources, borrowed results, and predictable optimization

**Status: proposal.** Committed here so every session builds against one
dependency-ordered plan for the Futhark/Swift-inspired workstream. Nothing
below is implemented unless marked landed; milestone numbers are scopes,
not PR numbers. Baseline checked: `specification` at `ae5043e`.

The arc is **sound authority contracts → composable resource APIs → safe
borrowed results → predictable optimization**. Swift informs ownership and
API ergonomics (SE-0377 parameter conventions, SE-0390/0432 noncopyable
types and matching, SE-0447 Span, SE-0430 transferring, SE-0176
exclusivity); Futhark informs size reasoning and array processing.

**Design constraints.** Keep resource identity, storage provenance, access
permission, lifetime, copyability, cleanup, and synchronization distinct.
Consumption transfers or invalidates authority; it does not itself prove
freshness, destruction, allocation, or device completion. Unknown facts
fail closed where a safety decision requires them. Opaque handles do not
acquire invented view/span storage borrows. Ordinary value-copy semantics
remain intentional. Every new surface needs end-to-end support in
checking, interpretation, and lowering.

## 0. Landed foundation — preserve and document accurately

| Foundation | Scope |
| --- | --- |
| Resource parameter modes (#68) | syntax-independent `borrowed`, `borrowed-mut`, `consumed`; canonical SemIR effects; legacy metadata compatibility |
| Call-local exclusivity (#69) | shared participants may alias; mutable/consumed participants need compatible authority classes — a call-boundary check, not interprocedural exclusivity |
| Contract repairs (#74) | consumed-mode normalization, direct fresh-result handling, causal diagnostics, nested-call rejection, conservative resource-reassignment rejection |
| Storage borrowing | views/spans, owner regions, writable reborrows, proved-disjoint sibling admission (`50-borrowing.md`) |
| Escape boundary | borrowed returns and borrowed aggregate storage conservatively restricted by `OAK-B0109` |

Entry work: refresh stale STATUS descriptions; record the trust boundary
of supplied semantic metadata. A green formal build does not prove
implementation correspondence. See `docs/resource-contracts-and-results.md`.

## 1. Enforce contracts inside callees — next safety milestone

Attach the checked parameter contract to function-entry authority.
`borrowed` permits shared use, never consumption or upgrade;
`borrowed-mut` permits authorized mutation, never permanent custody;
`consumed` removes the caller's authority and gives the callee usable
authority (not dead on entry). Reject wrappers that promise borrowing but
consume, retain, or forward improperly. Validate source-defined contracts
against bodies; imported/external contracts need an identified trust
boundary. Preserve unmarked-parameter meaning until a migration rule is
chosen.

**Done when:** a shared-borrow wrapper calling a consuming operation is
rejected; shared-to-mutable forwarding is rejected; permitted reads and
mutable operations pass; consumed parameters stay usable until their next
valid transfer; violations name the declaration and the offending use.

**Landed (first increment, 2026-09-11):** callee-entry authority for
forwarding (`50-borrowing.md` §9, `OAK-B0114`): each mode-marked resource
parameter enters with its contract's authority, aliases carry it, and
forwarding beyond it to a resource operation is rejected without
consuming; consumed parameters keep full authority; unmarked parameters are
unchanged. **Second increment (same day):** retention — returning a
borrowed or borrowed-mut parameter or its alias (directly, through a block,
or through a match arm) or storing it in a record or array literal is
rejected; a consumed parameter may be returned. Still open in this
milestone: imported/external contracts' trust boundary and the migration
rule for unmarked parameters.

## 2. Preserve contracts across every callable boundary

Stable semantic identities for resolved contracts, carried through function
values, higher-order parameters, aliases, generic specialization,
interfaces, receivers, imported/sealed signatures, and compiler renaming.
Start with exact normalized agreement; variance only after proving the
substitutability laws. An unknown contract is not an empty effect set.
Receiver authority is its own slot.

**Done when:** indirect consumption invalidates caller aliases; a consuming
function cannot satisfy a borrowed-function requirement; specializations
retain template modes; imports and sealing cannot erase modes; receivers
do not shift parameter numbering.

**Landed (first increment, 2026-09-11):** function values initialized from
global functions carry their contracts (indirect consumption invalidates
caller aliases); function values of unknown provenance have unknown
contracts and resources passed through them fail closed (`OAK-B0115`);
specializations retain template modes at call sites and in specialized
bodies (`50-borrowing.md` §9). **Second increment (same day):** receiver
authority as its own slot — receiver modes participate in exclusivity and
consumption without shifting explicit indices, govern method bodies, and
round-trip through SemIR. **Third increment (2026-09-12):** contracts on
function types — a function-typed parameter requires a callable contract,
satisfied only by exact agreement (`OAK-B0116`), and calls through the
parameter use it (acceptance case 2). **Fourth increment (2026-09-12):**
`via f(consumed h, borrowed mut receiver)` declares modes in source
(`112-protocols.md` §5) and, because protocols elaborate with internal
names, imports and sealing cannot erase them (acceptance case 4). The milestone's acceptance list is covered. **Fifth increment
(2026-09-11):** callable contracts, fresh returns, and methods
(`via Handle.close(consumed receiver)`) have their source spelling on
the via line (`112-protocols.md` §5.1).

## 3. Resource provenance through bindings, projections, control flow

Bindings by semantic identity with current authority origins; a location
holding a handle is distinct from the authority the handle identifies.
Replace blanket reassignment rejection incrementally. Support shadowing,
reassignment, projections, aggregate writes, branches, loops with
convergent dataflow. Distinct fields are not automatically distinct
resources; rebinding cannot manufacture freshness; freshness has a scope.

**Done when:** alias reassignment makes later exclusive use conflict;
fresh assignment does not revive old aliases; shadowing leaves outer
bindings alone; branches and loops cannot manufacture disjointness.

**Landed (first increment, 2026-09-12):** reassignment of resource bindings
is tracked (`50-borrowing.md` §9): rebinding to a live name joins its
class, rebinding to a fresh result starts a new class, other right-hand
sides give unknown provenance, rebound parameters release entry authority,
and joins drop names whose provenance differs. All four "done when" cases
are tested. **Second increment (same day):** projections and aggregate
writes — record literals give resource fields the provenance of their
initializers, paths extend through nested records, projections are uses of
the field's authority, field and whole-record writes rebind paths, and
fields without provenance stay untracked and fail closed. Still open:
array elements (never tracked) and loop-specific fixed points beyond the
existing two-iteration probe.

## 4. Checked result provenance, then borrowed returns

Independent result facts — identity (fresh / input alias / unknown),
permission (shared / mutable / owned), lifetime (which caller-owned storage
must stay valid). Stages: (a) checked result contracts with current escape
restrictions; (b) one shared borrowed result tied to one caller-owned
input; (c) nested and multiple-origin results; (d) mutable reborrows
suspending the parent; (e) borrowed values in aggregates with destination
lifetime checks. Freshness never proves backing-storage lifetime.

**Done when:** a parser returns a view into caller-owned bytes while a view
of local storage stays rejected; owner mutation is rejected while a
dependent view lives; wrappers preserve every dependency. Retain
`OAK-B0109` for every unsupported case.

**Landed (stage (a), 2026-09-12):** checked result contracts
(`50-borrowing.md` §9 "Result identity"): a result is declared fresh or an
alias of one argument (`resource.return-alias arg:N` in SemIR), bodies are
validated against the claim (`OAK-B0117`), a declared alias return of a
borrowed parameter is exempt from the retention rule, and callers carry
the aliased argument's provenance into bindings, rebinding, projections,
and nested arguments. **Stage (b) (same day):** borrowed resource results
(`50-borrowing.md` §9 "Borrowed results", `resource.return-borrow arg:N`,
`OAK-B0118`): a shared borrow of one borrowed argument is its own
authority dependent on the argument's owners for its scope; owner
mutation, consumption, and rebinding, dependent mutation, consumption,
storage, and uncontracted return, and rebinding across scopes are
rejected; contracted wrappers preserve the dependency; joins union
dependencies. Storage views keep their own rule (§8c). **Stage (c) (same
day):** multiple-origin results (`BorrowsArguments`, one `return-borrow`
per origin), root-owner union with fail-closed unknown origins, projection
owners protected against field and whole-record writes, wrapper contracts
that must cover every origin, and temporary borrowed results participating
in exclusivity by owner set. **Stage (d) (same day):** mutable reborrows
(`BorrowMutable`, `return-borrow-mut`, `OAK-B0119`): origins must all be
borrowed-mut, the result may be passed to borrowed-mut positions and
reborrowed, its owners are suspended entirely for its lexical scope (a
temporary suspends for the call), widening is rejected and narrowing
admitted. **Stage (e) (same day):** borrowed values in aggregates: record
fields hold borrowed results under a destination lifetime check, paths
carry dependency and permission, copies carry them, records holding
borrowed fields cannot be passed or returned, arrays stay rejected.
**Milestone 4 is implemented for opaque resources.** **Source spelling
(2026-09-11):** all three result identities are written on the via line
(`: alias h`, `: borrow a, b`, `: borrow mut a`; `112-protocols.md` §5.1),
and `via unsafe` marks a claim trusted — the explicit boundary for
primitives whose bodies carry no provenance (`50-borrowing.md` §9 "Trusted
result claims"). `Oak.ResourceResult` models admission, monotonicity,
narrowing/widening, the caller's classification, callable-contract
agreement, and the trust boundary. Open: contracts for record-typed
parameters and results that carry borrowed fields (today they fail
closed); array element provenance.

## 5. Resources through generics and pattern matching

Copyability as a capability, propagated through fields, payloads, generic
substitution, construction, extraction. `Option[Handle]`,
`Result[Handle, E]` first. Borrowing inspection vs consuming extraction in
the one match form; whole-value moves before partial-field states.

**Done when:** inspect an optional handle and keep using it; extract and
reject reuse of the old location; return through `Result` without
duplication; generic helpers specialize without erasing authority.

**Landed (first increment, 2026-09-12):** resource paths through record
fields and ADT payloads (`50-borrowing.md` §9 "Resources through
aggregates"), construction and match extraction (inspect keeps the source,
extract consumes the location, re-matching is `OAK-B0111`), return through
`Result` as an alias of a consumed parameter (no duplication), contracts on
aggregate parameters path by path with sibling paths failing closed, and a
template's contract governing its specializations' payloads. All four
"done when" cases are tested. Open: borrowing or aliasing an aggregate
argument as a whole, partial-field states after a move, array elements,
and copyability as a declared capability.

## 6. Cleanup and terminal-state obligations

Separate: may an unused value be dropped; does dropping clean up; must a
protocol reach an explicit terminal state. Define behavior across returns,
error propagation, transfers, partial moves; effects, failure, ordering
before choosing `defer`/destructor syntax.

**Done when:** no double cleanup after transfer; no cleanup of moved
fields; required `close`/`abort` transitions checked on every exit;
generated C makes cleanup auditable.

**Landed (first increment, 2026-09-12):** terminal-state obligations
(`50-borrowing.md` §9): protocols declare terminal states (SemIR guarantee
`terminal`), owned resources must reach one on every exit or pass custody
on (`OAK-B0120`), closers discharge their own parameters, and no double
cleanup or moved-field cleanup can occur because consumption forbids later
use. Three of four "done when" cases are tested; auditable cleanup in
generated C, and what dropping does (destructors), remain open. **`defer`
(same day):** `10-syntax.md` §4b, block-scoped and static, the idiomatic
way to discharge an obligation on every exit including `break`.

## 7. Scoped callbacks and shortened borrows

Nonescaping captures with justified stack environments first; callback
contracts preserve permissions; retention, reentrancy, effects accounted
for. Then last-use borrow shortening where dataflow proves it, lexical
fallback otherwise.

## 8. Symbolic extents and shape obligations

Constants, symbolic lengths, equalities, simple inequalities, +/−,
multiplication by constants; propagation through slicing, splitting,
contract-checked calls; existential result lengths; runtime checks
establishing scoped evidence. Keep `[N]T` layout extent distinct from a
view's length proposition. (The assembler's span guards —
`94-assembler.md` §7 — are the first instance of a runtime check
establishing scoped extent evidence.)

**Done when:** same-length requirements are established or diagnosed;
slicing keeps the correct owner region and extent; a checked comparison
is usable evidence; dynamic lengths never escape with fabricated
equalities.

## 9. Proven facts into predictable performance

Sequential bulk operations over caller storage first (map-into, zip-into,
folds, scans, proved partitioning) with explicit alias, effect,
initialization, and allocation behavior; then bounds-check elimination,
proven in-place updates, fusion where effects permit, SIMD/parallel under
explicit contracts. Parallel reduction needs algebraic laws and a
reproducibility policy — floating-point addition is not associative.
Report improvements only when measured.

**Landed (first increment, 2026-09-12):** protocol machines without a
data record lower to compile-time transition tables — shift DFAs up to
ten states, dense `u8` tables otherwise — with `name_run` over a byte view
(`112-protocols.md` §2a, `90-backend.md` §14, `Oak.Protocol`). Measured
against the branch tree the same declarations produced before: 3x to 15x
on input-driven steps, and the emitted UTF-8 validator at the hand-written
shift DFA's 0.5 ns per byte (`benchmarks/state-machines/`). The method —
find the fastest structure for a golden use case, prove it computes the
declaration, make the declaration the only thing the user writes — is the
one this milestone continues with.

**Second increment (2026-09-12):** the UTF-8 validator, the golden case's
fixed-format instance, written in Oak over `simd.U8x16` with four new
byte-classification operations (`93-simd.md` §1.2, §1.5, `stdlib/utf8.oak`):
9.6 GB/s against simdutf's 12 and the scalar builtin's 0.35, the lookup
tables proved against Table 3-7 pair by pair (`Oak.Utf8Lookup`), the stream
checked differentially against the builtin.

## 10. Device custody and concurrency

Transferable custody vs concurrent sharing. Pilot one real CPU → device →
CPU protocol; track reachable storage and dependent borrows; completion
needs the target's event, ordering, visibility, and coherence
obligations — a type-state label alone cannot discharge them.

## 11. Syntax and ergonomics from working examples

Diagnostics throughout; settle declaration spelling, receivers, ownership
markers, result annotations, inference defaults after representative APIs
(file handles, borrowed slices, resource containers, scoped callbacks,
device submission) exercise the semantics.

## Delivery waves and first increments

| Wave | Work | Result |
| --- | --- | --- |
| A | 1, then 2; begin 3 | borrowed APIs cannot hide consumption or lose contracts |
| B | 3, owning part of 5, 4a | resource-containing APIs and identity tracking |
| C | 4b–4d, borrowed part of 5, then 7 | safe caller-buffer parsing, scoped callbacks |
| D | 6 and 8 | predictable exits, usable extent evidence |
| E | 9 and 10 | measured bulk processing, one verified device transfer |

First five bounded changes: callee-entry permissions and forwarding
checks; receiver contracts and stable contract identity through module
transformations; function-value contract preservation and exact
compatibility; generic/wrapper/interface propagation; binding provenance
across reassignment and control-flow joins, then projections.

**Definition of done for every safety increment:** state the rule and the
supported subset; preserve facts through all stages; test valid use and
attempted authority laundering; exercise branches, loops, aliases,
projections, wrappers, nested calls; validate emitted C and interpreter
behavior; run the repository gates; extend the formal model and label
implementation refinement only with an explicit correspondence proof.

**Open decisions:** ownership surface spelling; receiver notation;
callable ownership variance; default/exported-contract inference;
user-visible lifetimes; per-resource dropping and cleanup policy;
partial-move rules; first borrowed aggregate shapes; the extent theory and
runtime-proof admission surface; parallel numeric reproducibility;
target-specific device-transfer obligations.

## Asks recorded from the resource work (2026-09-11)

The ml pilot's asks document (`docs/notes/oak-asks.md` in that project)
and its pitfalls list live outside this repository; the entries below are
the gaps this workstream kept running into, recorded here so the
specification branch carries them, and marked as they land.

**Tier 1 — blocking for the resource work to be usable from Oak source**

| Ask | Status |
| --- | --- |
| Source spelling for result identities (fresh, alias, borrow, mutable reborrow) and callable contracts on function-typed parameters; methods on via lines | **Landed 2026-09-11** (`112-protocols.md` §5.1) |
| A trusted boundary for resource primitives: a definition-less declaration needs an asm unit and an extern needs C types, so a cursor over an arena had no honest way to claim a borrow beyond the provenance-free-body rule | **Landed 2026-09-11** as `via unsafe` (trusted result identity, `50-borrowing.md` §9); the provenance-free-body rule stays, and is now proved sound (`fresh_tracked_body_is_borrow_body`) |
| Method calls on ADT receivers lower to C, so receiver contracts execute compiled | **Landed 2026-09-11** (`90-backend.md` §13; `Oak.MethodMangling`) |

**Tier 2 — ergonomic, hit repeatedly while writing fixtures**

| Ask | Status |
| --- | --- |
| A bare block statement `{ ... }` for scoping, now that suspension and dependencies are lexical | **Landed 2026-09-11** (`10-syntax.md` §4c) |
| Statement lines may begin with `(`, `-`, or `!` | **Landed 2026-09-11**: `(` and `!` already did; `-` joins the F18 rule (`10-syntax.md` §4a; `Oak.StatementBoundary`) |
| Closure literals take typed parameters and a return annotation | **Landed 2026-09-11** (`10-syntax.md` §3c; lifted to C, `90-backend.md` §9) |
| One protocol per resource type | Open (`ResolveResourceDeclarations` binds a type to one protocol; several protocols over one type need a conflict rule) |
| Array elements tracked by provenance | Open (milestone 3; indices are not static) |
| The `bf16` note cites the bfloat16 convention rather than IEEE | **Fixed 2026-09-11** (`20-types.md` §11.3.1) |

