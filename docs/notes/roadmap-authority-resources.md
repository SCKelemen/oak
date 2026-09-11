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
names, imports and sealing cannot erase them (acceptance case 4). The milestone's acceptance list is covered; still open: a source
spelling for callable contracts and fresh returns.

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
and nested arguments. Permission and lifetime facts, and stages (b)–(e),
remain open; view results stay `OAK-B0109`.

## 5. Resources through generics and pattern matching

Copyability as a capability, propagated through fields, payloads, generic
substitution, construction, extraction. `Option[Handle]`,
`Result[Handle, E]` first. Borrowing inspection vs consuming extraction in
the one match form; whole-value moves before partial-field states.

**Done when:** inspect an optional handle and keep using it; extract and
reject reuse of the old location; return through `Result` without
duplication; generic helpers specialize without erasing authority.

## 6. Cleanup and terminal-state obligations

Separate: may an unused value be dropped; does dropping clean up; must a
protocol reach an explicit terminal state. Define behavior across returns,
error propagation, transfers, partial moves; effects, failure, ordering
before choosing `defer`/destructor syntax.

**Done when:** no double cleanup after transfer; no cleanup of moved
fields; required `close`/`abort` transitions checked on every exit;
generated C makes cleanup auditable.

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
