# Resource contracts and borrowed results

Design and implementation audit following resource parameter modes and call-local
exclusivity. This document proposes the next semantic increments; it does not
enable borrowed returns or freeze source syntax. The normative borrowing rules
remain in `spec/50-borrowing.md`.

## Current implementation audit

Audited against specification commit `0c086683a8a02fa9bb96a5a6e0d856942bbe0321`.
PR #69 merged as `906bff7b575dd114e08a27e7ed9acdad4ef15d80`. Its resource-flow
files still match the reviewed head `99423a1` at this specification revision.

| Boundary | Evidence | Finding |
| --- | --- | --- |
| Declarations to resolved facts | `typechecker/resource_resolution.go`, `resolveResourceParameters` | Validates nominal resource parameters, modes, indices, and cross-protocol agreement; derives the consumption projection. |
| Resolved facts to SemIR | `compiler/resource_semir.go`, `emitResourceSemIR` | Emits canonical borrow, mutable-borrow, consume, and fresh-return effects. |
| SemIR to executable model | `typechecker/resource_semir.go`, `resourceParametersFromSemIR` | Preserves modes and consumption. Direct model construction needs the same canonicalization guarantees. |
| Ordinary global calls | `typechecker/resource_flow.go`, `callableIdentity` | Resolves the global function identity, provided it is not lexically shadowed. |
| Nominal method calls | The same resolver and `resource_callable_test.go` | Resolves `Receiver::method`. Parameter indices describe explicit arguments; the receiver is not an implicit consumed argument. A separate receiver authority contract is still needed. |
| Function values | `FunctionType` in `typechecker/typechecker.go`; `callableIdentity` | Function types carry parameter types, result type, and variadic status, but no resource contract. Local callable bindings are deliberately excluded from global-name resolution. Contract preservation through function values is not established. |
| Generic specialization | `typechecker/genericfn.go`, `invokeInstantiated` | Calls are rewritten to concrete mangled identities and specialized bodies are checked. There is no resource-contract projection in this specialization path. Rechecking bodies is not evidence that a template's external contract survives renaming. |
| Interfaces and wrappers | Nominal-only resource resolution and callable lookup | Interface-level ownership substitutability and wrapper effect summaries are not implemented by this path. A wrapper's call to a consuming function does not itself establish the wrapper's caller-facing contract. |

These are source-audit findings, not claims of executed end-to-end regression
coverage for every boundary. In particular, do not treat an unresolved callable
as proof that its resource effects are empty.

## Repair of the existing call checker

The accompanying repair normalizes direct resource operations in both directions:
legacy consumption adds consumed modes, and consumed modes generate consumption.
Matching duplicated representations are accepted for SemIR compatibility;
contradictory representations fail closed. The checking entry point normalizes
direct map construction too.

A successful fresh-return invocation supplies independent result authority even
when used directly as an argument. A source temporary is not required. Rejected
inner calls cannot certify fresh results or authorize outer-call consumption.
Unknown projections remain unknown after naming them. Already-consumed arguments
retain their causal use-after-consume diagnostic, rather than acquiring a second
unknown-provenance diagnosis.

Resource reassignment is conservatively rejected pending destination provenance
tracking. This is an acceptance restriction, not a complete reassignment model.
Future support must handle shadowing, reassignment through blocks, control-flow
joins, loop fixed points, and old aliases without reviving consumed authority.

## Callable contract preservation

Introduce one checked semantic callable contract, referenced by stable declaration
identity rather than inferred from source names or mangled-name prefixes. It must
describe explicit parameter modes, any receiver mode, result provenance, and
retention/escape obligations. Syntax and ABI projection remain separate choices.

Initially require exact normalized resource-contract agreement when substituting
function values or interface implementations. Do not invent ownership variance
until its substitutability laws are specified and proved. Missing information is
unknown, not an empty-effect contract. When a boundary cannot preserve a required
contract, reject that boundary with a diagnostic identifying where it would be
lost.

Specialization must project the template contract under the same type substitution
that produces the specialized signature. Wrappers must either have a checked
explicit contract or acquire a sound inferred summary. Borrowed parameters cannot
be forwarded to consuming operations merely because their local bindings are
live. A borrowed parameter's authority is also a callee-body obligation.

Acceptance cases:

1. Calling a consuming operation through a local function value still invalidates
   the caller's resource aliases.
2. A consuming implementation cannot satisfy a shared-borrow callable contract.
3. Two concrete specializations preserve the same template authority modes.
4. A wrapper that consumes its input cannot expose a borrow-only contract.
5. Receiver modes survive method resolution without shifting explicit indices.
6. Unknown contract information cannot erase an already-known obligation.

## Result provenance and lifetime dependencies

Result identity, access permission, and lifetime dependency are separate facts.
The following names are explanatory semantic categories, not proposed keywords.

| Result category | Authority identity | Lifetime/access obligation |
| --- | --- | --- |
| Fresh | New independent authority class, established by the callable contract | Freshness alone does not establish allocation, ownership of backing memory, or an unlimited lifetime. |
| Alias of input | Same authority class as a specified input or projection | Cannot widen the input's access permission; consumption of that class invalidates its dependent aliases. |
| Shared borrow of input | Proven dependency on the input's authority or storage origin | Read permission; result must stay within the proven owner lifetime and prohibit incompatible owner access while live. |
| Mutable reborrow of input | Proven dependency on an exclusive input access | Parent access is suspended for the result's lifetime and restored on release; the result cannot outlive its source. |
| Unknown | No established identity relationship | Cannot prove independence, permit exclusive use that requires it, or justify escape. |

For storage views, retain owner and absolute region facts. For opaque resources,
retain resource authority identity. Relate the two only when an operation's
contract establishes that relationship; do not manufacture a storage borrow for
an opaque handle.

Returning an alias or borrow of consumed input authority is invalid unless a
separately specified transfer contract establishes new valid authority. Merely
marking the return fresh is not proof of backing-storage liveness. The compiler
must validate declared result relationships against bodies, or admit them only
at an explicit trusted external boundary.

At control-flow joins, preserve every possible dependency. Conflicting origins
must become a conservative dependency set or unknown provenance, never fresh
authority. Field names alone do not prove resource independence: two different
fields may contain handles to the same resource.

Keep `OAK-B0109` in force until these relationships are implemented end to end.
The first useful positive case is a read-only result derived from one caller-owned
input with no local owner escape. Tests must include owner destruction, mutation,
consumption, wrapper storage, branch-dependent origins, and invalid nested calls.

## Call duration and future callbacks

Specify evaluation and access admission as separate phases. Evaluate the callee
and arguments in the language's defined order, preserving effects of nested calls;
validate resource arguments at the call boundary; admit temporary access; perform
the call; end temporary access. Consumption affects only accepted operations.
Rejecting an outer call does not undo valid nested calls already evaluated.

This pairwise call checker is not an interprocedural exclusivity proof. Before
capturing callbacks are enabled, contracts must account for retained authority,
reentrant access, globals, and overlapping callback execution. A returned borrow
extends a dependency beyond call completion and therefore cannot use the current
"all temporary access ends at return" rule without an explicit result contract.

## Generic resource ergonomics

Exercise `Option[Handle]`, `Result[Handle, E]`, and Oak's existing match expression
early. Inspection should borrow a payload; extraction should transfer authority
and invalidate the previous owning location. Copyability is a capability, not an
assumption that every type variable satisfies. Ownership-aware matching should
extend the existing match semantics without introducing a second branching form.

Editor information should expose parameter and result contracts. Diagnostics
should distinguish proven aliasing, unknown provenance, and already-unavailable
authority, showing both conflicting uses where applicable. A suggested temporary
binding must never be presented as a way to manufacture authority.

## Swift references

- [SE-0377: Parameter ownership modifiers](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0377-parameter-ownership-modifiers.md): contracts on declarations and function types. Swift consuming calls on copyable values are not Oak resource invalidation.
- [SE-0176: Exclusive access to memory](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0176-enforce-exclusive-access-to-memory.md): access duration and callbacks. Storage exclusivity does not establish unique resource authority; Swift's dynamic enforcement is not a proposed Oak runtime requirement.
- [SE-0437: Noncopyable standard-library primitives](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0437-noncopyable-stdlib-primitives.md): make optional/result APIs usable without assuming copying.
- [SE-0447: Span](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0447-span-access-shared-contiguous-storage.md): safe borrowed contiguous access and lifetime dependencies. Swift's read-only Span corresponds more closely to Oak's view.
- [Swift API design guidelines](https://www.swift.org/documentation/api-design-guidelines/): evaluate actual call sites and use consistent operation naming.
