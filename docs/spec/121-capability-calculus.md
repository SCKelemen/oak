# Capability calculus — v0 authority algebra

Status: **implemented pure pilot and Lean reference model; not yet a kernel-enforced capability language feature.**

Sources:
- `spec/lean/Oak/CapabilityAlgebra.lean` — order-theoretic permission algebra.
- `examples/testing/capability_algebra_test.oak` — executable finite rights-set pilot.
- `SCKelemen/os/spec/tla/AgentCapabilityHandoff.tla` — stateful handoff model (separate repository).

## Separation of concerns

1. **Static authority**: Oak nominal phantom resource/rights/custody indices; consumed, borrowed and borrowed-mut contracts. Indices may be erased at codegen, but checked type constructors cannot be forged from raw integers.
2. **Runtime authority**: opaque slot + generation, object identity, rights, owner, derivation/revocation information. Kernel validates these even for malicious clients.
3. **Distributed authority**: broker-enforced policy, expiry, quotas, approval and remote revocation. A local kernel cannot enforce remote side effects on its own.

## Pure algebra

For a request type `Q`, authority is a predicate `Q → Prop`. Define
`a ≤ b` iff every request allowed by `a` is allowed by `b`.
`meet(a,b)` permits requests allowed by both; `join(a,b)` permits requests
allowed by either. The Lean model proves reflexivity, transitivity,
meet/join bounds, and transitive no-amplification for delegation.

**Join is not a capability-minting operation.** Only a privileged kernel
or broker operation may introduce or install authority. `meet` is a pure
computation; an explicit `delegate_exact(parent, requested)` should reject
requested rights outside the parent, not silently intersect.

For contextual constraints, model the request as a tuple of object,
operation, principal, time and context. Pure predicate intersection is
compositional. Finite budgets are *not* pure predicates: they require
atomic accounting, including across duplicated/derived handles.

## Stateful capability operations (next refinement)

- `derive(parent, requested, child)`: validate subset, delegation right,
  scope, owner, quotas, and depth; install a child handle atomically.
- `transfer(consumed cap, recipient)`: move one handle reference; on
  failure preserve the sender's authority; on success invalidate its old
  reference and install the recipient's. This does not revoke unrelated
  copies.
- `duplicate(cap)`: require explicit duplicate/delegation authority.
- `revoke(root)`: invalidate descendants, drain/abort affected operations
  under a defined cutoff, remove CPU and DMA mappings and synchronize
  translations before reporting a completed local revocation barrier.
- `use(cap, operation)`: validate live generation, owner, rights,
  revocation epoch, budget, and service policy at the enforcement point.

IPC descriptors may carry handle IDs, but moving a descriptor through a
ring **does not transfer authority**. Installation/removal must be a
kernel-mediated transaction.

## Proof obligations

- No amplification along any derivation path.
- No forged handles or generation reuse aliasing.
- Transfer failure preserves the sender's handle; transfer success does
  not leave a second sender-owned reference for move-only custody.
- No authorized new operation after a completed revocation barrier.
- CPU and device translations obey the grant's effective authority.
- Resource/accounting conservation for delegated budgets.
- Compiler/source-to-machine refinement for static capability contracts.

The Lean file proves only the **pure authority algebra**. It does not
prove kernel enforcement, affine code generation, cryptographic security,
remote revocation or physical memory isolation.

## Migration policy

Keep the OS's existing Oak/Zig conformance harness. Expand the Oak
capability implementation to endpoint, lend and recursive revocation
parity before making this a trusted end-to-end handoff. Keep Zig as a
differential and performance oracle, not the permanent authority.
