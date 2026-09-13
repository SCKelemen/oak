# Security protocol proof-of-concepts

Status: experimental pilots on `poc/security-protocols`.

These pilots test whether Oak can keep executable security-protocol state machines, theorem statements, resource/typestate facts, generated test actions, and TLA+ projections close to one semantic source definition.

## Pilots

`examples/testing/security_protocols_test.oak` contains the original three deliberately small models:

1. **Authenticated handshake plumbing** — the session may enter `Established` only after peer authentication, transcript binding, and shared-secret readiness have all been established.
2. **One-use ratchet key lifecycle** — deriving a message key moves the machine out of `Ready`; another key cannot be derived until the current message key is consumed. Closing the ratchet clears both live-key flags.
3. **Challenge-bound sealed-key authorization** — a protected operation requires user-presence evidence plus challenge binding, and consuming or expiring authorization returns the machine to a state with no live authorization.

`examples/testing/security_resources_test.oak` pushes the same ideas into Oak's type/resource surface:

- nominal key-purpose marker types and `SecretHandle[K]`, whose POC representation is an opaque numeric handle rather than secret bytes;
- a static-typestate `OneUseSecret` protocol, where `use` consumes the available-state handle and returns a spent-state handle;
- a bounded ratchet-key lifecycle with mechanically stated invariants;
- challenge-bound authorization carrying an explicit challenge value rather than reducing freshness to one Boolean.

`examples/testing/noise_security_test.oak` is a Noise-shaped authenticated-channel model:

- local ephemeral generation;
- validated remote ephemeral input;
- idealized DH/transcript binding;
- peer authentication;
- live send/receive chains;
- bounded per-direction message counters;
- close/abort paths that leave no live traffic-key state.

`examples/testing/double_ratchet_security_test.oak` adds:

- a fixed four-slot skipped-message-key cache rather than an unbounded dynamic map;
- consume-on-use skipped-key semantics;
- a Double-Ratchet-shaped epoch/counter state machine;
- an idealized DH-ratchet transition that advances epochs and resets per-epoch counters;
- close-state invariants clearing root/send/receive key liveness.

Each model has executable tests and protocol-invariant theorem candidates. Because Oak protocol declarations project to ordinary Oak state/step/data types, they are also suitable for generated property histories and `oak protocol -tla` model generation. Protocols without an explicit resource clause additionally project a static typestate handle whose transitions consume the source handle, which is the mechanism used by the one-use secret pilot.

## What these proofs mean

These POCs verify **protocol plumbing, boundedness, and lifecycle invariants**. They do not establish computational cryptographic security.

The handshake and ratchet models treat authentication, transcript hashing/binding, shared-secret derivation, DH, AEAD, KDFs, signatures, and key agreement as idealized boundaries. A proof that an Oak state machine only reaches `Established` after a `valid` transition is not a proof that an active attacker cannot forge authentication. A proof that a ratchet advances and deletes old logical authority is not by itself a proof of forward secrecy or post-compromise security.

The intended verification stack is:

```text
Oak nominal types/resources/typestate
    make key/evidence classes distinct and constrain ownership/use

Oak theorem + Lean extraction
    local algebraic, boundedness, and lifecycle invariants

Oak protocol + TLA+
    transition safety, ordering, fairness, bounded state, liveness

property/DST tests
    implementation behavior under generated histories and faults

cryptographic protocol verifier
    active-adversary secrecy/authentication/forward-secrecy claims
```

A future symbolic-security projection should target a tool such as Tamarin, ProVerif, or an equivalent verifier rather than pretending that TLA+ or ordinary functional correctness proves cryptographic indistinguishability.

## Secret values and erasure

The current pilots intentionally use opaque `SecretHandle[K]` values when they need secret authority. This avoids normalizing secret material as `[N]u8` in example APIs, but it is **not yet a language-level `Secret[T]` guarantee**.

A future `Secret[T]` policy should mean more than source-level unreachability:

- non-copyable/resource semantics;
- no default formatting or debug/event serialization;
- destruction/zeroization at the end of software-owned lifetime;
- exclusion from ordinary crash dumps/checkpoints unless explicitly authorized;
- an opaque-handle representation for non-exportable hardware keys (SEP/HSM/TPM) where bytes never enter ordinary memory;
- explicit assumptions when a backend/runtime cannot prove physical erasure.

This is a language/runtime requirement surfaced by the pilots, not a property these files claim today.

## Cryptographic primitive boundary

The executable protocol should eventually call nominal primitives such as:

```text
DH(EphemeralPrivateKey, EphemeralPublicKey) -> SharedSecret
KDF(Secret[SharedSecret], TranscriptHash) -> Secret[ChainKey]
AEAD.seal(Secret[MessageKey], Nonce, AssociatedData, Plaintext) -> Ciphertext
AEAD.open(Secret[MessageKey], Nonce, AssociatedData, Ciphertext) -> Result[Plaintext, InvalidTag]
```

The implementation can be tested against vectors and proved functionally correct where feasible, but computational assumptions (for example AEAD security, DH hardness, KDF assumptions) must remain explicit inputs to the adversarial proof layer.

## Next research steps

1. Add a first-class `Secret[T]`/non-exportable-secret policy rather than representing it only by convention.
2. Give crypto primitives nominal signatures and test-vector harnesses without baking one algorithm into the protocol layer.
3. Add generated property/DST histories for the Noise and ratchet POCs, including packet loss, duplication, reordering, expiry, and bounded skipped-key exhaustion.
4. Add a symbolic network/adversary projection from a deliberately small Oak crypto-protocol subset and compare generated output against Tamarin or ProVerif.
5. Model a real Noise pattern against official/reference vectors.
6. Only after the projection and assumptions are explicit, model Double Ratchet/PQXDH behavior against the Signal specifications/reference vectors.

The goal is not to replace mature cryptographic analysis tools. It is to minimize drift between the protocol that is analyzed and the program that actually runs.

## Current proof boundary

The branch now deliberately spans three different evidence classes: static typestate/resource rejection for one-use authority, invariant theorems over reachable protocol states, and executable transition tests. None of those imply symbolic or computational cryptographic security. The next qualitatively new capability is therefore not another Boolean protocol field; it is an explicit adversary/network model and a projection to a crypto-specific verifier.
