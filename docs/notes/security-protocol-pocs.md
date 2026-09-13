# Security protocol proof-of-concepts

Status: experimental pilots on `poc/security-protocols`.

These pilots test whether Oak can keep executable security-protocol state machines, theorem statements, generated test actions, and TLA+ projections close to one semantic source definition.

## Pilots

`examples/testing/security_protocols_test.oak` contains three deliberately small models:

1. **Authenticated handshake plumbing** — the session may enter `Established` only after peer authentication, transcript binding, and shared-secret readiness have all been established.
2. **One-use ratchet key lifecycle** — deriving a message key moves the machine out of `Ready`; another key cannot be derived until the current message key is consumed. Closing the ratchet clears both live-key flags.
3. **Challenge-bound sealed-key authorization** — a protected operation requires user-presence evidence plus challenge binding, and consuming or expiring authorization returns the machine to a state with no live authorization.

Each model has executable tests and protocol-invariant theorem candidates. Because Oak protocol declarations project to ordinary Oak state/step/data types, they are also suitable for generated property histories and `oak protocol -tla` model generation.

## What these proofs mean

These POCs verify **protocol plumbing and lifecycle invariants**. They do not establish computational cryptographic security.

In particular, the handshake model treats authentication, transcript binding, shared-secret derivation, AEAD, KDFs, signatures, and key agreement as idealized boundaries. A proof that an Oak state machine only reaches `Established` after an `auth_ok` transition is not a proof that an attacker cannot forge authentication.

The intended verification stack is:

```text
Oak types/resources
    make key/evidence classes distinct and constrain ownership

Oak theorem + Lean extraction
    local algebraic and lifecycle invariants

Oak protocol + TLA+
    transition safety, ordering, fairness, bounded state, liveness

property/DST tests
    implementation behavior under generated histories and faults

cryptographic protocol verifier
    adversarial secrecy/authentication/forward-secrecy claims
```

A future symbolic-security projection should target a tool such as Tamarin, ProVerif, or an equivalent verifier rather than pretending that TLA+ or ordinary functional correctness proves cryptographic indistinguishability.

## Desired next language abstractions

These pilots intentionally avoid introducing new syntax, but they motivate several reusable abstractions:

- nominal `PrivateKey`, `PublicKey`, `SharedSecret`, `ChainKey`, `MessageKey`, `Nonce`, `Signature`, and `Ciphertext` types even where representations have identical widths;
- resource/linear `Secret[T]` values for one-use or non-copyable secret state;
- secure-destruction semantics for `Secret[T]` rather than merely making an old value unreachable in source;
- opaque `KeyHandle[Purpose, Policy]` values for hardware-backed non-exportable keys;
- `Authentication[...]` and `Attestation[...]` evidence values rather than Boolean authorization flags;
- explicit cryptographic assumptions at trusted primitive boundaries;
- a symbolic attacker/network projection from an Oak protocol definition.

## Candidate next pilots

The next useful progression is deliberately incremental:

1. replace the handshake's Boolean idealizations with nominal key/evidence types;
2. make `MessageKey` and `ChainKey` resources and prove one-use/consume behavior through the resource checker;
3. build a Noise-style two-party handshake using idealized DH/KDF/AEAD primitives and official vectors;
4. model a symmetric ratchet with bounded skipped-key storage and out-of-order receive;
5. model Double Ratchet state evolution;
6. add a symbolic adversary projection and compare a generated model with a dedicated cryptographic verifier;
7. only then evaluate a Signal/PQXDH-compatible implementation against official/reference test vectors.

The goal is not to replace mature cryptographic analysis tools. It is to minimize drift between the protocol that is analyzed and the program that actually runs.
