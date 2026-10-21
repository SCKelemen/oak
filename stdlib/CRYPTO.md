# Oak crypto: implementation and verification plan

Baseline: `specification` at `7c8a08badda067b96afc55408df5c456393cf82b`.
This increment starts the crypto standard library. Go's `crypto` and
`golang.org/x/crypto` provide package and interoperability references; Oak
implementations use explicit storage, effects and ownership. This is not a
port of every historical algorithm or Go's implicit global entropy API.

**All new crypto APIs are experimental.** Public vectors and symbolic models
are present; implementation refinement, secret erasure and constant-time
preservation to ARM64 and RV64 are not yet proved. The existing SHA-256
streaming laws do not establish FIPS compression correctness. In particular,
the AArch64 SHA extension path remains a recorded trusted implementation.
No production-security or FIPS-validation claim follows from this increment.

## Implemented packages

| Import | Exports | Meaning and failure contract |
| --- | --- | --- |
| `crypto/x25519` | `public_key(private_key, out)`, `shared(private_key, peer, out)` | RFC 7748 X25519; exact 32-byte inputs; short output or all-zero shared secret fails unchanged; successful output preserves suffix. See [X25519 contracts and proof obligations](crypto/X25519.md). |
| `crypto/subtle` | `equal(a, b)` | Byte equality; lengths public. Unequal lengths return false. Equal lengths scan every byte in Oak source. No machine-level timing guarantee yet. |
| `crypto/hmac` | `sum256(key, message, out)` | RFC 2104 HMAC-SHA-256. Writes 32 bytes; short output returns false without mutation; a larger output retains its suffix. |
| `crypto/hmac` | `sum256_parts(key, a, b, c, out)` | Same MAC over `a ++ b ++ c`, without allocating the concatenation. Supports HKDF's previous-block/info/counter input. |
| `crypto/hmac` | `verify256(key, message, tag)` | Accepts only a matching full 32-byte tag. Other lengths return false. |
| `crypto/hkdf` | `extract256(salt, ikm, out)` | RFC 5869 Extract, SHA-256. Empty salt has the RFC default semantics. Writes 32 bytes, preserving any suffix; short output is unchanged. |
| `crypto/hkdf` | `expand256(prk, info, out)` | Fill exactly `len(out)` bytes. Require `len(prk) >= 32` and `len(out) <= 8160`; otherwise return false without mutation. A valid PRK and zero output succeed. |
| `crypto/hkdf` | `key256(salt, ikm, info, out)` | Extract then Expand. More than 8160 output bytes fail without mutation. |

All inputs are borrowed read-only views; outputs are exclusive mutable spans.
Ordinary Oak borrowing requires disjoint input and output storage. All work
is deterministic and allocation-free, with no I/O, clock or entropy effect.
Different calls may execute concurrently with disjoint writable storage.
Malformed storage supplied through unsafe/FFI remains outside safe callers'
contract. The Bool failure surface is provisional until crypto error types
and opaque secret types stabilize.

HMAC costs O(key bytes + message bytes), with constant auxiliary storage.
HKDF Extract has HMAC's cost. Expand uses `ceil(L/32)` HMAC operations over
the PRK, up to 32 previous bytes, info, and a counter; the current implementation
recomputes the HMAC pads per block. Auxiliary storage is constant; output is
caller-owned. Three u32-sized message parts keep each HMAC input comfortably
below SHA-256's byte-length limit. Key length and message/output lengths are
public metadata. No function silently obtains randomness. HKDF is not a
password hashing function and raw DH output is not an application key.

The value-based SHA implementation copies secret intermediates. Guaranteed
erasure of copies, stack spills, and registers is future compiler/runtime
work; adding an ordinary clearing loop would not close that obligation.
These APIs deliberately do not expose a forgeable public incremental MAC
state. A later streaming API needs an opaque, invariant-preserving state and
checked total-length accounting.

## Package scope

Names below are planned unless the status says implemented. None become
stable before their proof gates close on **both ARM64 and RV64**.

| Area / planned import | Scope | Go reference | Next evidence |
| --- | --- | --- | --- |
| `crypto/subtle`, `crypto/secret` | Equal/select/swap; secret owners, opaque keys, controlled export and destruction | `crypto/subtle`, opaque key interfaces | Functional laws, leakage trace semantics, copy/erase accounting |
| `crypto/rand` | Fallible entropy capability; OS and freestanding realizations; rejection sampling | `crypto/rand` | Host contracts, entropy failure tests, no deterministic fallback |
| `crypto/sha256`, `crypto/sha512`, `crypto/sha3` | SHA-2, SHA-3, SHAKE; reuse existing `hash.sha256` during migration | Corresponding `crypto` packages | FIPS 180-4/202, NIST vectors, compression refinement |
| `crypto/blake2` | BLAKE2b/s; existing BLAKE3 stays separately identified | `x/crypto/blake2b`, `blake2s` | RFC 7693 and upstream vectors |
| `crypto/hmac`, `crypto/hkdf` | SHA-256 implemented; SHA-384/512 after digest foundations | `crypto/hmac`, `crypto/hkdf` | RFC 4231/5869, extraction/expansion laws, implementation refinement |
| `crypto/aead` | AES-128/256-GCM, ChaCha20-Poly1305, XChaCha20-Poly1305 | `crypto/aes`, `cipher`, `x/crypto/chacha20poly1305` | NIST GCM, RFC 8439, Wycheproof; no plaintext release on tag failure |
| `crypto/ecdh` | X25519 first; NIST P-256, P-384, P-521 | `crypto/ecdh`, `x/crypto/curve25519` | RFC 7748, NIST, Wycheproof; field/ladder/validation proofs |
| `crypto/ed25519`, `crypto/ecdsa` | Ed25519; NIST ECDSA; explicit message/prehash/context profiles | `crypto/ed25519`, `ecdsa` | RFC 8032, FIPS 186-5, RFC 6979 when selected, Wycheproof |
| `crypto/rsa` | PSS and OAEP; PKCS#1 v1.5 signature interoperability for Web PKI/ACME | `crypto/rsa` | RFC 8017, NIST/Wycheproof; blinding and parsing proofs |
| `crypto/password` | Argon2id preferred; scrypt/PBKDF2 and bcrypt for explicit compatibility | `x/crypto/argon2`, `scrypt`, `bcrypt`; `crypto/pbkdf2` | RFC 9106/7914/6070, resource ceilings, parameter policy |
| `crypto/mlkem`, `crypto/mldsa` | Standardized PQ primitives and explicitly named hybrid profiles | Go's ML-KEM / ML-DSA packages | FIPS 203/204, NIST ACVP; separate computational assumptions |
| `crypto/hpke` | RFC 9180 suites, modes, context binding, sequence limits | `crypto/hpke` | Official HPKE vectors; mode-specific Tamarin models |
| `encoding/asn1`, `encoding/pem`, `crypto/x509` | Bounded DER, SPKI, PKCS#8/10, certificate creation and path validation | `encoding/asn1`, `pem`, `crypto/x509` | Adversarial parser tests, X.509 Limbo, name/constraint/time policies |
| `crypto/jwk`, `crypto/jws` | JWK import/export and thumbprints; strict JWS profiles | Go primitives; RFC 7515/7517/7518/7638 | RFC 7520 vectors, duplicate fields, key/alg confusion rejection |
| `crypto/tls` | TLS 1.3 client/server, certificate verification, resumption; 0-RTT disabled initially | `crypto/tls` | RFC 8448 traces, interoperability, transcript/key schedule/record models |
| `crypto/ocsp` | Parse/verify OCSP under explicit freshness and responder policy | `x/crypto/ocsp` | RFC 6960, revoked/unknown/stale responses |
| `crypto/acme`, `crypto/acme/autocert` | RFC 8555 client and certificate lifecycle automation | `x/crypto/acme`, `acme/autocert` | Request model now; issuance models and Pebble integration next |
| `crypto/ssh` | Modern SSH transport and authentication, agent/key interfaces | `x/crypto/ssh`, `ssh/agent`, `ssh/knownhosts` | Interoperability, host-key policy, rekey/authentication models |
| Optional compatibility | Fixed RFC 7919 FFDHE groups; explicitly requested legacy formats | Relevant Go interoperability APIs | Separate review and validation profiles; no arbitrary caller-selected DH groups |

MD4, MD5, SHA-1 signing, DES/3DES, RC4, obsolete TLS/SSH suites, unauthenticated
encryption defaults, and deprecated `x/crypto` protocols do not enter the
modern stable surface merely because Go has retained compatibility APIs.
The scope table is a staged proposal, not a claim of present implementation.

## Safe interfaces and dependencies

Typed signing keys, verification keys, DH private/public keys, shared secrets,
AEAD keys, and derived application keys must remain distinct. Signature
schemes and accepted JWS algorithms are policy inputs, never inferred from
untrusted headers. Key generation consumes an explicit entropy capability;
test randomness has a separate realization that production cannot select
silently. Remote/HSM signers fit a narrow capability with declared effects.

AEAD opening must authenticate before exposing plaintext, or use scratch
storage with a proved failure cleanup contract. Nonce length and uniqueness
belong to the key's algorithm profile. High-level sealers own counters or use
a specified random-nonce construction, fail on exhaustion, and preserve nonce
uniqueness across restart. AAD is mandatory in interfaces even when empty.

The dependency order is byte/bit arithmetic and secret storage -> digest/MAC/
KDF/AEAD/curve arithmetic -> signatures/key exchange -> key and certificate
encoding -> authenticated transports -> certificate automation. Protocols
consume explicit network, clock, trust-store, entropy, and persistence
capabilities. Deterministic protocol simulation tests faults in those ports;
production crypto must never depend on the simulation PRNG.

“Web crypto” includes both Web PKI protocols and a possible browser WebCrypto
adapter. The latter is a separate realization with key-usage/extractability
checks and raw/JWK/SPKI/PKCS#8 interoperability tests. A host browser operation
is an explicit trust boundary, not a proof of Oak's own primitive.

## Diffie–Hellman milestone

Implement fixed-width Curve25519 field arithmetic and a ladder with no
secret-dependent control flow or memory access; prove arithmetic bounds and
reduction before target optimization. X25519 follows RFC 7748 decoding,
clamping and high-bit handling. Reject the all-zero shared result in the
high-level agreement API, including malicious low-order inputs. This does
not mean rejecting every noncanonical u-coordinate: the RFC's decoding rules
must be respected. NIST ECDH separately validates scalar ranges and public
points, rejects infinity and wrong-curve keys, and specifies encodings.

The output is a `SharedSecret`, requiring a named KDF/profile and a context
binding the identities, roles, algorithm, transcript and intended purpose.
Raw DH establishes no peer identity. Authentication comes from a reviewed
protocol, such as TLS or an admitted HPKE mode, with its own model. The
signed-DH model in this increment is a proof exercise, not a new wire protocol
and not an implementation of TLS.

## ACME milestone

Build the client state machine around a caller-supplied signer, HTTP transport,
clock, persistence and challenge provider. A deployable implementation needs:

1. Directory discovery, account registration and external account binding
   (EAB); canonical JWK thumbprints and distinct account/certificate keys.
2. Flattened JWS, algorithm policy, exactly the required `jwk` or `kid`,
   signed request URL, replay-nonce storage, bounded `badNonce` retries and
   POST-as-GET. Sign the exact payload bytes; reject duplicate JSON members.
3. Order/authorization/challenge transitions and legal polling. Bind every
   authorization to its account, order and identifier set. HTTP-01 and DNS-01
   first; TLS-ALPN-01 follows with its RFC 8737 certificate profile. Wildcard
   handling and challenge suitability are explicit policy.
4. CSR generation and proof of possession; finalize only authorized orders;
   validate returned certificate public key, identifiers, chain and validity.
5. Account key rollover, revocation, cancellation, rate-limit/Retry-After
   handling, bounded responses and redirect policy. No unchecked endpoint
   traversal or automatic issuance for arbitrary input hostnames.
6. `autocert`: explicit host allowlist, crash-safe storage, renewal locks,
   atomic certificate replacement, recovery, and RFC 9773 ARI scheduling.

Extend Tamarin to model account creation/EAB, account-key compromise and
rollover, domain control/challenge observations, issuance authorization and
revocation. Model HTTP/DNS validation and TLS assumptions explicitly. Add
negative controls for nonce reuse, substituted account keys, cross-endpoint
requests, CSR substitution and challenge/order mix-ups. Prove reachability
as well as safety. Pebble integration supplies protocol interoperability;
there is no single public vector corpus that proves all ACME behavior.

## Evidence layers and release gates

| Layer | What it establishes | What remains outside that claim |
| --- | --- | --- |
| Public vectors and Go differential tests | Concrete primitive outputs and rejection behavior | All-input correctness, protocol security, timing |
| Oak/Lean functional refinement | Oak bodies implement mathematical algorithms and contracts | Hardness assumptions, leakage and platform behavior unless modeled |
| Tamarin | Symbolic trace properties for the exact protocol model and assumptions | Byte parsers, curve arithmetic, entropy quality, constant time, computational reductions |
| Protocol implementation refinement | Every admitted implementation trace maps to the proved model | Host capability guarantees beyond the stated contracts |
| Target verification | Compiled ARM64 and RV64 bytes preserve functional and leakage semantics | Unmodeled microarchitecture, hardware faults and external services |

For every stable operation bind evidence to source/model/vector digests,
compiler/checker versions, target profile, enabled optimizations, final linked
bytes and explicit assumptions. Mark each layer independently as pending,
tested, modeled, or proved. Tamarin remains an external analysis tool; its
output is not an Oak-kernel proof certificate in this increment. Oak's v1
self-hosted proof requirement needs a sound independently checked evidence
path or self-hosted equivalent, plus protocol-to-code refinement.

Constant time needs a relational leakage model: secret values may vary while
public lengths/policy remain fixed; branch outcomes, memory addresses and
admitted instruction timing observations must agree. Check portable code,
optimizer transformations and accelerated implementations separately on both
targets, with explicit instruction/CPU assumptions. A branchless source loop,
timing benchmark, or successful test-vector run is insufficient evidence.
The same applies to zeroization and secrets copied by the ABI.

## Public test sources and reproducibility

This increment embeds all seven SHA-256 cases from RFC 4231 in
`compiler/e2e_crypto_test.go`, including the case whose published tag is
truncated (tested as an output prefix; the verification API rejects truncated
tags). It embeds SHA-256 cases A.1–A.3 from RFC 5869, checking both PRK and
OKM, and the combined API. The tests run the Oak interpreter and C-backed
executable. Additional Go-oracle tests cover HMAC key/message boundaries and
HKDF output lengths 0, 1, 31, 32, 33 and 8160; invalid lengths and untouched
output regions are checked. The maximum HKDF case runs compiled only.

As primitives land, import applicable NIST CAVP/ACVP and Wycheproof files by
immutable upstream commit plus SHA-256 and license/provenance. Preserve test
IDs and flags. `valid` must succeed, `invalid` must reject, and `acceptable`
needs an explicit per-profile disposition. Fail on unknown schemas/flags,
unexpected counts, or zero executed cases. An absent Oak algorithm is
**unsupported**, never a passing test obtained by running only Go.

```sh
go test ./compiler -run '^TestE2ECrypto' -count=1
go test ./spec/tamarin/crypto
go run ./spec/tamarin/crypto -out /tmp/oak-crypto-proofs
```

The runner requires Tamarin and Maude, fails on missing tools, warnings,
timeouts or missing/wrong lemma results, and retains full proof output plus
source SHA-256 values. It expects the raw-DH secrecy lemma to be **falsified**.
`spec/tamarin/crypto/RESULTS.json` records a local run; CI reruns the models.
The CI download pins are Tamarin 1.12.0 and Maude 3.5.1. These are bootstrap
tools, not new release-runtime dependencies.

## Implementation sequence

| Gate | Deliverable and completion condition |
| --- | --- |
| C0 (this increment) | HMAC/HKDF implementation, RFC vectors, bounded API failures, three executable protocol models and strict result checking. Functional/machine proofs remain open. |
| C1 | Entropy/secret storage and leakage semantics; SHA-256 compression and HMAC/HKDF refinement, including negative output/storage contracts. |
| C2 (in progress) | Portable X25519 field/ladder/encoding, RFC 7748 vectors, Go differential/field tests and byte-view HKDF composition implemented. Field/ladder/target proofs, Wycheproof, typed secrets and extended compromise/key-confirmation cases remain open; see [X25519](crypto/X25519.md). |
| C3 | Ed25519, P-256 ECDSA/ECDH, SHA-512, AEAD; common certificate and Web PKI cryptographic dependencies with public vectors and target proofs. |
| C4 | Strict DER/PEM/JWK/JWS, CSR/X.509, explicit verification policy; parser fuzzing and cross-implementation testing. |
| C5 | ACME client and challenge lifecycle, then autocert/ARI; Pebble plus implementation refinement to the extended Tamarin models. |
| C6 | TLS 1.3, remaining modern Go/x/crypto scope, HPKE/PQ and SSH with per-profile proofs and interoperability. |
| C7 | Full stable crypto corpus self-hosted and proved through final ARM64 and RV64 executable bytes; no target deferral. |

## Primary references

- [Go crypto](https://pkg.go.dev/crypto), [x/crypto](https://pkg.go.dev/golang.org/x/crypto), [ECDH](https://pkg.go.dev/crypto/ecdh), [ACME](https://pkg.go.dev/golang.org/x/crypto/acme).
- [HMAC vectors, RFC 4231](https://www.rfc-editor.org/rfc/rfc4231), [HKDF, RFC 5869](https://www.rfc-editor.org/rfc/rfc5869), [X25519, RFC 7748](https://www.rfc-editor.org/rfc/rfc7748).
- [ACME, RFC 8555](https://www.rfc-editor.org/rfc/rfc8555), [ARI, RFC 9773](https://www.rfc-editor.org/rfc/rfc9773), [WebCrypto](https://www.w3.org/TR/webcrypto/).
- [Tamarin manual](https://tamarin-prover.com/manual/master/book/001_introduction.html), [Wycheproof](https://github.com/C2SP/wycheproof), [NIST CAVP](https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program), [Pebble](https://github.com/letsencrypt/pebble).
