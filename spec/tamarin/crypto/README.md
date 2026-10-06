# Crypto protocol models

Run `go run ./spec/tamarin/crypto -out /tmp/oak-crypto-proofs` from the repo
root. Tamarin and Maude must be installed. `-tamarin` selects a binary and
`-timeout` bounds each invocation (default 2m). Missing dependencies do not
skip verification. Full output, exact model copies, and a JSON report with
model SHA-256 values are retained in the specified output directory.

| Model | Expected results | Scope |
| --- | --- | --- |
| `signed_dh.spthy` | Executability, server authentication, forward secrecy, one acceptance per client session: verified | One authentic server signing key, unbounded ephemeral DH sessions, adversarial network and signing-key compromise. No ephemeral/session-state reveal. Server authentication only, no client authentication or explicit server key confirmation. Ideal DH and signature/hash abstractions. Not TLS or an implementable protocol specification. |
| `unauthenticated_dh.spthy` | Executability and attacker-known session: verified; secrecy: falsified | Negative control demonstrating that arbitrary peer DH values do not authenticate a peer. |
| `acme_request.spthy` | Executability, request authentication and nonce single use: verified | Pre-registered authentic account keys, protected algorithm/account/nonce/URL/payload, endpoint binding, signature checks and linear server nonce state. Models account compromise. Does not model domain control or issuance. |

The client in the ACME model can sign arbitrary environment-supplied
payloads. Authentication means an accepted envelope was signed (or its key
was compromised), **not** that its payload was authorized by a user or
that a domain belongs to the requester. Signature and nonce acceptance are
modeled as one atomic step. A real implementation needs a durable atomic
nonce-consumption contract to refine this model under concurrency/crashes.

The current files are hand-written protocol models. They are not generated
from Oak source. `oak protocol -tamarin` is currently a specified future
projection, not an implemented security verifier. No connection between
these model proofs and compiled Oak bytes is claimed. See
[`stdlib/CRYPTO.md`](../../../stdlib/CRYPTO.md) for the refinement roadmap.

The verification runner checks every expected lemma, including the expected
attack; a missing lemma, incomplete analysis, warning, timeout or absent tool
fails. `RESULTS.json` is recorded local evidence, not a replacement for reruns.
