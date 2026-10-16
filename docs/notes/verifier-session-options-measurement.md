# Verifier session options: measured scope and open performance finding

The session-options change captures OFF, BUDGET and ONLY for one verification
run and propagates that immutable configuration through its proof owners. Cache
identity version 6 binds the captured configuration. Options and their digest
identify configuration; they are not proof evidence. The change does not claim
complete isolation from the process environment.

## Fixed comparison

The comparison used baseline tree
`b69bb31a7240222e7e785c2a6bb4e5ea26f79579` and options-only tree
`cd23d82e268acd27b9528574bce65915ea5d546d`. It excludes the later checked-CNF
ownership and implication-timing changes.

Both versions compiled the same `u32` identity function through a fresh public
`Compilation.Check`, targeting Linux/ARM64 without executing ARM machine code.
Two configurations, default and `OFF=components,BUDGET=base`, each used six
alternating AB/BA blocks with four cold/warm pairs per version. The fixed screen
completed 24 child processes and 216 checks, including 24 uncached
`VerifyFresh` controls. Each executable warmed its own verdict-cache namespace;
the intentional v5-to-v6 migration miss was not timed.

All normalized reports matched: the same selected body and recipe, 24 candidates
considered and materialized, one real validation, and the same non-transient
Proven linear-form result. There were 96 cold misses, 96 warm hits and 24 fresh
controls. These observations establish the fixture's proof/cache comparability,
not native execution or coverage of large and bounded-child-heavy proofs.

## Performance remains qualified

| Configuration/state | Median paired candidate/baseline | Median paired difference |
|---|---:|---:|
| Default, cold | 0.885666 | -0.449 ms |
| Default, warm | 0.896831 | -0.361 ms |
| Components, cold | 1.269807 | +1.025 ms |
| Components, warm | 0.916276 | -0.269 ms |

Each pair compares medians of four calls within a matched process block; the
table reports the median of six paired ratios or differences. Pooled medians
are different estimators and must not replace these figures.

**Components/cold showed an unresolved +26.98% paired median time increase
(+1.025 ms), with four of six blocks more than 5% slower.** The predeclared coarse
flag required both a paired median above 1.10 and at least five of six blocks
above 1.05. It did not fire because the second condition was not met. This is
not a finding of no regression, equivalence, zero overhead or a speedup.

Components/cold individual samples ranged from 2.857 to 5.770 ms for baseline
and 3.042 to 7.354 ms for candidate. Slower candidate blocks occurred in both
orders and later in the fixed schedule. The observations do not distinguish
version cost from temporal or GC variation. Allocation medians were about
2.20 MB per cold call and 2.11 MB per warm call, with small nonzero differences;
unchanged allocations are not claimed.

The candidate captures and parses configuration before every Check, and hashes
three raw options into the cache key. A miss creates a verification session;
a hit bypasses its proof work. The baseline captured OFF through a process-global
`sync.Once` and deferred budget parsing. The fixture's linear proof returns
before component reasoning, so the components configuration measures capture
and keying around that proof rather than component reasoning throughput.
No phase timing in this experiment attributes the observed increase to an
individual operation.

The performance finding remains open. A causal claim would need a representative
phase profile or independently planned comparison; changing the threshold after
seeing these data would not resolve it. Broader hosted correctness, native-host
cache behavior and native cold-producer completion remain separate obligations.

## Evidence identity

- Comparison SHA256:
  `55ac9821040abd1a2fe5f09a006313be86ac695ed0c0e036a878d567e1dd7e1d`
- Complete raw log SHA256:
  `c3d126fa3f39cc341149814d6d0b530a1a04548d440b46309d9cb6db5ec5b8dc`
- Independent descriptive interpretation SHA256:
  `7da890640d802c3791a5b354d0afaa1d5f32ccb323670bfe147618e72d5e7836`

The screen is finite and host-specific. It provides no statistical confidence
bound or whole-compiler performance claim. Failed preparation attempts remain
part of the retained validation record.
