# Bounded reader and APDU length models: evaluation scope

This slice adds `encoding/reader`, `smartcard/apdu`, four implementation tests and two handwritten Lean models. The parser covers the reviewed seven structural command-length cases: case 1 and short/extended cases 2, 3 and 4. It returns header values, a payload offset/length and optional response length. It retains the specified length-error priority, zero-sentinel response values, exact-consumption checks and bounded-reader rejection/nonmutation contracts.

This is a partial structural parser. It does not implement command authorization, application selection/state, chaining/reassembly, secure messaging, response processing, credential handling or a FIDO2, PIV or OpenPGP protocol. No complete ISO APDU or other protocol conformance is claimed.

The reader/APDU Oak bytes passed a prior finite diagnostic host gate: four exact roots, four successful C compilations and four normal generated-program exits of 42, alongside their interpreted checks. That gate used a diagnostic helper. The portable test restores the existing `buildPackageAndRun` call and preserves every fixture/assertion, including 30 named-Bool initializers. The current portable helper/compiler combination requires its own hosted four-root PASS evidence. Historical generated C/product hashes are observations; successful raw artifacts were not retained. Diagnostic and portable helpers do not have equivalent failure reporting, timeout, output or resource behavior.

The exact Lean v2 sources compiled successfully, and their resulting objects passed a separate actual-environment audit: 48 named theorem terms, 15 compiled anonymous examples, 500 candidate declarations and 1,049 imports. Only `propext`, `Quot.sound` and `Classical.choice` occurred as axioms. The evidence is a composition of the clean two-module compilation prefix and a successful audit of those exact objects; the earlier whole invocation remains failed. Module headers preserve their original candidate wording; this note records the subsequent checked status.

The proofs concern the handwritten abstract models: seven-case uniqueness/completeness, exact rejection cases, mathematical offset/length bounds and conditional no-u32-wrap bounds, plus construction-level frame facts. They are not extracted Oak proofs or implementation refinement. The connection from Oak reader operations to mathematical values/accesses, machine UInt and endian representation, copied headers, physical alias/nonmutation behavior and compiled behavior remains open. Imported official Lean objects are trusted in the normal way; they were not freshly kernel-rechecked.

The mandatory hosted gate locks the exact source identities, recompiles the two modules in a fresh private object directory and audits their complete theorem/dependency/axiom inventory. Source locking preserves the reviewed theorem statements and anonymous examples. The owner/name/private/kind audit is not an independent restatement of theorem signatures. The ordinary aggregate proof build and existing audits remain required, and generic CI success cannot substitute for evidence that all four APDU roots actually passed.

## Generated-reader refinement evidence

A later bounded local gate compiled the actual qualified-reader extraction and
proved the preserved refinement candidate. Independent audit accepted 117 named
propositions, including 18 finite controls, 753 owned declarations and 1,050
imports. Reconstructed dependencies contained 2,966 nodes and 50,627 edge
occurrences; only `propext`, `Quot.sound` and `Classical.choice` were reachable.
The raw extraction is SHA-256
`56c1ffe193a13469472c1710b4873c8c6b5200be54d678658e2a55bb1cf04df1`;
the committed profiled module is
`94f44f3e034bd421c1653304d5b8cb6558a2440f595854af962a2088fe08a335`.
Profiling changes only the two header budgets. The accepted refinement source is
`21f8c9bf4956e21a192a31192d70bddf997baf0e5f325450315b99ca42ec50b8`.

This establishes refinement of the generated Lean definitions of window,
remaining, take and read-u16-be against the bounded-reader mathematical model,
including all UInt32 states/counts and all extraction fuel under the stated
source-size assumption. Errors, successful byte value, safe logical indices,
nonwrapping arithmetic and returned cursor state are covered. The exact theorem
statements remain in `BoundedReaderRefinement.lean`.

The original seven-case APDU length model is still an abstract-model proof.
Neither that model nor the new generated-reader proof establishes the correctness
of the Oak loader/checker/extractor, ordered physical reads, input alias/frame
behavior, emitted C or machine execution. There is no FIDO2, PIV, OpenPGP or full
ISO protocol-conformance claim.

The new mandatory workflow job performs fresh current-source qualified extraction,
requires raw/profiled/receipt equality and runs fresh compilation plus full audit.
It also requires all four portable APDU/reader roots without skips. Existing
abstract-model checks stay mandatory. At source integration time this hosted
composition has not run; local accepted results do not transfer an exact hosted
pass. Workflow selection does not change repository branch-protection settings.
Full audit and extraction artifacts allow independent replay; see
`spec/lean/reader_apdu/README.md` for limits and the explicit hosted trust boundary.

Local independent terminal review SHA-256:
`16a5a34f7c9fae4d396afd7204414a00945b9d819f263e9c3cf90013503d49b4`.
Final composed evidence-manifest SHA-256:
`4235f4f6322396c06f0a29628bb3d7dfd3db616f0c7d9b73d40a72eee2b1d460`.
These identify retained local review authorities; they are not remotely available
proof artifacts or a substitute for the new hosted result.
