# Supplied typed-CNF regression fixture

This is the minimal retained input for the completed concrete-memory implication
instance. Tests load only these repository files. Historical captures, generated
Lean files, compiled objects and prior successful receipts are not inputs.

## Exact input schema

- `fixture.json` is one UTF-8 JSON object with exactly `format`, `profile`,
  `roots`, `declarations`, `nodes_sha256`, `cnf_sha256` and
  `certificate_sha256`. Format is `oak-typed-cnf-fixture-v1`; profile is
  `raw-implication-independent-ew-reads-v1`.
- `roots` has exactly `premise:104`, `left:207`, `right:371`.
- `declarations` contains exactly six `{name,width}` objects, sorted by name:
  `ew[?]:32`, `le.bytes_at:32`, `le.state_at:32`, `signed:1`, `v:64`, `width:32`.
- `nodes.jsonl` contains exactly 372 nonempty JSON-object lines, including the
  last newline. Every node has exactly `id`, `kind`, `width`, `declared`, `cond`,
  `left`, `right`, `value`, `name`, `op`, `args`. IDs are 0 through 371, in order.
  `kind` is the retained Go term kind (parameter 0, constant 1, binary 2,
  comparison 3, ITE 4, read 5). `width` is use width; `declared` retains the
  original declaration-width field. Absent children are -1; present children
  must precede their parent. `value` is an exact JSON uint64 integer, never a
  floating-point number. `args` is an explicit empty array. Each record creates
  a separate pointer even if its syntax equals another record.
- `raw.cnf` and `raw.lrat` are the exact ordered CNF and retained self-hosted
  RUP-only LRAT certificate. Their SHA-256 values are
  `ca659ecd4ed22d4e5d461edb10999857acfb6a008572baee77d0bd35cacb962a` and
  `3d189c4e459438315c2bef4485ae81dda1ad4c2e931a5ff6879c910fcbde66c4`.

The loader pins the manifest and node bytes as well as the CNF/proof. It rejects
missing, duplicate, case-folded or unknown fields, nulls, trailing JSON, invalid
UTF-8, integer overflows, incorrect declarations, topology and reachability.
Input caps are 4 KiB manifest, 64 KiB nodes, 256 KiB CNF and 512 KiB LRAT, with
the exact retained file sizes also checked. A node line is capped at 1 KiB.

## Mandatory gates and writer contract

`TestTypedCNFDurableFixture` independently replays the supplied instance and
compares generated CNF bytes exactly. The resulting circuit has 375 nodes,
353 inputs, 2,537 gates, 2,890 variables, five structural read blocks and 10,352
ordered clauses. The checker must finish without error under LRAT limits of
16,777,216 work, storage and count units, and 8 MiB formula/proof text caps.
Success requires 5,409 additions and 6,163 deleted IDs; the pinned certificate
ends with empty addition 15,761. Partial counts on an error confer no result.

`TestTypedCNFEmitInstance` repeats this complete gate before writing Lean source.
Set `OAK_TYPED_CNF_INSTANCE_OUT` to an absolute, clean, nonexistent directory with
an existing parent. The writer creates that directory exclusively. Without the
variable it uses a fresh child of the test's temporary directory; it never skips.
An explicitly empty variable, existing output, missing parent or failed write is
an error. Its exact initial inventory is `Data.lean`, `Checks.lean`,
`Nodes00.lean` through `Nodes14.lean`, and `Final.lean` (18 files). The aggregate
source cap is 8 MiB. The final proof includes the reviewed Bool/numeral
normalization. The separate portable pipeline transforms and kernel-checks these
initial files; Go test success alone does not prove their Lean propositions.

Focused normal/race controls are `TestTypedCNFFixtureJSONBoundaries`,
`TestTypedCNFFixtureManifestBoundaries`, `TestTypedCNFFixtureGraphBoundaries`,
`TestTypedCNFFixtureFileBoundaries`, `TestTypedCNFFixtureIdentityBoundaries`,
`TestTypedCNFFixtureCancellation`, and `TestTypedCNFInstanceWriterBoundaries`.
They cover exact uint64 decoding, malformed inputs, distinct identical nodes,
all four pinned identities, cancellation and exclusive bounded output.
The old opt-in `TestTypedCNFSavedCapture` remains a separate historical diagnostic
and intentionally binds a different certificate.

## Provenance and trust boundary

`provenance.json` records historical source/capture and closure hashes for review;
it is not a runtime dependency. The fixture retains the first 372 semantic nodes
of the historical capture and removes observational evaluator/cache fields.

The formal subject is this supplied generated typed model and its concrete-memory
implication. Capture fidelity and Go/parser projection remain reviewed,
hash-bound evidence. This is not a universal runtime, whole-compiler or target-code
refinement theorem, and it changes neither compiler admission nor Proven behavior.
