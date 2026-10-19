# Fixed three-artifact Lean audit

This development harness instantiates the existing restricted two-u32
AND/OR/XOR source-to-Wasm/ARM64/RV64 theorem on four exact input buffers. It does
not change compiler APIs, verified flags, or production admission by itself.
The model's existing native loading, alignment, address bounds, ARM register
inputs, and RV64 stack-frame assumptions remain in the universal theorem.
Physical fetch, OS/linker behavior, external ISA/Wasm refinement, and general
Oak compiler correctness remain outside its claim.

## Trust boundary

`spec/lean/Oak/CheckedBundleAudit.lean` is fixed trusted auditor code. A controlled
installation must own the pinned Lean 4.33.1 executable, the auditor/model source
closure and all imported `.olean` files and metadata, compile the closure from
that source with kernel checking enabled, and control the import search path.
Neither `--trust=0`, an axiom listing, a caller path, nor a self-declared hash
authenticates imported `.olean` files. In Lean 4.33.1 `collectAxioms` consults
trusted imported closure metadata. Rechecking a root proof against an environment
containing imports does not independently authenticate those imports.

The request renderer takes four immutable byte buffers. Each byte is serialized
as a decimal integer; source strings, filenames, theorem names, types, imports,
and commands cannot enter the Lean driver as code. Limits are 2,048 source bytes,
1,024 Wasm bytes, and 2,048 bytes per ELF. Empty and larger inputs refuse.

The fixed request declares:

- `source`, `wasm`: `List UInt8`
- `arm`, `rv`: `Oak.MinimalELF.Bytes`
- `declaration`: `(BitwiseSource.parse source).getD ⟨[], [], [], .and⟩`
- `admitted`: `BitwiseSourceObjectParity.check source wasm arm rv = some declaration`
- `binding`: the exact type of `accepted_source_object_binding admitted`
- `all_inputs`: the full type of `accepted_all_input_success admitted`

The last two headers use fixed `type_of%` expressions. The auditor independently
constructs the expected types from the fixed theorems and the exact definitions.
It waits on `Environment.toKernelEnv`, requires safe closed monomorphic data
and current-request theorem roots in that checked environment, rechecks their
values using `Kernel.check`, compares exact types using `Kernel.isDefEq`, and
checks every root's transitive axiom inventory. Only `propext`, `Quot.sound`, and
`Classical.choice` are allowed. Missing roots, wrong declaration kinds/types,
extra premises, metavariables/free variables, universe parameters, `sorryAx`,
and nonstandard axioms refuse. No arbitrary caller proof/type/audit is accepted
by the production request interface.

## Output contract

After all checks, `#oak_checked_bundle_audit` emits one compact JSON object with
exactly these keys:

- `schema`: `oak.checked-bundle.v1`
- `profile`: `bitwise-source-wasm-arm64-rv64-v1`
- `proof_package`: `698f6a7b013df508a831d391fe425f4f27cf4581`
- `lean_version`: `4.33.1`, checked against the running toolchain
- `source`, `wasm`, `arm`, `rv`: exact numeric byte arrays reduced by the kernel
- `declaration`: `name`, `first`, `second` numeric byte arrays and `op` (`and`, `or`, `xor`)
- `roots`: exactly the `admitted`, `binding`, `all_inputs` qualified names, in that
  order, each with `name` and `axioms`; names are under `Oak.CheckedBundleRequest`

`proof_package` identifies the semantic-package baseline, not the installed
application/auditor revision. Installation identity must separately bind that
source. Axiom arrays use Lean `Name.lt` order, not lexical string order.

A consumer MUST await successful process termination, strictly parse the entire
bounded output as one object (reject duplicates, unknown/missing fields, wrong
types, extra/trailing records), enforce the exact profile/root inventory and
axiom allowlist, and compare all four byte arrays with the immutable submitted
buffers. A record alone is not authority: an earlier or later Lean error can
coexist with valid theorem roots and an emitted record. Diagnostics and `#print
axioms` text never count as success. Cancellation, timeout, memory exhaustion,
process failure, or any discrepancy must produce no receipt.

## Reproduce

With the pinned toolchain on `PATH`, from `spec/lean`:

```sh
lake build Oak.CheckedBundleAudit
```

Run the bounded serial regression from the repository root:

```sh
python3 tools/checked_bundle/test_request.py -v
```

To retain process diagnostics, set `OAK_AUDIT_TEST_REPORT` to a JSON output path.
The suite uses `lean -j1 -M4096 --trust=0`, a 240-second per-process timeout, and
checks a real canonical production bundle plus adversarial mutations. Its fixed
inventory requires all 10 unittest methods and 24 named Lean processes with no
skips or expected failures. Each mismatched input also has an independent,
successful kernel proof that `check = none`; a failed admission process alone
is not treated as a semantic-refusal proof. The
canonical positive used about 2.34 GiB RSS and eight seconds on the October 19
host; `-M2048` fails closed on it. `-M` is Lean's allocator budget, not an OS RSS
limit. The consumer still needs external process/output/resource controls.

To regenerate the fixture with the current public compiler APIs (Go toolchain
from `go.mod`):

```sh
GOMAXPROCS=1 go run -p=1 ./tools/checked_bundle/emit --output /tmp/oak-bundle
python3 tools/checked_bundle/request.py \
  --source /tmp/oak-bundle/source.oak --wasm /tmp/oak-bundle/module.wasm \
  --arm /tmp/oak-bundle/arm.o --rv /tmp/oak-bundle/rv.o \
  --output /tmp/oak-bundle/Request.lean
cd spec/lean
lake env lean -j1 -M4096 --trust=0 /tmp/oak-bundle/Request.lean
```

The checked-in positive is 39 source / 45 Wasm / 688 ARM / 720 RV bytes, emitted
from the PR 769 source tree `430af5d65f7bc27e548a3b6366766bf441fbc31c`. Fixture
hashes and producer manifests are diagnostic provenance, not proof authority.
