# Raw Oak complete-image admission

The additive [strict native writer](94-selfhost-bitwise-elf.md) and
[complete Wasm writer](91-selfhost-bitwise-module.md) feed the existing,
unchanged `ImageInstallation.CheckImageBundle` through
`TestSelfHostedBitwiseImageBundleReal`. This is a bounded producer-and-checker
integration, not an Oak source-consuming compiler.

## Exact bytes and original source

The six requests are AND, OR and XOR for `bitwise(x,y)` and for
`Mix9(left,right)`. The driver retains each complete canonical source, including
its final LF, and supplies name/op and fixed native linked-text proposals to the
Oak writers. The native body is opaque to its envelope writer. The unchanged
checker alone binds the original source to the complete artifacts.

The harness compiles the Oak generators through the Go seed's `EmitC` and the
system `cc`. It captures binary stdout as owned bytes without trimming. Native
records carry the Oak-reported file length and every caller-buffer byte;
the harness checks the reported bounds and untouched sentinel suffix before
copying precisely that file extent. Wasm stdout contains precisely the complete
Oak-reported module; compiled-Oak assertions check size and untouched suffix.
No Go-built metadata, re-encoding, parsed-image reconstruction or normalization
is inserted into any captured artifact.

Each tuple is independently compared byte-for-byte with fresh Go `EmitWasm`
and fresh Go native objects plus the production `asm.WriteExecutable`, compiled
from the same original source snapshot. Diagnostic lengths and SHA-256 hashes
identify these files but do not confer admission. Only the original source and
the three captured Oak byte slices are passed directly to `CheckImageBundle`.
The public compiler convenience bundle API is deliberately not used: it would
regenerate Go artifacts. The resulting receipt and copied bytes must identify
the same source and complete captured files. Setting the optional
`OAK_SELFHOST_IMAGE_CORPUS_OUT` directory retains those exact four files and a
diagnostic receipt for each admitted tuple; serialized receipts cannot restore
checked authority.

Twenty-six controls mutate actual captured output or replay it against a
same-length changed source name/operation. They cover module names/bodies,
native names/bodies/startup/entry/flags/symbols/sections/padding, truncation and
trailing bytes. Each must reach the real proof/auditor refusal with exit status
1 and its checked refusal marker. A timeout, crash, missing tool or setup error
is a failure, not evidence that the mutation was refused.

## Required gates

The existing `checked-image-bundle.yml` workflow has a separate required job
with two race-instrumented suites in `required_backend_tests.py`:

- `selfhost-image-producers`: every native corpus child, every Wasm success and
  refusal child, both new Wasm Extract and Faithful roots together, the native
  extraction probe, and all six complete-file parity tuples
- `selfhost-image-admission`: all six direct raw-tuple admissions and every
  mutation refusal child

The exact live Go test inventory is checked, and the runner rejects missing
roots/children, unlisted children, every nested skip, malformed test output and
nonzero exit. The Wasm filenames end in `_wasm_module_test.go`, avoiding Go's
architecture-specific `_wasm_test.go` filtering. The new job sets
`OAK_REQUIRE_SELFHOST_IMAGE_PRODUCERS=1`, `OAK_REQUIRE_WASM_LEAN=1` and
`OAK_REQUIRE_BITWISE_IMAGECHECK=1`. Missing C, Lean or the exact official archive
is a hard failure. Faithful builds the extracted writer and early-guard module
and checks all finite complete-array claims in the kernel. Existing checker
source/runtime/compiler inventories and old workflow jobs remain intact.

With the existing approved Go/C/Lean tools and exact official offline archive:

```sh
export OAK_REQUIRE_SELFHOST_IMAGE_PRODUCERS=1
export OAK_REQUIRE_WASM_LEAN=1
export OAK_REQUIRE_BITWISE_IMAGECHECK=1
export OAK_BITWISECHECK_LEAN_ARCHIVE=/path/to/lean-4.33.1-linux.tar.zst
python3 .github/scripts/required_backend_tests.py --check
python3 .github/scripts/required_backend_tests.py selfhost-image-producers
python3 .github/scripts/required_backend_tests.py selfhost-image-admission
```

## Remaining trust and proof boundaries

Exact finite output parity and per-request checked admission do not prove the
Oak writer universally correct. Native successful output/refusal/frame
refinement remains open. The Wasm extraction, four scoped early-guard lemmas
and finite kernel correspondence likewise leave universal envelope success,
loop/fuel/arithmetic/footprint and total refinement obligations open. Existing
assembler lemmas are reusable foundations, not a completed envelope join.

The Go seed, extractor and system C compilation remain trust boundaries. The
name/op driver does not parse original Oak source in Oak. The native linked-text
proposals do not prove the general self-hosted linker. Existing checker closures,
digests, acceptance profiles, proof premises and runtime authority are unchanged.
No whole-language compiler correctness, full self-hosting, Linux process/ECALL
completion, hardware execution or reset reachability follows. A 4.33 admission
receipt is not portable execution authority in the separate 4.29 Sail bridge;
that bridge would have to freshly check these exact complete bytes under its
existing model, register, memory, stack and clock premises.
