# Local Oak playground prototype

Build from the repository root:

```sh
sh playground/build.sh
python3 -m http.server 8000 --bind 127.0.0.1 --directory playground/web
```

Open `http://127.0.0.1:8000`. The source stays local. The plain textarea editor,
compiler worker, execution worker, diagnostics and Wasm download require no CDN
or package installation. The generated `oakc.wasm` and matching Go
`wasm_exec.js` are ignored build artifacts, not checked-in binaries.

The example sums 0 through 99 and returns 4950. Run invokes a zero-argument
`main`; other functions are exported for programmatic use. Only the documented
[scalar profile](../docs/spec/91-wasm.md) is accepted. The CLI alternative is
`oak build -target core/wasm32 -o program.wasm program.oak`.

Scalar v1 includes signed/unsigned 32- and 64-bit division and remainder.
Zero divisors trap; signed overflow preserves Oak's wrapping result. The page
requires matching v1 profile/validator reports. Rebuild the compiler assets and
reload the page together after updating; stale v0 reports are not accepted.

Single returning blocks, acyclic CFGs up to 127 blocks, and one pre-test loop
with an acyclic body up to 124 blocks omit the dispatcher/PC local; other CFGs
keep the dispatch baseline. See the
[measured fixture sizes](../docs/spec/91-wasm.md#four-block-conditionals-with-a-join) and
[preliminary engine timings](../benchmarks/wasm/README.md). This does not reduce
the Go compiler payload or establish a general browser runtime speedup.

“Compile only” produces a downloadable module without executing it or requiring
`main`. Artifact information includes the compiler's target and DAG provenance.
The page checks hashes against the actual source and module bytes before
publishing the artifact; editing or stopping discards stale hash completions.
Serve over localhost or HTTPS for WebCrypto's secure-context requirement.

Source checking, Oak byte/type validation and engine validation are shown
separately from the missing
formal translation proof. This is **not** a fully verified backend or a
production deployment of try.oak.dev. No domain or hosting is configured.

The compiler worker is reused for up to 32 completed requests, then recycled;
60 seconds idle also releases it. Every request constructs a fresh compilation:
no symbols, DAG artifacts, diagnostics or verdicts are cached between sources.
Requests carry a protocol version and monotonically increasing ID. Startup has
a 90-second deadline; compilation has 10 seconds. Editing cancels active work
by terminating its worker, but retains an idle runtime. Ordinary source errors
do not discard the runtime. Stop discards it, including during guest execution.
Each execution still has a separate disposable worker and a 2-second deadline.

Source-bound diagnostics retain compiler codes, severities and zero-based
UTF-16 ranges. Click a located diagnostic to select its source; unlocated
backend/profile refusals remain plain text. The API caps diagnostics at 64,
each message at 8 KiB. The UI checks the actual source hash even for refusals,
validates ranges, and uses text-only rendering. Timings report cold/warm worker
startup, compilation, and request round trip in milliseconds. They exclude
artifact hashing, engine validation and execution, and are observations rather
than performance gates or incremental-compilation claims.

Host imports, user-controlled JS, external imports and persistent storage
are unavailable. Compiler/engine resource limits are not a formal memory quota.
Do not serve this development directory on an authenticated application origin.

Tests:

```sh
OAK_REQUIRE_WASM_TESTS=1 go test ./compiler -run '^TestWasm' -count=1
OAK_REQUIRE_WASM_TESTS=1 OAK_WASM_TEST_ENGINE=deno go test ./compiler ./wasm/check -run '^TestWasm' -count=1
go test -race ./internal/wasmtest -count=1
go test ./playground -count=1
node --test playground/compiler-session_test.mjs
deno run --allow-read --allow-write=/tmp --allow-net=127.0.0.1 --allow-run playground/browser_test.ts /path/to/chrome
```

The engine tests need a working Node or Deno. The browser smoke test needs the
built assets and Chrome/Chromium; it uses a disposable profile and loopback
server to test execution, compile-only, cold/warm reuse, UTF-16 diagnostic
navigation, corrupt reports, stale asynchronous hashing, infinite-loop
cancellation and invalid-source cleanup. Session unit tests use fake workers
and clocks to exercise stale IDs, cancellation, timeouts and recycling without
timing races; they also run with `deno test --allow-read` in place of Node.
CI requires engine execution, session unit tests and browser builds; smoke CI is
still planned. The initial Go compiler module is approximately 39 MiB
uncompressed on the development build: deployment size is not optimized yet.

`OAK_WASM_TEST_ENGINE=node|deno` explicitly selects the executable on `PATH`.
It skips only the redundant `--version` discovery probe, not any Wasm test or
result check. Invalid/missing explicit engines fail even in optional mode;
semantic test failures never cause fallback to another engine. Without this
setting, the shared test helper tries Node then Deno with three-second probes,
retaining bounded process diagnostics on failure. CI explicitly selects its
installed Node. The scalar and byte-validator execution deadlines remain 20
and 30 seconds; output-pipe cleanup has a separate one-second bound. This
selection concerns test infrastructure, not Oak target selection or proof status.

The session increment's nine JavaScript tests and Go diagnostic/isolation tests
pass. Its expanded Chrome smoke test still needs a post-fix rerun: the first
attempt stalled at startup, and local sandbox policy blocked rerunning after
the timer-receiver fix. No cold/warm speedup is claimed without that measurement.

See the [design and roadmap](../docs/notes/wasm-wasi-browser-2026-09.md) and
[target maturity matrix](../docs/targets.md).
