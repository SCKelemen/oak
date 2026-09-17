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

Source checking and engine validation are shown separately from the missing
formal translation proof. This is **not** a fully verified backend or a
production deployment of try.oak.dev. No domain or hosting is configured.

Compilation and execution have separate workers and deadlines; Stop discards
them. Host imports, user-controlled JS, external imports and persistent storage
are unavailable. Compiler/engine resource limits are not a formal memory quota.
Do not serve this development directory on an authenticated application origin.

Tests:

```sh
OAK_REQUIRE_WASM_TESTS=1 go test ./compiler -run '^TestWasm' -count=1
deno run --allow-read --allow-write=/tmp --allow-net=127.0.0.1 --allow-run playground/browser_test.ts /path/to/chrome
```

The engine tests need a working Node or Deno. The browser smoke test needs the
built assets and Chrome/Chromium; it uses a disposable profile and loopback
server to test execution, infinite-loop cancellation and invalid-source cleanup.
CI requires engine execution and builds the browser assets; browser smoke CI is
still planned. The initial Go compiler module is approximately 39 MiB
uncompressed on the development build: deployment size is not optimized yet.

See the [design and roadmap](../docs/notes/wasm-wasi-browser-2026-09.md) and
[target maturity matrix](../docs/targets.md).
