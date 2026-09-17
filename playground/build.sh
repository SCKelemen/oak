#!/bin/sh
set -eu
playground_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$playground_root"
CGO_ENABLED=0 GOOS=js GOARCH=wasm go build -trimpath -o playground/web/oakc.wasm ./cmd/oak-browser
playground_goroot=$(go env GOROOT)
install -m 0644 "$playground_goroot/lib/wasm/wasm_exec.js" playground/web/wasm_exec.js
