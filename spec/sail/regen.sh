#!/bin/sh
# Regenerate the Lean that Sail's backend produces from `arm_primitives.sail`
# (docs/spec/94-assembler.md §8, stage 3). Needs Sail (`opam install sail`,
# 0.20.2 or later) and the support library from `setup.sh`.
#
# The generated files are committed (`lean/Out.lean`, `lean/Out/`); this
# script overwrites them, and `asm/sail_lean_test.go` checks that the
# committed copy is what the installed Sail generates.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
external=$(cd "$here/../../.." && pwd)/external
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

# Run inside the temporary directory: sail writes an SMT cache beside its cwd.
(cd "$out" && sail "$here/arm_primitives.sail" --lean --lean-single-file \
  --lean-output-dir "$out" --lean-lib-path "$external/lean-sail")

rm -rf "$here/lean/Out" "$here/lean/Out.lean"
cp "$out/out/Out.lean" "$here/lean/Out.lean"
cp -R "$out/out/Out" "$here/lean/Out"
echo "regenerated $here/lean/Out.lean and $here/lean/Out/"
