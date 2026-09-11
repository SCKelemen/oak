#!/bin/sh
# Set up the Sail-to-Lean bridge (docs/spec/94-assembler.md §8, stage 3).
#
# The bridge package `spec/sail/lean` needs the Sail Lean support library,
# rems-project/lean-sail, checked out at `external/lean-sail` beside the `oak`
# checkout at the pinned revision, with two register-reference helpers patched for Lean 4.33
# (`lean-sail-4.33.patch`). Regenerating `spec/sail/lean/Out*` additionally
# needs Sail itself (`opam install sail`; see `regen.sh`).
set -eu

here=$(cd "$(dirname "$0")" && pwd)
external=$(cd "$here/../../.." && pwd)/external
rev=79b4d08505af29d88b3918f32d29840fae1fa191 # tag v4, the revision Sail 0.20.2's backend targets

mkdir -p "$external"
if [ ! -d "$external/lean-sail" ]; then
  git clone --quiet https://github.com/rems-project/lean-sail.git "$external/lean-sail"
fi
git -C "$external/lean-sail" checkout --quiet "$rev"
if ! git -C "$external/lean-sail" apply --check "$here/lean-sail-4.33.patch" 2>/dev/null; then
  if git -C "$external/lean-sail" apply --reverse --check "$here/lean-sail-4.33.patch" 2>/dev/null; then
    echo "lean-sail: patch already applied"
  else
    echo "lean-sail: patch does not apply cleanly" >&2
    exit 1
  fi
else
  git -C "$external/lean-sail" apply "$here/lean-sail-4.33.patch"
  echo "lean-sail: patched for Lean 4.33"
fi
echo "lean-sail ready at $external/lean-sail ($rev)"
echo "build the bridge with: cd $here/lean && lake build"
