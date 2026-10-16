#!/usr/bin/env bash
# Provision the archive already pinned by all three reader/APDU contracts.
# Do not invoke elan: its cold install checks an unrelated latest release.
set -euo pipefail

test "$(uname -s)" = Linux
test "$(uname -m)" = x86_64
test "$(cat spec/lean/lean-toolchain)" = leanprover/lean4:v4.33.1

install_dir="${RUNNER_TEMP:?RUNNER_TEMP must name the runner temporary directory}/reader-apdu-lean"
mkdir -m 700 -- "$install_dir"
archive="$install_dir/lean-4.33.1-linux.tar.zst"
curl --fail --location --silent --show-error \
  --proto '=https' --proto-redir '=https' --connect-timeout 15 --max-time 180 \
  https://releases.lean-lang.org/lean4/v4.33.1/lean-4.33.1-linux.tar.zst \
  --output "$archive"
printf '%s  %s\n' 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235 "$archive" |
  sha256sum --check --strict >&2
timeout --signal=TERM --kill-after=5s 60s \
  tar --zstd --extract --file "$archive" --directory "$install_dir" --no-same-owner
rm -- "$archive"
lean="$install_dir/lean-4.33.1-linux/bin/lean"
test -f "$lean"
test -x "$lean"
printf '%s\n' "$lean"
