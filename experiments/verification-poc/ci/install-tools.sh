#!/usr/bin/env bash
# Explicit CI/developer provisioning only; the verifier never runs this script.
set -euo pipefail
experiment_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
task_tools="$experiment_root/build/tools"
mode=${1:-all}
case "$mode" in all|lean) ;; *) echo 'usage: install-tools.sh [all|lean]' >&2; exit 2 ;; esac
lock="$experiment_root/tools.lock.json"
mkdir -p "$task_tools"
fetch() { curl --fail --silent --show-error --location --retry 3 "$1" -o "$2"; }
check_hash() { printf '%s  %s\n' "$1" "$2" | sha256sum --check; }
lean_version=$(jq -r '.lean.version' "$lock")
lean_archive="$task_tools/lean.zip"
if [[ ! -f "$lean_archive" ]]; then fetch "$(jq -r '.lean.archive' "$lock")" "$lean_archive"; fi
check_hash "$(jq -r '.lean.sha256' "$lock")" "$lean_archive"
if [[ ! -x "$task_tools/lean-$lean_version-linux/bin/lean" ]]; then unzip -q -o "$lean_archive" -d "$task_tools"; fi
lean_bin="$task_tools/lean-$lean_version-linux/bin"
paths=("$lean_bin")
if [[ "$mode" == all ]]; then
  z3_version=$(jq -r '.z3.version' "$lock")
  z3_archive="$task_tools/z3.zip"
  if [[ ! -f "$z3_archive" ]]; then fetch "$(jq -r '.z3.archive' "$lock")" "$z3_archive"; fi
  # Upstream's older Z3 asset has no published SHA-256. Record the fetched
  # archive hash and verify the exact executable version in the suite.
  sha256sum "$z3_archive"
  if [[ ! -x "$task_tools/z3-$z3_version-x64-glibc-2.35/bin/z3" ]]; then unzip -q -o "$z3_archive" -d "$task_tools"; fi
  paths+=("$task_tools/z3-$z3_version-x64-glibc-2.35/bin")
  cadical_commit=$(jq -r '.cadical.commit' "$lock")
  if [[ ! -d "$task_tools/cadical-src/.git" ]]; then
    git init -q "$task_tools/cadical-src"
    git -C "$task_tools/cadical-src" remote add origin https://github.com/arminbiere/cadical.git
    git -C "$task_tools/cadical-src" fetch -q --depth 1 origin "$cadical_commit"
    git -C "$task_tools/cadical-src" checkout -q --detach FETCH_HEAD
  fi
  test "$(git -C "$task_tools/cadical-src" rev-parse HEAD)" = "$cadical_commit"
  if [[ ! -x "$task_tools/cadical-src/build/cadical" ]]; then
    (cd "$task_tools/cadical-src" && ./configure && make -j2)
  fi
  paths+=("$task_tools/cadical-src/build")
  # TLC is vendored (tools.lock.json records the upstream asset it was taken
  # from); the copy is still checked against the pinned digest.
  cp "$experiment_root/$(jq -r '.tlc.source' "$lock")" "$task_tools/tla2tools.jar"
  check_hash "$(jq -r '.tlc.sha256' "$lock")" "$task_tools/tla2tools.jar"
  jq -n --arg lean "$(sha256sum "$lean_archive" | cut -d' ' -f1)" \
    --arg z3 "$(sha256sum "$z3_archive" | cut -d' ' -f1)" \
    --arg cadical "$cadical_commit" --arg tlc "$(sha256sum "$task_tools/tla2tools.jar" | cut -d' ' -f1)" \
    '{lean_archive_sha256:$lean,z3_archive_sha256:$z3,cadical_commit:$cadical,tlc_jar_sha256:$tlc}' > "$task_tools/provenance.json"
fi
# GITHUB_PATH is GitHub's output contract, not repurposed process state.
if [[ -n "${GITHUB_PATH:-}" ]]; then printf '%s\n' "${paths[@]}" >> "$GITHUB_PATH"; fi
printf 'export PATH=' > "$task_tools/env.sh"
for path in "${paths[@]}"; do printf '%q:' "$path" >> "$task_tools/env.sh"; done
printf '"$PATH"\n' >> "$task_tools/env.sh"
"$lean_bin/lean" --version
