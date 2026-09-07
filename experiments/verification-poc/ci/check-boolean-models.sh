#!/usr/bin/env bash
# The acceptance claim is about the decoded model; source export remains unproved.
set -euo pipefail
experiment_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$experiment_root"
mkdir -p build/boolean-models
attempt=$(mktemp -d "$experiment_root/build/boolean-models/attempt-XXXXXX")
jq -n '{format:"oak-boolean-model-gate-1",passed:false}' > build/boolean-models/report.json
export LEAN_PATH="$attempt"
for module in RUPSoundness RUPExecutable RUPText BooleanCNF NumberedCNF BooleanSafety BooleanModel; do
  lean -DwarningAsError=true -o "$attempt/$module.olean" "proof/$module.lean" > "$attempt/$module.log" 2>&1 || { cat "$attempt/$module.log"; exit 1; }
done
check() {
  local expected=$1 bundle=$2 base=$3 step=$4 output=$5 status
  set +e
  lean -DwarningAsError=true --run proof/BooleanModel.lean check "$bundle" "$base" "$step" > "$output" 2> "$output.stderr"
  status=$?
  set -e
  cat "$output"
  if [[ "$expected" == true ]]; then test "$status" -eq 0; else test "$status" -eq 1; fi
  jq -e --argjson expected "$expected" '.format == "oak-boolean-safety-1" and .scope == "decoded-boolean-model" and .stage == "check" and .accepted == $expected' "$output" >/dev/null
}
for name in publication publication-relaxed; do
  go run . export-boolean --out "$attempt/$name.json" "examples/native/$name.json"
  for role in initial base step; do
    cnf="$attempt/$name-$role.cnf"
    proof="$attempt/$name-$role.lrat"
    lean -DwarningAsError=true --run proof/BooleanModel.lean emit "$attempt/$name.json" "$role" "$cnf"
    set +e
    cadical --lrat --no-binary "$cnf" "$proof" > "$attempt/$name-$role-solver.log" 2>&1
    status=$?
    set -e
    expected=20
    if [[ "$role" == initial || ( "$name" == publication-relaxed && "$role" == step ) ]]; then expected=10; fi
    if [[ "$status" -ne "$expected" ]]; then cat "$attempt/$name-$role-solver.log"; exit 1; fi
  done
done
safe="$attempt/publication"
broken="$attempt/publication-relaxed"
check true "$safe.json" "$safe-base.lrat" "$safe-step.lrat" "$attempt/safe.json"
check false "$broken.json" "$broken-base.lrat" "$broken-step.lrat" "$attempt/unsafe.json"
check false "$broken.json" "$safe-base.lrat" "$safe-step.lrat" "$attempt/wrong-model.json"
for role in base step; do
  cat "$safe-$role.lrat" > "$attempt/invalid-$role.lrat"
  printf '\n2147483647 0 0\n' >> "$attempt/invalid-$role.lrat"
  base="$safe-base.lrat"; step="$safe-step.lrat"
  if [[ "$role" == base ]]; then base="$attempt/invalid-base.lrat"; else step="$attempt/invalid-step.lrat"; fi
  check false "$safe.json" "$base" "$step" "$attempt/invalid-$role.json"
done
# Malformed models must fail before any checking result. Preserve diagnostics.
jq '.step[0] = {op:"!",value:false,index:0,left:0,right:0}' "$safe.json" > "$attempt/forward.json"
if lean -DwarningAsError=true --run proof/BooleanModel.lean emit "$attempt/forward.json" step "$attempt/forward.cnf" > "$attempt/forward.log" 2>&1; then exit 1; fi
grep -q 'non-backward child reference' "$attempt/forward.log"
sha256sum "$attempt/"*.cnf "$attempt/"*.lrat "$safe.json" "$broken.json" > "$attempt/sha256sums.txt"
jq -n --arg attempt "$attempt" '{format:"oak-boolean-model-gate-1",passed:true,attempt:$attempt,safe_models:1,unsafe_models_rejected:1,wrong_models_rejected:1,invalid_suffixes_rejected:2,malformed_models_rejected:1}' > build/boolean-models/report.json
printf 'Boolean model gate: 1 safe model accepted, 1 unsafe model, 1 wrong model, 2 corruptions and 1 malformed model rejected\n'
