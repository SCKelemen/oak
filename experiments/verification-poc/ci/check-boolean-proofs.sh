#!/usr/bin/env bash
# CaDiCaL searches; the proved Lean pipeline reconstructs and checks the target.
set -euo pipefail
experiment_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$experiment_root"
mkdir -p build/boolean-proofs
attempt=$(mktemp -d "$experiment_root/build/boolean-proofs/attempt-XXXXXX")
jq -n --arg attempt "$attempt" '{format:"oak-boolean-proofs-1",passed:false,attempt:$attempt}' > build/boolean-proofs/report.json
export LEAN_PATH="$attempt"
for module in RUPSoundness RUPExecutable RUPText BooleanCNF NumberedCNF; do
  lean -DwarningAsError=true -o "$attempt/$module.olean" "proof/$module.lean" > "$attempt/$module.log" 2>&1 || { cat "$attempt/$module.log"; exit 1; }
done
lean -DwarningAsError=true --run proof/BooleanProof.lean list > "$attempt/examples.tsv" 2>&1 || { cat "$attempt/examples.tsv"; exit 1; }
check() {
  local expected=$1 name=$2 proof=$3 output=$4 status
  set +e
  lean -DwarningAsError=true --run proof/BooleanProof.lean check "$name" "$proof" > "$output" 2> "$output.stderr"
  status=$?
  set -e
  cat "$output"
  if [[ "$expected" == true ]]; then test "$status" -eq 0; else test "$status" -eq 1; fi
  jq -e --argjson expected "$expected" '.format == "oak-boolean-proof-1" and .accepted == $expected' "$output" >/dev/null
}
accepted=0
satisfiable=0
while IFS=$'\t' read -r name expected; do
  cnf="$attempt/$name.cnf"
  proof="$attempt/$name.lrat"
  lean -DwarningAsError=true --run proof/BooleanProof.lean emit "$name" "$cnf"
  set +e
  cadical --lrat --no-binary "$cnf" "$proof" > "$attempt/$name-solver.log" 2>&1
  status=$?
  set -e
  test "$status" -eq "$expected"
  if [[ "$expected" -eq 20 ]]; then
    check true "$name" "$proof" "$attempt/$name-accepted.json"
    # Checking rebuilds the source's numbered CNF, so a proof for another
    # expression cannot rely on the formula originally given to the solver.
    check false true "$proof" "$attempt/$name-wrong-source.json"
    cat "$proof" > "$attempt/$name-invalid-suffix.lrat"
    printf '\n2147483647 0 0\n' >> "$attempt/$name-invalid-suffix.lrat"
    check false "$name" "$attempt/$name-invalid-suffix.lrat" "$attempt/$name-invalid-suffix.json"
    jq -e '.stage == "check"' "$attempt/$name-invalid-suffix.json" >/dev/null
    accepted=$((accepted + 1))
  else
    check false "$name" "$proof" "$attempt/$name-satisfiable.json"
    satisfiable=$((satisfiable + 1))
  fi
  jq -n --arg name "$name" --argjson solver_exit "$status" \
    --arg cnf_sha256 "$(sha256sum "$cnf" | cut -d' ' -f1)" \
    --arg proof_sha256 "$(sha256sum "$proof" | cut -d' ' -f1)" \
    '{name:$name,solver_exit:$solver_exit,cnf_sha256:$cnf_sha256,proof_sha256:$proof_sha256}' > "$attempt/$name-record.json"
done < "$attempt/examples.tsv"
test "$accepted" -eq 6
test "$satisfiable" -eq 3
jq -s --arg attempt "$attempt" --argjson accepted "$accepted" --argjson satisfiable "$satisfiable" \
  '{format:"oak-boolean-proofs-1",passed:true,attempt:$attempt,accepted:$accepted,satisfiable_rejected:$satisfiable,corruptions_rejected:($accepted*2),results:.}' \
  "$attempt/"*-record.json > build/boolean-proofs/report.json
printf 'Boolean proof bridge: %d accepted refutations, %d satisfiable cases and %d corruptions rejected\n' "$accepted" "$satisfiable" "$((accepted * 2))"
