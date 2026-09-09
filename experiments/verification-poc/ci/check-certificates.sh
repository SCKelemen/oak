#!/usr/bin/env bash
# Independent, opt-in rechecking of actual suite certificates with Lean.
set -euo pipefail
experiment_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$experiment_root"
report=${1:-build/integration/report.json}
mkdir -p build/lean-gate
attempt=$(mktemp -d "$experiment_root/build/lean-gate/attempt-XXXXXX")
# Replace any prior success before validation so failed retries cannot leave a
# stale green report behind.
jq -n --arg attempt "$attempt" \
  '{format:"oak-lean-certificate-gate-1",passed:false,attempt:$attempt}' > build/lean-gate/report.json
jq -e '.passed == true and (.models | length > 0)' "$report" >/dev/null
export LEAN_PATH="$attempt"
lean -DwarningAsError=true -o "$attempt/RUPSoundness.olean" proof/RUPSoundness.lean > "$attempt/soundness.log" 2>&1
lean -DwarningAsError=true -o "$attempt/RUPExecutable.olean" proof/RUPExecutable.lean > "$attempt/executable.log" 2>&1
lean -DwarningAsError=true -o "$attempt/RUPText.olean" proof/RUPText.lean > "$attempt/text.log" 2>&1
check() {
  local expected=$1 cnf=$2 proof=$3 output=$4 status
  set +e
  lean -DwarningAsError=true --run proof/RUPCheck.lean "$cnf" "$proof" > "$output" 2> "$output.stderr"
  status=$?
  set -e
  cat "$output"
  # A crash, compiler error, timeout, or missing executable is not a successful
  # negative test. Require the checker's structured rejection and exact status.
  if [[ "$expected" == true ]]; then test "$status" -eq 0; else test "$status" -eq 1; fi
  jq -e --argjson expected "$expected" \
    '.format == "oak-lean-text-check-1" and .accepted == $expected and (.stage == "parse" or .stage == "check")' "$output" >/dev/null
}
count=0
while IFS=$'\t' read -r cnf proof; do
  count=$((count + 1))
  check true "$cnf" "$proof" "$attempt/$count-accepted.json"
  if [[ "$count" -eq 1 ]]; then
    OAK_SELF_HOSTED_TEXT_CNF="$cnf" OAK_SELF_HOSTED_TEXT_PROOF="$proof" \
      OAK_SELF_HOSTED_TEXT_CORPUS_OUT="$attempt/oak-text-certificate.json" \
      go test -count=1 -v . -run '^TestSelfHostedTextCertificate$' 2>&1 | tee "$attempt/oak-text-certificate.log"
    lean -DwarningAsError=true --run proof/RUPTextCompare.lean "$attempt/oak-text-certificate.json" | tee "$attempt/oak-text-certificate-lean.log"
  fi
  # The suite requires SAT for each project's initial query.
  initial="$(dirname "$cnf")/initial.cnf"
  check false "$initial" "$proof" "$attempt/$count-wrong-formula.json"
  cat "$proof" > "$attempt/$count-invalid-suffix.lrat"
  printf '\n2147483647 0 0\n' >> "$attempt/$count-invalid-suffix.lrat"
  check false "$cnf" "$attempt/$count-invalid-suffix.lrat" "$attempt/$count-invalid-suffix.json"
  jq -e '.stage == "check"' "$attempt/$count-invalid-suffix.json" >/dev/null
  jq -n --arg cnf "$cnf" --arg proof "$proof" \
    --arg cnf_sha256 "$(sha256sum "$cnf" | cut -d' ' -f1)" \
    --arg proof_sha256 "$(sha256sum "$proof" | cut -d' ' -f1)" \
    '{cnf:$cnf,proof:$proof,cnf_sha256:$cnf_sha256,proof_sha256:$proof_sha256,accepted:true,wrong_formula_rejected:true,invalid_suffix_rejected:true}' \
    > "$attempt/$count-record.json"
done < <(jq -r '.models[].cadical.logs[] | select(.exit_code == 20 and .command[0] == "cadical") | [.command[-2], .command[-1]] | @tsv' "$report")
expected=$(jq '[.models[].cadical | if .expected_safety then 2 else 1 end] | add' "$report")
test "$count" -gt 0
test "$count" -eq "$expected"
# Replay every real certificate that fits the fixed Oak profile. Exclusions are
# retained explicitly; malformed text and in-profile disagreement fail the gate.
for module in BoundedDecimal ScannerState PackedBuffers RangeBridge LiveTable PropagationState ClauseClassifier PropagationChain CertifiedStream InitialDecoder ProofPacking SegmentPublication CommandAssembly CertificateFile PackedText; do
  lean -DwarningAsError=true -o "$attempt/$module.olean" "proof/$module.lean" 2>&1 | tee "$attempt/$module.log"
done
# The proved file model must also accept the replayed Oak text certificate.
lean -DwarningAsError=true --run proof/CertificateFileCompare.lean "$attempt/oak-text-certificate.json" | tee "$attempt/oak-text-certificate-file-model.log"
jq '[.models[].cadical.logs[] | select(.exit_code == 20 and .command[0] == "cadical") | {cnf:.command[-2],proof:.command[-1]}]' \
  "$report" > "$attempt/certified-manifest.json"
lean -DwarningAsError=true --run proof/CertificateReplay.lean "$attempt/certified-manifest.json" \
  "$attempt/certified-cases.json" "$attempt/certified-report.json" 2>&1 | tee "$attempt/certified-lean.log"
OAK_CERTIFIED_CERTIFICATE_CASES="$attempt/certified-cases.json" \
  go test -count=1 -v . -run '^TestSelfHostedCertifiedCertificates$' 2>&1 | tee "$attempt/certified-oak-go.log"
jq -s --arg attempt "$attempt" --slurpfile certified "$attempt/certified-report.json" \
  '{format:"oak-lean-certificate-gate-1",passed:true,attempt:$attempt,certificates:length,rejection_checks:(length*2),results:.,certified_replay:($certified[0] + {native_agreement:true})}' \
  "$attempt/"*-record.json > build/lean-gate/report.json
printf 'Lean certificate gate: %d accepted certificates, %d rejected corruptions\n' "$count" "$((count * 2))"
