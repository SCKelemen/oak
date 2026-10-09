#!/usr/bin/env python3
"""Fail closed on the actual post-return readiness prefix and source-to-clocked callback theorem closures."""
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = json.loads((ROOT.parent / "lean-sail433/axiom-allowlist.json").read_text())
STANDARD = set(BASE["standard"])
PROFILE = STANDARD | set(BASE["configuration"])
# The sole additional declaration comes from try_step's unselected waiting
# branch. Its exact type is checked below; no value is assumed.
STEPPED = PROFILE | set(BASE["full_dispatch_extras"]) | {"valid_reservation"}
CLAIMS = {
    "OakSailClockedSource.accepted_typed_clocked_prefix": STEPPED,
    "OakSailBoundedAppend.callback_done": STEPPED,
    "OakSailBoundedAppend.bounded_stopped": STEPPED,
    "OakSailBoundedAppend.bounded_append": STEPPED,
    "OakSailExitChecks.initialized_exit_ready": STEPPED,
    "OakSailExitChecks.initial_a7_unchanged": STANDARD,
    "OakSailExitChecks.ready_memory": STANDARD,
    "OakSailExitChecks.ready_register_other": STANDARD,
    "OakSailExitChecks.ready_nonregister_state": STANDARD,
    "OakSailExitChecks.high_bit_result_representation": STANDARD,
    "OakSailExitChecks.sixth_tick_at_deadline": PROFILE,
    "OakSailExitInstructions.decode_exit_addi": PROFILE,
    "OakSailExitInstructions.decode_exit_ecall": PROFILE,
    "OakSailExitInstructions.execute_exit_addi_run": STANDARD,
    "OakSailExitInstructions.x17_memoryConfig": STANDARD,
    "OakSailExitInstructions.x17_config": STANDARD,
    "OakSailExitInstructions.x17_stepProfile": STANDARD,
    "OakSailExitInstructions.x17_clockProfile": STANDARD,
    "OakSailExitInstructions.control_x17": STANDARD,
    "OakSailExitInstructions.exit_addi_step": STEPPED,
    "OakSailExitSource.acceptsExit_iff": STANDARD,
    "OakSailExitSource.accepted_load": STANDARD,
    "OakSailExitSource.returned_profiles": STANDARD,
    "OakSailExitSource.returned_segment_preserved": STANDARD,
    "OakSailExitSource.returned_exit_bytes": STANDARD,
    "OakSailExitSource.suffix_permissions": STANDARD,
    "OakSailExitSource.exit_word_bytes": STANDARD,
    "OakSailExitSource.accepted_typed_exit_ready": STEPPED,
}

def main():
    version = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             text=True, capture_output=True, check=True).stdout
    if not version.startswith("Lean (version 4.29.0,"):
        raise RuntimeError("Expected same-kernel Lean 4.29.0: " + version)
    source = "import OakSailExitChecks\nnoncomputable section\nexample : Unit → Bool := valid_reservation\n"
    source += "#check valid_reservation\n"
    source += "\n".join("#print axioms " + name for name in CLAIMS) + "\n"
    with tempfile.TemporaryDirectory(prefix="oak-exit-audit-") as tmp:
        path = Path(tmp) / "Audit.lean"
        path.write_text(source)
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                text=True, capture_output=True, check=False)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", result.stdout, re.S)
    actual = {name: {x.strip() for x in body.split(",") if x.strip()} for name, body in matches}
    actual.update({name: set() for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout)})
    for name, allowed in CLAIMS.items():
        if name not in actual:
            raise RuntimeError("Missing audited theorem: " + name)
        unexpected = actual[name] - allowed
        if unexpected:
            raise RuntimeError(f"Unexpected dependencies in {name}: {sorted(unexpected)}")
        print(f"{name}: {len(actual[name])} checked dependencies")
    baseline = actual["OakSailClockedSource.accepted_typed_clocked_prefix"]
    for name in ("OakSailExitSource.accepted_typed_exit_ready",
                 "OakSailExitChecks.initialized_exit_ready"):
        if actual[name] != baseline:
            raise RuntimeError(f"Exit readiness theorem changed clocked trust closure: {name}")
    print("Exit admission, placement and initial-state register-preservation checks use only standard Lean axioms.")
    print(f"Both exit readiness theorems retain exactly the existing {len(baseline)}-name clocked closure.")
    print("No native-evaluation, sorry, or unlisted dependencies admitted.")

if __name__ == "__main__":
    main()
