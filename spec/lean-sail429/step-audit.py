#!/usr/bin/env python3
"""Fail closed on the actual nine-step source-to-execution theorem closure."""
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
    "OakSailBridge.BitwiseDecoded.dispatchInterrupt_machine_run": PROFILE,
    "OakSailBridge.BitwiseDecoded.should_inc_minstret_machine_run": STANDARD,
    "OakSailBridge.BitwiseDecoded.is_landing_pad_expected_run": STANDARD,
    "OakSailBridge.BitwiseDecoded.stepProfile_nonempty": STANDARD,
    "OakSailBridge.BitwiseDecoded.stepProfileState_uninhibited": STANDARD,
    "OakSailBridge.BitwiseDecoded.stepProfileState_uninhibited_not_profile": STANDARD,
    "OakSailBridge.BitwiseDecoded.tick_pc_run": STANDARD,
    "OakSailBridge.BitwiseDecoded.run_hart_active_success": STEPPED - {"valid_reservation"},
    "OakSailBridge.BitwiseDecoded.try_step_success": STEPPED,
    "OakSailSteppedBody.frame_body_step": STEPPED - {"valid_reservation"},
    "OakSailSteppedFrame.nine_steps": STEPPED,
    "OakSailSteppedFrame.accepted_typed_steps": STEPPED,
    "OakSailSteppedFrame.stepped_pc_and_next": STANDARD,
    "OakSailSteppedFrame.stepped_register_other": STANDARD,
    "OakSailSteppedFrame.stepped_memory_other": STANDARD,
    "OakSailSteppedFrame.stepped_nonregister_state": STANDARD,
    "OakSailSteppedChecks.nonexecutable_fetch_fault": STANDARD,
    "OakSailSteppedChecks.witness_combined_profile": STANDARD,
    "OakSailSteppedChecks.witness_frame_access": STANDARD,
    "OakSailSteppedChecks.witness_executable": STANDARD,
    "OakSailSteppedChecks.witness_disjoint": STANDARD,
    "OakSailSteppedChecks.changed_body_rejected": STANDARD,
    "OakSailSteppedChecks.changed_source_rejected": STANDARD,
    "OakSailSteppedChecks.changed_ram_byte_rejected": STANDARD,
}

def main():
    version = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             text=True, capture_output=True, check=True).stdout
    if not version.startswith("Lean (version 4.29.0,"):
        raise RuntimeError("Expected same-kernel Lean 4.29.0: " + version)
    source = "import OakSailSteppedChecks\nnoncomputable section\nexample : Unit → Bool := valid_reservation\n"
    source += "#check valid_reservation\n"
    source += "\n".join("#print axioms " + name for name in CLAIMS) + "\n"
    with tempfile.TemporaryDirectory(prefix="oak-stepped-audit-") as tmp:
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
    print("valid_reservation : Unit → Bool; referenced by unselected HART_WAITING path.")
    print("No native-evaluation, sorry, or unlisted dependencies admitted.")

if __name__ == "__main__":
    main()
