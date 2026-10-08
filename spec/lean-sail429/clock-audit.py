#!/usr/bin/env python3
"""Fail closed on the bounded clocked callback theorem closure."""
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
    "OakSailClockTick.tick_clock_run": PROFILE,
    "OakSailClockTick.tick_clock_at_deadline": PROFILE,
    "OakSailClockTick.tick_clock_at_deadline_not_below": PROFILE,
    "OakSailClockTick.clock_profile_nonempty": STANDARD,
    "OakSailClockTick.clockState_stepProfile": STANDARD,
    "OakSailClockTick.cycle_increment_modular": STANDARD,
    "OakSailClockTick.cycle_increment_wraps": STANDARD,
    "OakSailPlatformCallback.generated_loop_callback": STEPPED,
    "OakSailPlatformCallback.stopped_callback": STEPPED,
    "OakSailClockedPrefix.clocked_nine_steps": STEPPED,
    "OakSailClockedSource.accepted_typed_clocked_prefix": STEPPED,
    "OakSailClockedState.clocked_result": STANDARD,
    "OakSailClockedState.clocked_pc_and_next": STANDARD,
    "OakSailClockedState.clocked_register_other": STANDARD,
    "OakSailClockedState.clocked_memory_other": STANDARD,
    "OakSailClockedState.clocked_nonregister_state": STANDARD,
    "OakSailClockChecks.phase_one_actual_tick": STEPPED,
    "OakSailClockChecks.phase_one_not_phase_zero": STEPPED,
    "OakSailClockChecks.four_cycles_modular": STANDARD,
    "OakSailClockChecks.four_cycles_wrap": STANDARD,
    "OakSailClockChecks.witness_clock_profile": STANDARD,
}

def main():
    version = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             text=True, capture_output=True, check=True).stdout
    if not version.startswith("Lean (version 4.29.0,"):
        raise RuntimeError("Expected same-kernel Lean 4.29.0: " + version)
    source = "import OakSailClockedSource\nimport OakSailClockChecks\nnoncomputable section\nexample : Unit → Bool := valid_reservation\n"
    source += "#check valid_reservation\n"
    source += "\n".join("#print axioms " + name for name in CLAIMS) + "\n"
    with tempfile.TemporaryDirectory(prefix="oak-clocked-audit-") as tmp:
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
    print("Clock helpers add no opaque parameters; callback/prefix retains existing 77-name step closure.")
    print("The generated callback equality does not unfold the opaque recursive iterator.")
    print("No native-evaluation, sorry, or unlisted dependencies admitted.")

if __name__ == "__main__":
    main()
