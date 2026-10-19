#!/usr/bin/env python3
"""Fail closed on the actual ELF entry prefix and source-to-clocked callback theorem closures."""
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
    "OakSailEntryChecks.initial_profiles": STANDARD,
    "OakSailEntryChecks.initialized_entry_clocked_prefix": STEPPED,
    "OakSailEntryChecks.initial_ra_unchanged": STANDARD,
    "OakSailEntryChecks.returned_control": STANDARD,
    "OakSailEntryChecks.fifth_tick_at_deadline": PROFILE,
    "OakSailEntryInstructions.decode_start_auipc": PROFILE,
    "OakSailEntryInstructions.decode_start_call": PROFILE,
    "OakSailEntryInstructions.write_x1": STANDARD,
    "OakSailEntryInstructions.execute_start_auipc_run": STANDARD,
    "OakSailEntryInstructions.execute_start_call_run": PROFILE,
    "OakSailEntryInstructions.x1_memoryConfig": STANDARD,
    "OakSailEntryInstructions.x1_config": STANDARD,
    "OakSailEntryInstructions.x1_stepProfile": STANDARD,
    "OakSailEntryInstructions.x1_clockProfile": STANDARD,
    "OakSailEntryInstructions.word_step": STEPPED,
    "OakSailEntryInstructions.clear_aligned": STANDARD,
    "OakSailEntryInstructions.control_x1": STANDARD,
    "OakSailEntryInstructions.entry_add_toNat": STANDARD,
    "OakSailEntryInstructions.entry_add_aligned": STANDARD,
    "OakSailEntryInstructions.entry_bytes": STANDARD,
    "OakSailEntryInstructions.called_register_other": STANDARD,
    "OakSailEntryInstructions.called_control": STANDARD,
    "OakSailEntryInstructions.called_nonregister_state": STANDARD,
    "OakSailEntryInstructions.startup_steps": STEPPED,
    "OakSailEntryInstructions.startup_callbacks": STEPPED,
    "OakSailEntryInstructions.startup_then": STEPPED,
    "OakSailEntrySource.acceptsEntry_iff": STANDARD,
    "OakSailEntrySource.accepted_load": STANDARD,
    "OakSailEntrySource.accepted_entry_code": STANDARD,
    "OakSailEntrySource.accepted_entry_permissions": STANDARD,
    "OakSailEntrySource.accepted_typed_entry_clocked_prefix": STEPPED,
}

def main():
    version = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             text=True, capture_output=True, check=True).stdout
    if not version.startswith("Lean (version 4.29.0,"):
        raise RuntimeError("Expected same-kernel Lean 4.29.0: " + version)
    source = "import OakSailEntryChecks\nnoncomputable section\nexample : Unit → Bool := valid_reservation\n"
    source += "#check valid_reservation\n"
    source += "\n".join("#print axioms " + name for name in CLAIMS) + "\n"
    with tempfile.TemporaryDirectory(prefix="oak-entry-audit-") as tmp:
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
    for name in ("OakSailEntrySource.accepted_typed_entry_clocked_prefix",
                 "OakSailEntryChecks.initialized_entry_clocked_prefix"):
        if actual[name] != baseline:
            raise RuntimeError(f"Entry theorem changed clocked trust closure: {name}")
    print("Entry admission, placement, preservation and initialization use only standard Lean axioms.")
    print(f"Both entry execution theorems retain exactly the existing {len(baseline)}-name clocked closure.")
    print("No native-evaluation, sorry, or unlisted dependencies admitted.")

if __name__ == "__main__":
    main()
