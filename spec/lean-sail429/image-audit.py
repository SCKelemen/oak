#!/usr/bin/env python3
"""Fail closed on the explicit image loader and source-to-clocked callback theorem closures."""
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
    "OakSailImageLoad.loaded_segment": STANDARD,
    "OakSailImageLoad.checkedLoad_success": STANDARD,
    "OakSailImageLoad.checkedLoad_reject": STANDARD,
    "OakSailImageSource.accepted_load": STANDARD,
    "OakSailImageLoad.copyBytes_regs": STANDARD,
    "OakSailImageLoad.copyBytes_at": STANDARD,
    "OakSailImageLoad.copyBytes_other": STANDARD,
    "OakSailImageLoad.acceptsImage_iff": STANDARD,
    "OakSailImageLoad.loaded_body": STANDARD,
    "OakSailImageLoad.loaded_memory_other": STANDARD,
    "OakSailImageLoad.loaded_register_other": STANDARD,
    "OakSailImageLoad.loaded_regions": STANDARD,
    "OakSailImageLoad.range_contained": STANDARD,
    "OakSailImageLoad.aligned_paddr": STANDARD,
    "OakSailImageLoad.range_disjoint": STANDARD,
    "OakSailImageLoad.image_region_matches": STANDARD,
    "OakSailImageLoad.stack_region_matches": STANDARD,
    "OakSailImageLoad.frame_code": STANDARD,
    "OakSailImageLoad.executable_frame": STANDARD,
    "OakSailImageLoad.stack_bits": STANDARD,
    "OakSailImageLoad.stack_access": STANDARD,
    "OakSailImageLoad.code_stack_disjoint": STANDARD,
    "OakSailImageLoad.copyBytes_nonregister_state": STANDARD,
    "OakSailImageLoad.loaded_nonregister_state": STANDARD,
    "OakSailImageLoad.loaded_memoryConfig": STANDARD,
    "OakSailImageSource.accepts_iff": STANDARD,
    "OakSailImageSource.loaded_stepProfile": STANDARD,
    "OakSailImageSource.loaded_clockProfile": STANDARD,
    "OakSailImageChecks.invocation_profiles": STANDARD,
    "OakSailImageChecks.loaded_stack_unchanged": STANDARD,
    "OakSailImageChecks.rx_rw_permissions": STANDARD,
    "OakSailClockedSource.accepted_typed_clocked_prefix": STEPPED,
    "OakSailImageSource.accepted_typed_image_clocked_prefix": STEPPED,
    "OakSailImageChecks.initialized_image_clocked_prefix": STEPPED,
}

def main():
    version = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             text=True, capture_output=True, check=True).stdout
    if not version.startswith("Lean (version 4.29.0,"):
        raise RuntimeError("Expected same-kernel Lean 4.29.0: " + version)
    source = "import OakSailImageChecks\nnoncomputable section\nexample : Unit → Bool := valid_reservation\n"
    source += "#check valid_reservation\n"
    source += "\n".join("#print axioms " + name for name in CLAIMS) + "\n"
    with tempfile.TemporaryDirectory(prefix="oak-image-audit-") as tmp:
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
    for name in ("OakSailImageSource.accepted_typed_image_clocked_prefix",
                 "OakSailImageChecks.initialized_image_clocked_prefix"):
        if actual[name] != baseline:
            raise RuntimeError(f"Image theorem changed clocked trust closure: {name}")
    print("Loader, placement, permissions and initialization use only standard Lean axioms.")
    print(f"Both image execution theorems retain exactly the existing {len(baseline)}-name clocked closure.")
    print("No native-evaluation, sorry, or unlisted dependencies admitted.")

if __name__ == "__main__":
    main()
