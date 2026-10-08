#!/usr/bin/env python3
"""Audit the same-kernel source/body/fetch closure without native evaluation."""
import re
import subprocess
import tempfile
from pathlib import Path

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
FETCH = STANDARD | {"plat_term_write", "sys_enable_experimental_extensions"}
FRAME = FETCH | {"load_reservation", "match_reservation"}
CLAIMS = {
    "OakSailBridge.BitwiseDecoded.mem_fetch4_run": STANDARD,
    "OakSailBridge.BitwiseDecoded.readBytes4_missing_first": STANDARD,
    "OakSailBridge.BitwiseDecoded.fetch_bytes4_run": FETCH,
    "OakSailBridge.BitwiseDecoded.fetch_base_run": FETCH,
    "OakSailFetchedCode.frameCodeAt_finalState": STANDARD,
    "OakSailFetchedCode.codePC_bytes": STANDARD,
    "OakSailFetchedFrame.every_frame_word_fetch": FETCH,
    "OakSailFetchedFrame.every_frame_word_fetch_after_stores": FETCH,
    "OakSailFetchedFrame.accepted_source_word_fetch": FETCH,
    "OakSailFetchedFrame.accepted_typed_word_fetch": FETCH,
    "OakSailFramedComposition.accepted_typed_frame": FRAME,
    "Oak.RiscVFramedBitwise.run_success": STANDARD,
    "Oak.BitwiseSource.parse_sound": STANDARD,
}

def main():
    root = Path(__file__).resolve().parent
    version = subprocess.run(["lake", "env", "lean", "--version"], cwd=root,
                             text=True, capture_output=True, check=True).stdout
    if not version.startswith("Lean (version 4.29.0,"):
        raise RuntimeError("Expected the pinned single-kernel Lean 4.29.0 project: " + version)
    source = "import OakSailFetchedFrame\n" + "\n".join(
        "#print axioms " + name for name in CLAIMS) + "\n"
    with tempfile.TemporaryDirectory(prefix="oak-fetch-audit-") as temp:
        path = Path(temp) / "Audit.lean"
        path.write_text(source)
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=root,
                                text=True, capture_output=True, check=False)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", result.stdout, re.S)
    actual = {name: {x.strip() for x in body.split(",") if x.strip()} for name, body in matches}
    for name, allowed in CLAIMS.items():
        if name not in actual:
            raise RuntimeError("Missing audited theorem: " + name + "\n" + result.stdout)
        unexpected = actual[name] - allowed
        if unexpected:
            raise RuntimeError(f"Unexpected dependencies in {name}: {sorted(unexpected)}")
        print(f"{name}: {sorted(actual[name])}")
    print("Same Lean 4.29 source/body/fetch kernel closure checked; no native or sorry axioms.")

if __name__ == "__main__":
    main()
