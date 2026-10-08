#!/usr/bin/env python3
"""Fail closed on unexpected axioms in both narrow and full-dispatch claims."""
import argparse
import json
import re
import subprocess
import tempfile
from pathlib import Path

NARROW = [
    "OakSailComposition.accepted_typed_projection",
    "OakSailComposition.complete_framed_decoding",
    "OakSailBridge.BitwiseDecoded.and_return",
    "OakSailBridge.BitwiseDecoded.or_return",
    "OakSailBridge.BitwiseDecoded.xor_return",
    "OakSailBridge.BitwiseDecoded.framed_decode",
]
FULL_DISPATCH = [
    "OakSailFullDispatch.accepted_source_full_projection",
    "OakSailBridge.BitwiseDecoded.generated_rtype_dispatch",
    "OakSailBridge.BitwiseDecoded.generated_jalr_dispatch",
]


FRAMED = [
    "OakSailFramedComposition.accepted_typed_frame",
    "OakSailFramedComposition.frame_instructions_run",
    "OakSailBridge.BitwiseDecoded.vmem_stack_load8_run",
    "OakSailBridge.BitwiseDecoded.vmem_stack_store8_run",
]
STANDARD_ONLY = [
    "OakSailBridge.BitwiseDecoded.writeBytes8_readBytes8",
    "OakSailBridge.BitwiseDecoded.lookup_store64_other",
    "OakSailBridge.BitwiseDecoded.pmp_load_run",
    "OakSailBridge.BitwiseDecoded.pmp_store_run",
    "OakSailBridge.BitwiseDecoded.stagedFrameState_eq_finalFrameState",
    "OakSailFramedComposition.saved_slots_bounds",
]
FULL_DISPATCH += [
    "OakSailFramedFullDispatch.accepted_typed_full_frame",
    "OakSailFramedFullDispatch.generated_frame_agreement",
]

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lakefile", default="lakefile.toml")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    allow = json.loads((root / "axiom-allowlist.json").read_text())
    narrow = set(allow["standard"] + allow["configuration"])
    full = narrow | set(allow["full_dispatch_extras"])
    framed = narrow | set(allow["framed_extras"])
    standard = set(allow["standard"])
    names = NARROW + FRAMED + STANDARD_ONLY + FULL_DISPATCH
    source = "import OakSailFullDispatch\nimport OakSailBridge.BitwiseDispatchAgreement\nimport OakSailFramedFullDispatch\n"
    source += "\n".join("#print axioms " + name for name in names) + "\n"
    with tempfile.TemporaryDirectory(prefix="oak-sail-axioms-") as tmp:
        path = Path(tmp) / "Audit.lean"
        path.write_text(source)
        result = subprocess.run(["lake", "-f", args.lakefile, "env", "lean", str(path)],
                                cwd=root, text=True, capture_output=True, check=False)
    if result.returncode:
        raise RuntimeError("Lean audit failed:\n" + result.stdout + result.stderr)
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", result.stdout, re.S)
    actual = {name: {item.strip() for item in body.split(",") if item.strip()}
              for name, body in matches}
    for name in names:
        if name not in actual:
            raise RuntimeError(f"Missing axiom audit result for {name}: {result.stdout}")
        expected = standard if name in STANDARD_ONLY else framed if name in FRAMED else narrow if name in NARROW else full
        unexpected = actual[name] - expected
        if unexpected:
            raise RuntimeError(f"Unexpected axioms in {name}: {sorted(unexpected)}")
        print(f"{name}: {len(actual[name])} checked dependencies")
    print("No native-evaluation, sorryAx, or unlisted dependencies admitted.")
    print("Narrow claims retain the declared Boolean platform parameter.")
    print("Framed claims additionally retain the declared terminal/reservation parameters.")
    print("Full-dispatch agreement retains the separately enumerated opaque primitive parameters.")


if __name__ == "__main__":
    main()
