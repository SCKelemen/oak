#!/usr/bin/env python3
"""Check that the provenance verifier rejects changed and incomplete inputs."""
import argparse
import json
import shutil
import tempfile
from pathlib import Path
from verify_export import verify_export

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--generated", required=True, type=Path)
args = parser.parse_args()
source = args.generated.resolve()
sail = source / ".lake/packages/Sail"
pins = json.loads((Path(__file__).parent / "export-provenance.json").read_text())
with tempfile.TemporaryDirectory(prefix="oak-export-mutants-") as tmp:
    model, support = Path(tmp) / "model", Path(tmp) / "sail"
    for root, dest, files in [(source, model, pins["model_files"]),
                              (sail, support, pins["sail_files"])]:
        for name in files:
            path = dest / name
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(root / name, path)
    verify_export(model, support)

    def rejected(label):
        try:
            verify_export(model, support)
        except RuntimeError:
            return
        raise RuntimeError("Provenance verifier accepted " + label)

    for path in [model / "LeanRV64D/RiscvExtras.lean", support / "Sail.lean",
                 model / "lean-toolchain"]:
        original = path.read_bytes()
        path.write_bytes(original + b"\n-- mutation\n")
        rejected(str(path))
        path.write_bytes(original)
    extra = model / "Unexpected.lean"
    extra.write_text("-- extra source")
    rejected("an extra model source")
    extra.unlink()
    missing = model / "LeanRV64D.lean"
    missing.unlink()
    rejected("a missing model source")
print("PASS: valid export accepted; five source/configuration/inventory mutations rejected")
