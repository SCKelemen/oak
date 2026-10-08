#!/usr/bin/env python3
"""Check exact source identity against the reviewed upstream export artifact.

The pinned hashes/provenance are evidence from the recorded GitHub Actions run,
not a theorem that Sail generation preserves ISA semantics. Existing CI retains
its original pinned source checkout/generation and required 4.29 checks. No
artifact-service lifetime or mutable download URL is needed by this check.
"""
import hashlib
import json
from pathlib import Path


def verify_export(generated: Path, sail: Path) -> dict:
    pins = json.loads((Path(__file__).parent / "export-provenance.json").read_text())
    for root, files, label in [(generated, pins["model_files"], "model"),
                               (sail, pins["sail_files"], "Sail support")]:
        actual = {p.relative_to(root).as_posix() for p in root.rglob("*.lean")
                  if not any(x.startswith(".") for x in p.relative_to(root).parts)}
        if label == "Sail support":
            actual = {p for p in actual if p == "Sail.lean" or p.startswith("Sail/")}
        expected = {p for p in files if p.endswith(".lean")}
        if actual != expected:
            raise RuntimeError(f"{label} source inventory mismatch: missing={sorted(expected-actual)}, extra={sorted(actual-expected)}")
        for name, digest in files.items():
            path = root / name
            if not path.is_file() or path.is_symlink():
                raise RuntimeError(f"Missing/non-regular {label} input: {path}")
            if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                raise RuntimeError(f"Provenance source hash mismatch: {path}")
    print(f"Verified artifact {pins['artifact']['id']} provenance: "
          f"{len(pins['model_files'])} model/config and {len(pins['sail_files'])} support/config hashes")
    return pins
