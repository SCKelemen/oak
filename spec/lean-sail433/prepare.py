#!/usr/bin/env python3
"""Copy an already-provenance-verified RV64 export into isolated Lean 4.33 projects.

This is not a generator or a provenance attestation. It verifies the input
project's declared pins and exact source-copy equality, and copies no .olean
files. The existing source-artifact bootstrap supplies export provenance.
"""
import argparse
import hashlib
import json
from pathlib import Path

SAIL_REV = "079463134b9c50450b8393e1566a09fc492a34d9"
OLD_TOOLCHAIN = "leanprover/lean4:v4.29.0"
NEW_TOOLCHAIN = "leanprover/lean4:v4.33.1"


def checked_write(path: Path, data: bytes) -> None:
    if path.exists():
        if path.read_bytes() != data:
            raise RuntimeError(f"Refusing to overwrite differing file: {path}")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def copy_library(source: Path, dest: Path, library: str) -> list[dict[str, str]]:
    sources = [source / f"{library}.lean", *sorted((source / library).rglob("*.lean"))]
    if len(sources) < 2:
        raise RuntimeError(f"Missing source library: {source / library}")
    manifest = []
    for path in sources:
        data = path.read_bytes()
        relative = path.relative_to(source)
        target = dest / relative
        checked_write(target, data)
        if target.read_bytes() != data:
            raise RuntimeError(f"Source-copy mismatch: {target}")
        manifest.append({"path": str(relative), "sha256": hashlib.sha256(data).hexdigest()})
    return manifest


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generated", required=True, type=Path,
                        help="already-verified Lean_RV64D export directory")
    parser.add_argument("--sail", type=Path, help="pinned lean-sail source directory")
    parser.add_argument("--external", type=Path,
                        default=Path(__file__).resolve().parents[2] / "external")
    args = parser.parse_args()
    generated = args.generated.resolve()
    sail = (args.sail or generated / ".lake/packages/Sail").resolve()
    if (generated / "lean-toolchain").read_text().strip() != OLD_TOOLCHAIN:
        raise RuntimeError("Expected the pinned Lean 4.29 RV64 input export")
    packages = json.loads((generated / "lake-manifest.json").read_text())["packages"]
    if not any(p.get("name") == "Sail" and p.get("rev") == SAIL_REV for p in packages):
        raise RuntimeError("Generated export does not declare the pinned lean-sail revision")

    model_dest, sail_dest = args.external / "rv64-lean433", args.external / "sail-lean433"
    model_manifest = copy_library(generated, model_dest, "LeanRV64D")
    sail_manifest = copy_library(sail, sail_dest, "Sail")
    old_requirement = 'git = "https://github.com/rems-project/lean-sail"\nrev = "v5"'
    config = (generated / "lakefile.toml").read_text()
    if config.count(old_requirement) != 1:
        raise RuntimeError("Unexpected RV64 Lake dependency configuration")
    checked_write(model_dest / "lakefile.toml",
                  config.replace(old_requirement, 'path = "../sail-lean433"').encode())
    checked_write(sail_dest / "lakefile.toml", (sail / "lakefile.toml").read_bytes())
    for dest in (model_dest, sail_dest):
        checked_write(dest / "lean-toolchain", (NEW_TOOLCHAIN + "\n").encode())
    report = {"scope": "Exact source-copy verification; input export provenance is external",
              "source_toolchain": OLD_TOOLCHAIN, "build_toolchain": NEW_TOOLCHAIN,
              "declared_sail_revision": SAIL_REV,
              "model_sources": model_manifest, "sail_sources": sail_manifest}
    checked_write(model_dest / "source-copy-manifest.json",
                  (json.dumps(report, indent=2, sort_keys=True) + "\n").encode())
    print(f"Verified {len(model_manifest)} model and {len(sail_manifest)} Sail source files")
    print("Only dependency paths/toolchain files changed; no compiled artifacts copied.")


if __name__ == "__main__":
    main()
