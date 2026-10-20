#!/usr/bin/env python3
"""Audit every public theorem of the selected ARM scalar bridge."""
import re
import subprocess
import tempfile
from pathlib import Path

root = Path(__file__).resolve().parent / "lean"
names = ["Oak.SailBridge.Scalar." + name for name in
         re.findall(r"^theorem\s+(\w+)", (root / "ScalarExecutionBridge.lean").read_text(), re.M)]
if not names or len(names) != len(set(names)):
    raise RuntimeError("Empty or duplicate scalar theorem list")
with tempfile.TemporaryDirectory(prefix="oak-scalar-audit-") as tmp:
    path = Path(tmp) / "Audit.lean"
    path.write_text("import ScalarExecutionBridge\n" + "\n".join("#print axioms " + n for n in names) + "\n")
    result = subprocess.run(["lake", "env", "lean", str(path)], cwd=root,
                            text=True, capture_output=True, check=True)
rows = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", result.stdout, re.S)
actual = {n: {x.strip() for x in a.split(",") if x.strip()} for n, a in rows}
if len(rows) != len(actual) or set(actual) != set(names):
    raise RuntimeError("Missing/extra scalar audit result: " + result.stdout)
allowed = {"propext", "Classical.choice", "Quot.sound"}
for n, a in actual.items():
    if a - allowed:
        raise RuntimeError(f"Unexpected axioms in {n}: {sorted(a-allowed)}")
    print(f"{n}: {sorted(a)}")
print(f"PASS: {len(names)} public scalar theorem closures; standard logical axioms only.")
