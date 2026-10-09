#!/usr/bin/env python3
"""Fail closed on unexpected axioms in Core, numeric binding, and controls."""
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
all_names = set()
for filename in ("Audit.lean", "NumericControls.lean"):
    path = ROOT / filename
    source = path.read_text()
    names = re.findall(r"^#print axioms (\S+)$", source, re.M)
    if not names or len(names) != len(set(names)) or all_names.intersection(names):
        raise RuntimeError(f"Empty or duplicate axiom query list: {filename}")
    result = subprocess.run(["lake", "env", "lean", str(path)],
                            cwd=ROOT.parent / "lean", capture_output=True, text=True, check=True)
    rows = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
                      result.stdout, re.S)
    actual = {name: {x.strip() for x in axioms.split(",") if x.strip()} for name, axioms in rows}
    if len(rows) != len(actual) or set(actual) != set(names):
        raise RuntimeError(f"Missing, extra, or duplicate axiom report in {filename}: " + result.stdout)
    for name, axioms in actual.items():
        if axioms - ALLOWED:
            raise RuntimeError(f"Unexpected axioms in {name}: {sorted(axioms - ALLOWED)}")
        print(f"{name}: {sorted(axioms)}")
    all_names.update(names)
print(f"PASS: {len(all_names)} Core/numeric/control theorem closures; no native/sorry/custom axioms.")
