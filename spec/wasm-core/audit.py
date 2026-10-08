#!/usr/bin/env python3
"""Fail closed on unexpected axioms in the hand-transcribed Core proof graph."""
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
source = (ROOT / "Audit.lean").read_text()
names = re.findall(r"^#print axioms (\S+)$", source, re.M)
if not names or len(names) != len(set(names)):
    raise RuntimeError("Empty or duplicate Core axiom query list")
result = subprocess.run(["lake", "env", "lean", str(ROOT / "Audit.lean")],
                        cwd=ROOT.parent / "lean", capture_output=True, text=True, check=True)
rows = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", result.stdout, re.S)
actual = {name: {x.strip() for x in axioms.split(",") if x.strip()} for name, axioms in rows}
if len(rows) != len(actual) or set(actual) != set(names):
    raise RuntimeError("Missing, extra, or duplicate Core axiom report: " + result.stdout)
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in actual.items():
    if axioms - allowed:
        raise RuntimeError(f"Unexpected axioms in {name}: {sorted(axioms - allowed)}")
    print(f"{name}: {sorted(axioms)}")
print(f"PASS: {len(names)} restricted Core theorem closures; no native/sorry/custom axioms.")
