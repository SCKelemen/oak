#!/usr/bin/env python3
"""Fail-closed standard-only audit of every public Return* theorem closure."""
import re
import subprocess
import tempfile
from pathlib import Path

root = Path(__file__).resolve().parent / 'lean'
names, modules = [], []
for path in sorted(root.glob('Return*.lean')):
    source = path.read_text()
    theorems = re.findall(r'^theorem\s+(\w+)', source, re.M)
    if not theorems:
        continue
    namespaces = re.findall(r'^namespace\s+(\S+)', source, re.M)
    if len(namespaces) != 1:
        raise RuntimeError('Expected one explicit theorem namespace: ' + str(path))
    modules.append(path.stem)
    names.extend(namespaces[0] + '.' + name for name in theorems)
if not names or len(names) != len(set(names)):
    raise RuntimeError('Empty or duplicate guarded-return theorem list')
with tempfile.TemporaryDirectory(prefix='oak-return-audit-') as tmp:
    path = Path(tmp) / 'Audit.lean'
    path.write_text('\n'.join('import ' + module for module in modules) + '\n' +
                    '\n'.join('#print axioms ' + name for name in names) + '\n')
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=root,
                            text=True, capture_output=True, check=True)
rows = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", result.stdout, re.S)
actual = {name: {axiom.strip() for axiom in axioms.split(',') if axiom.strip()} for name, axioms in rows}
if len(rows) != len(actual) or set(actual) != set(names):
    raise RuntimeError('Missing/extra/duplicate return audit result: ' + result.stdout)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, axioms in actual.items():
    if axioms - allowed:
        raise RuntimeError(f'Unexpected axioms in {name}: {sorted(axioms - allowed)}')
    print(f'{name}: {sorted(axioms)}')
print(f'PASS: {len(names)} public guarded-return/scalar-extension theorem closures; standard logical axioms only.')
