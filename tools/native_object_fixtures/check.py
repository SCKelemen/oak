#!/usr/bin/env python3
"""Kernel-check native ELF model/fixtures in bounded processes and audit axioms.
This CI evidence gate is not a production artifact-authority API.
"""
from pathlib import Path
import re
import json
import subprocess
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from threading import Lock

PRINT_LOCK = Lock()

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / 'spec' / 'lean'
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}


def inventory(lines):
    namespaces, names = [], {}
    for index, line in enumerate(lines):
        if match := re.match(r'^namespace ([\w.]+)$', line):
            namespaces.append(match[1])
        elif re.match(r'^end(?: [\w.]+)?$', line):
            namespaces.pop()
        elif match := re.match(r'^(?:@\[[^\n]*\] )?theorem (\w+)', line):
            names[index] = '.'.join(namespaces + [match[1]])
    if len(names) != len(set(names.values())):
        raise SystemExit('Duplicate theorem names in source inventory')
    return names


def require_inventory(kind, actual):
    pinned = json.loads((ROOT / 'tools/native_object_fixtures/expected-theorems.json').read_text())
    expected = pinned[kind]
    if len(expected) != len(set(expected)) or list(actual) != expected:
        raise SystemExit('Changed, missing, or duplicate pinned ' + kind + ' theorem inventory')
    return expected


def run(args):
    result = subprocess.run(args, cwd=LEAN, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=240)
    with PRINT_LOCK:
        print(result.stdout, end='', flush=True)
    if result.returncode:
        raise SystemExit(f'Command failed ({result.returncode}): {args}')
    return result.stdout


def check_proof(source, expected):
    source += '\nset_option format.width 100000\n' + '\n'.join('#print axioms ' + name for name in expected) + '\n'
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', prefix='NativeObjectCheck',
                                     dir=LEAN, delete=False) as handle:
        handle.write(source)
        path = Path(handle.name)
    try:
        output = run(['lake', 'env', 'lean', '-j1', str(path)])
    finally:
        path.unlink(missing_ok=True)
    audit_reports(output, expected)


def audit_reports(output, expected):
    # Lean may wrap a bracketed axiom list across lines. Accept only that
    # whitespace variation; every other byte must belong to an exact report.
    pattern = re.compile(r"'([^'\n]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
    actual, end = {}, 0
    for match in pattern.finditer(output):
        if output[end:match.start()].strip():
            raise SystemExit('Unexpected axiom-audit output before report')
        end = match.end()
        name, axioms = match.groups()
        if name in actual:
            raise SystemExit('Duplicate axiom report: ' + name)
        actual[name] = {a.strip() for a in axioms.split(',')} if axioms else set()
        if actual[name] - ALLOWED:
            raise SystemExit('Unapproved proof axioms: ' + name + ': ' + str(actual[name]))
    if output[end:].strip():
        raise SystemExit('Unexpected axiom-audit output after report')
    if set(actual) != set(expected):
        raise SystemExit('Missing or extra theorem axiom reports')


def main():
    model = inventory((LEAN / 'Oak' / 'NativeBitwiseObject.lean').read_text().splitlines())
    lines = (LEAN / 'NativeBitwiseObjectFixtures.lean').read_text().splitlines()
    fixtures = inventory(lines)
    require_inventory('model', model.values())
    require_inventory('fixtures', fixtures.values())
    run(['lake', 'build', 'Oak.NativeBitwiseObject'])
    check_proof('import Oak.NativeBitwiseObject\n', list(model.values()))
    # Every retained fixture theorem is a complete one-line kernel-decide fact.
    # Fail closed if a renderer change would defeat declaration-based sharding.
    for index in fixtures:
        if not lines[index].endswith(' := by decide +kernel'):
            raise SystemExit('Unsupported multiline/non-kernel fixture declaration')
    positive = [i for i, name in fixtures.items() if name.endswith('.admitted')]
    negative = [i for i in fixtures if i not in positive]
    batches = [positive] + [negative[i:i+16] for i in range(0, len(negative), 16)]
    checked = set()
    def check_batch(number, batch):
        selected = set(batch)
        source = '\n'.join(line for i, line in enumerate(lines) if i not in fixtures or i in selected)
        expected = [fixtures[i] for i in batch]
        with PRINT_LOCK:
            print(f'Checking fixture batch {number}/{len(batches)} ({len(batch)} declarations)', flush=True)
        check_proof(source, expected)
        return number, expected
    # Two workers, each a fresh single-thread Lean process; no repository-wide
    # build or unbounded process fanout. This bounds proof-elaboration memory.
    with ThreadPoolExecutor(max_workers=2) as pool:
        tasks = [pool.submit(check_batch, n, b) for n, b in enumerate(batches, 1)]
        for task in as_completed(tasks):
            number, expected = task.result()
            if checked.intersection(expected):
                raise SystemExit('Duplicate checked fixture')
            checked.update(expected)
            with PRINT_LOCK:
                print(f'Passed fixture batch {number}/{len(batches)}; {len(checked)} facts checked', flush=True)
    if checked != set(fixtures.values()):
        raise SystemExit('Incomplete fixture coverage')
    print(f'Kernel checked {len(positive)} admissions and {len(negative)} refusals; '
          f'{len(model)+len(checked)} exact theorem-closure reports; allowed axioms only.')


if __name__ == '__main__':
    main()
