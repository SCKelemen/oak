#!/usr/bin/env python3
"""Kernel-check native executable ELF model/fixtures in bounded processes and audit axioms.
This CI evidence gate is not a production artifact-authority API.
"""
from pathlib import Path
import re
import json
import subprocess
import tempfile
import argparse
import hashlib
import time
import resource
from render_lean_fixtures import expand_literal
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
    pinned = json.loads((ROOT / 'tools/native_image_fixtures/expected-theorems.json').read_text())
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
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', prefix='NativeImageCheck',
                                     dir=LEAN, delete=False) as handle:
        handle.write(source)
        path = Path(handle.name)
    try:
        output = run(['lake', 'env', 'lean', '-j1', '-M3000', str(path)])
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


def fixture_source(lines, fixtures, selected):
    """Keep only selected fixture namespaces, preserving all their input bytes."""
    selected = set(selected)
    dependencies = {fixtures[index].removesuffix('.loaded') + '.admitted' for index in selected if fixtures[index].endswith('.loaded')}
    selected.update(index for index, name in fixtures.items() if name in dependencies)
    wanted = {fixtures[index].rsplit('.', 1)[0] for index in selected}
    namespaces, result = [], []
    for index, line in enumerate(lines):
        opening = re.match(r'^namespace ([\w.]+)$', line)
        closing = re.match(r'^end(?: [\w.]+)?$', line)
        if opening:
            namespaces.append(opening[1])
        keep = len(namespaces) < 2 or '.'.join(namespaces) in wanted
        if keep and (index not in fixtures or index in selected):
            result.append(line)
        if closing:
            namespaces.pop()
    return '\n'.join(result)


def verify_inputs(lines):
    """Pin complete literal bytes and requested name/source, not producer metadata."""
    pins = json.loads((ROOT/'tools/native_image_fixtures/evidence.json').read_text())
    current, inputs = None, {}
    for line in lines:
        opening = re.match(r'^namespace (\w+)$', line)
        if opening and opening[1] in pins:
            current = opening[1]
            if current in inputs:
                raise SystemExit('Duplicate fixture namespace')
            inputs[current] = {}
        if current:
            match = re.match(r'^def (source|nameBytes|header|suffix|image|renamedImage) : (?:List UInt8|Bytes) := (.*)$', line)
            if match:
                if match[1] in inputs[current]:
                    raise SystemExit('Duplicate fixture input')
                inputs[current][match[1]] = match[2]
        if line.startswith('end '):
            current = None
    if set(inputs) != set(pins):
        raise SystemExit('Missing or extra complete-image fixtures')
    for name, definitions in inputs.items():
        if definitions.get('image') != 'header ++ (List.replicate 3976 0 ++ suffix)':
            raise SystemExit('Changed complete-image representation: '+name)
        header = expand_literal(definitions['header'])
        suffix = expand_literal(definitions['suffix'])
        image = header + bytes(3976) + suffix
        pin = pins[name]
        if len(header) != 120 or len(image) != pin['length'] or hashlib.sha256(image).hexdigest() != pin['sha256']:
            raise SystemExit('Changed retained complete-image bytes: '+name)
        if expand_literal(definitions['nameBytes']) != pin['name'].encode():
            raise SystemExit('Changed retained requested name: '+name)
        if hashlib.sha256(expand_literal(definitions['source'])).hexdigest() != pin['source_sha256']:
            raise SystemExit('Changed retained original source: '+name)
        if 'renamedImage' in definitions:
            other = pins[name.replace('_mix_', '_Mix9_')]
            raw = expand_literal(definitions['renamedImage'])
            if hashlib.sha256(raw).hexdigest() != other['sha256']:
                raise SystemExit('Changed complete name-replay image: '+name)


def require_statements(lines, fixtures, kind):
    pinned = json.loads((ROOT/'tools/native_image_fixtures/expected-statements.json').read_text())[kind]
    actual = {name: lines[index].split(' := by ', 1)[0] for index, name in fixtures.items()}
    if actual != pinned:
        raise SystemExit('Changed fixed fixture theorem statements')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture-source', type=Path)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--jobs', type=int, choices=[1, 2], default=1)
    started = time.monotonic()
    parser.add_argument('--fresh', action='store_true', help='Check fresh core fixtures against the pinned fresh theorem inventory')
    args = parser.parse_args()
    model = inventory((LEAN / 'Oak' / 'NativeBitwiseImage.lean').read_text().splitlines())
    lines = (args.fixture_source or LEAN / 'NativeBitwiseImageFixtures.lean').read_text().splitlines()
    fixtures = inventory(lines)
    require_inventory('model', model.values())
    kind = 'fresh' if args.fresh else 'fixtures'
    require_inventory(kind, fixtures.values())
    require_statements(lines, fixtures, kind)
    verify_inputs(lines)
    run(['lake', 'build', 'Oak.NativeBitwiseImage'])
    check_proof('import Oak.NativeBitwiseImage\n', list(model.values()))
    # Every retained fixture theorem is one complete line. Atomic kernel decisions
    # and checked list/profile composition preserve the full recognizer equality.
    # Fail closed if a renderer change would defeat declaration-based sharding.
    for index in fixtures:
        if ' := by ' not in lines[index]:
            raise SystemExit('Unsupported multiline fixture declaration')
    positive = [i for i, name in fixtures.items() if name.endswith('.admitted') or name.endswith('.loaded')]
    negative = [i for i in fixtures if i not in positive]
    batches = [positive[i:i+4] for i in range(0, len(positive), 4)] + [negative[i:i+8] for i in range(0, len(negative), 8)]
    checked = set()
    def check_batch(number, batch):
        selected = set(batch)
        source = fixture_source(lines, fixtures, selected)
        expected = [fixtures[i] for i in batch]
        with PRINT_LOCK:
            print(f'Checking fixture batch {number}/{len(batches)} ({len(batch)} declarations)', flush=True)
        check_proof(source, expected)
        return number, expected
    # One worker in a fresh single-thread Lean process; no repository-wide
    # build or unbounded process fanout. This bounds proof-elaboration memory.
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
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
    admissions = sum(name.endswith('.admitted') for name in fixtures.values())
    loads = sum(name.endswith('.loaded') for name in fixtures.values())
    report = dict(admissions=admissions, loads=loads, refusals=len(negative),
                  audited_roots=len(model)+len(checked), seconds=time.monotonic()-started,
                  max_child_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                  jobs=args.jobs, per_process_memory_mib=3000, per_process_timeout_seconds=240)
    print(f'Kernel checked {admissions} admissions, {loads} decoded-address loads and {len(negative)} refusals; '
          f'{len(model)+len(checked)} exact theorem-closure reports; allowed axioms only.')
    print(json.dumps(report, sort_keys=True))
    if args.report:
        args.report.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
