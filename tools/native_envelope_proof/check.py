#!/usr/bin/env python3
"""Fresh, isolated kernel build of the source-extracted native envelope proof.

Every local transitive import is rebuilt from the current source with trust zero.
Only the pinned release's core/Std files are reused; candidate .olean caches are
never on LEAN_PATH. This is an implementation-refinement proof gate, not a claim
that extraction, the Go seed, the C compiler, or arbitrary bodies are verified.
"""
import argparse
import hashlib
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'spec' / 'lean'
MODULE = 'Oak.NativeBitwiseEnvelopeCorrectness'
PRODUCER = 'Oak.BitwiseELFProducer.'
SPEC = 'Oak.NativeBitwiseEnvelope.'
THEOREMS = (
    *(PRODUCER + name for name in (
        'scan_index', 'name_scan_exact', 'zero_index', 'zero_exact', 'word_exact',
        'copy_index', 'text_copy_exact', 'name_copy_exact', 'wordOctets_eq',
        'native_word_bytes', 'bytes_overlay', 'zero_patches',
        'nativePatches_ordered', 'nativePatches_bytes', 'sourceSections_nat',
        'startup_reads', 'writer_patches_exact', 'image_exact', 'image_frame',
        'image_output_admitted')),
    *(SPEC + name for name in (
        'E_length', 'E_size_bound', 'E_arm64_size_bound', 'E_rv64_size_bound',
        'startup_read_footprint', 'startup_read_index', 'startup_read_shift_counts',
        'E_body_slice', 'E_strictProfile', 'E_accepts')),
)
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}
REPORT = re.compile(r"'([^'\n]+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)")


def audit_reports(output, expected=THEOREMS):
    if not expected or len(set(expected)) != len(expected):
        raise ValueError('empty or duplicate expected theorem inventory')
    seen, end = set(), 0
    for match in REPORT.finditer(output):
        if output[end:match.start()].strip():
            raise ValueError('unexpected output in axiom audit')
        name, axioms = match.groups()
        if name not in expected or name in seen:
            raise ValueError('unexpected or duplicate theorem report: ' + name)
        for axiom in (x.strip() for x in (axioms or '').split(',')):
            if axiom and axiom not in ALLOWED:
                raise ValueError('forbidden axiom: ' + axiom)
        seen.add(name)
        end = match.end()
    if output[end:].strip() or seen != set(expected):
        raise ValueError('missing theorem report or unexpected trailing output')


def dependency_order(module, source=SOURCE):
    order, visiting, seen = [], set(), set()

    def visit(name):
        if name in seen:
            return
        if name in visiting:
            raise ValueError('cyclic local import: ' + name)
        if not re.fullmatch(r'Oak(?:\.[A-Za-z0-9_]+)+', name):
            raise ValueError('unexpected local module name: ' + name)
        path = source.joinpath(*name.split('.')).with_suffix('.lean')
        if not path.is_file():
            raise ValueError('missing local source: ' + name)
        visiting.add(name)
        for line in path.read_text().splitlines():
            if line.startswith('import '):
                for imported in line[7:].split():
                    if imported.startswith('Oak.'):
                        visit(imported)
                    elif not re.fullmatch(r'(?:Lean|Std|Init)(?:\.[A-Za-z0-9_]+)*', imported):
                        raise ValueError('unexpected nonlocal import: ' + imported)
        visiting.remove(name)
        seen.add(name)
        order.append((name, path))

    visit(module)
    return order


def run(command, **kwargs):
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=900, **kwargs)
    if result.returncode:
        raise RuntimeError(f'command failed ({result.returncode}): {command}\n{result.stdout}')
    return result.stdout


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    prefix = run([args.lake, 'env', 'lean', '--print-prefix'], cwd=SOURCE).strip().splitlines()[-1]
    if not Path(prefix).is_absolute():
        raise RuntimeError('lake returned a nonabsolute Lean installation prefix')
    lean = Path(prefix) / 'bin' / 'lean'
    version = run([str(lean), '--version']).strip()
    if not version.startswith('Lean (version 4.33.1,'):
        raise RuntimeError('proof gate requires pinned Lean 4.33.1: ' + version)
    audit_source = 'import ' + MODULE + '\nset_option format.width 100000\n' + ''.join(
        '#print axioms ' + name + '\n' for name in THEOREMS)
    committed_audit = SOURCE / 'Oak' / 'NativeBitwiseEnvelopeAudit.lean'
    if committed_audit.read_text() != audit_source:
        raise RuntimeError('committed native-envelope audit inventory differs from the required roots')
    order = dependency_order(MODULE)
    identities = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for _, p in order}
    with tempfile.TemporaryDirectory(prefix='oak-native-envelope-proof-') as tmp:
        build = Path(tmp)
        env = dict(os.environ, LEAN_PATH=str(build), LEAN_NUM_THREADS='1')
        for name, path in order:
            output = build.joinpath(*name.split('.')).with_suffix('.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            log = run([str(lean), '-j1', '-t0', '-M3000', '-o', str(output), str(path)], cwd=SOURCE, env=env)
            if log.strip():
                print(log, end='', flush=True)
            print('kernel checked ' + name, flush=True)
        audit = build / 'NativeEnvelopeAudit.lean'
        audit.write_text(audit_source)
        log = run([str(lean), '-j1', '-t0', '-M3000', str(audit)], cwd=SOURCE, env=env)
        audit_reports(log)
        print(log, end='', flush=True)
    for rel, digest in identities.items():
        if hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() != digest:
            raise RuntimeError('source changed during proof build: ' + rel)
    print(f'fresh source closure: {len(order)} local modules; exact axiom inventory: {len(THEOREMS)} theorems', flush=True)


if __name__ == '__main__':
    main()
