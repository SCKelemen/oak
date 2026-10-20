#!/usr/bin/env python3
"""Fresh trust-zero total native-writer outcome proof and exact axiom gate."""
import argparse
import hashlib
import importlib.util
import os
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'spec' / 'lean'
_spec = importlib.util.spec_from_file_location('native_success_gate',
    ROOT / 'tools' / 'native_envelope_proof' / 'check.py')
BASE = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(BASE)
MODULE = 'Oak.NativeBitwiseEnvelopeTotalControls'
PRODUCER = 'Oak.BitwiseELFProducer.'
THEOREMS = BASE.THEOREMS + tuple(PRODUCER + name for name in (
    'name_scan_total_suffix', 'name_scan_total', 'packed_read_octets',
    'native_read_value', 'read_value_bytes', 'startupCheck_iff',
    'sourceInitial_eq', 'image_refuses_outer', 'image_refuses_scan',
    'image_refuses_startup', 'image_total_machine', 'image_total',
    'image_refusal_exact', 'image_total_ne_none',
    'TotalControls.unsupported_arch', 'TotalControls.empty_name',
    'TotalControls.oversized_name', 'TotalControls.maximal_ascii_name',
    'TotalControls.first_invalid_byte', 'TotalControls.last_invalid_byte',
    'TotalControls.initial_false_short_circuit', 'TotalControls.zero_scan_fuel',
    'TotalControls.zero_name_byte', 'TotalControls.wrong_text_extent',
    'TotalControls.zero_startup', 'TotalControls.short_capacity',
))
ALLOWED = BASE.ALLOWED

def audit_reports(output, expected=THEOREMS):
    BASE.audit_reports(output, expected)

def dependency_order(module, source=SOURCE):
    return BASE.dependency_order(module, source)

run = BASE.run


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
    committed_audit = SOURCE / 'Oak' / 'NativeBitwiseEnvelopeTotalAudit.lean'
    if committed_audit.read_text() != audit_source:
        raise RuntimeError('committed native-envelope total-outcome audit inventory differs from the required roots')
    order = dependency_order(MODULE)
    identities = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for _, p in order}
    with tempfile.TemporaryDirectory(prefix='oak-native-envelope-total-proof-') as tmp:
        build = Path(tmp)
        env = dict(os.environ, LEAN_PATH=str(build), LEAN_NUM_THREADS='1')
        for name, path in order:
            output = build.joinpath(*name.split('.')).with_suffix('.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            log = run([str(lean), '-j1', '-t0', '-M3000', '-o', str(output), str(path)], cwd=SOURCE, env=env)
            if log.strip():
                print(log, end='', flush=True)
            print('kernel checked ' + name, flush=True)
        audit = build / 'NativeEnvelopeTotalAudit.lean'
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
