#!/usr/bin/env python3
"""Fresh total-Wasm proof gate, retaining every successful-domain proof check.

Build the superset source closure once, then check both committed root
inventories and both control files. No candidate .olean files enter LEAN_PATH.
The unchanged original gate provides the fail-closed audit and import scanner.
"""
import argparse
import hashlib
import importlib.util
import os
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'spec' / 'lean'
EXACT_PATH = ROOT / 'tools' / 'wasm_module_proof' / 'check.py'
EXACT_SPEC = importlib.util.spec_from_file_location('wasm_module_exact_check', EXACT_PATH)
EXACT = importlib.util.module_from_spec(EXACT_SPEC)
EXACT_SPEC.loader.exec_module(EXACT)
MODULE = 'Oak.WasmBitwiseModuleTotal'
THEOREMS = tuple('Oak.WasmAssembler.' + name for name in (
    'module_name_bytes_iff', 'module_bad_name_witness', 'module_length_guard_iff',
    'bitwise_module_total', 'module_success_count', 'module_result_refuses_iff',
    'bitwise_module_refusal_iff', 'module_result_size', 'bitwise_module_terminates',
    'bitwise_module_total_fuel_independent',
))
AUDIT = SOURCE / 'Oak' / 'WasmBitwiseModuleTotalAudit.lean'
CONTROLS = SOURCE / 'WasmBitwiseModuleTotalControls.lean'
EXACT_AUDIT = SOURCE / 'Oak' / 'WasmBitwiseModuleExactAudit.lean'


def audit_source(module, names):
    if not names or len(set(names)) != len(names):
        raise ValueError('empty or duplicate required theorem inventory')
    return 'import ' + module + '\nset_option format.width 100000\n' + ''.join(
        '#print axioms ' + name + '\n' for name in names)


def checked_audits():
    inventories = (
        (EXACT_AUDIT, EXACT.MODULE, EXACT.THEOREMS),
        (AUDIT, MODULE, THEOREMS),
    )
    for path, module, names in inventories:
        if path.read_text() != audit_source(module, names):
            raise RuntimeError('committed audit inventory differs from required roots: ' + str(path))
    return inventories


def require_version(version):
    if not version.startswith('Lean (version 4.33.1,'):
        raise RuntimeError('proof gate requires pinned Lean 4.33.1: ' + version)


def checked_order():
    order = EXACT.dependency_order(MODULE)
    required = {name for name, _ in EXACT.dependency_order(EXACT.MODULE)}
    if not required.issubset(name for name, _ in order):
        raise RuntimeError('total source closure lost successful-domain dependencies')
    return order


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    prefix = EXACT.run([args.lake, 'env', 'lean', '--print-prefix'], cwd=SOURCE).strip().splitlines()[-1]
    if not Path(prefix).is_absolute():
        raise RuntimeError('lake returned a nonabsolute Lean installation prefix')
    lean = Path(prefix) / 'bin' / 'lean'
    require_version(EXACT.run([str(lean), '--version']).strip())
    inventories = checked_audits()
    order = checked_order()
    paths = [p for _, p in order] + [EXACT_AUDIT, AUDIT, EXACT.CONTROLS, CONTROLS,
        EXACT_PATH, Path(__file__).resolve()]
    identities = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    with tempfile.TemporaryDirectory(prefix='oak-wasm-module-total-proof-') as tmp:
        build = Path(tmp)
        env = dict(os.environ, LEAN_PATH=str(build), LEAN_NUM_THREADS='1')
        command = [str(lean), '-j1', '-t0', '-M2048', '-DwarningAsError=true']
        for name, path in order:
            output = build.joinpath(*name.split('.')).with_suffix('.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            log = EXACT.run(command + ['-o', str(output), str(path)], cwd=SOURCE, env=env)
            if log.strip():
                print(log, end='', flush=True)
            print('kernel checked ' + name, flush=True)
        for path, module, names in inventories:
            isolated = build / path.name
            isolated.write_text(audit_source(module, names))
            log = EXACT.run(command + [str(isolated)], cwd=SOURCE, env=env)
            EXACT.audit_reports(log, names)
            print(log, end='', flush=True)
            print('checked exact axiom inventory: ' + path.name, flush=True)
        for controls in (EXACT.CONTROLS, CONTROLS):
            log = EXACT.run(command + [str(controls)], cwd=SOURCE, env=env)
            if log.strip():
                print(log, end='', flush=True)
            print('kernel checked ' + controls.stem, flush=True)
    for rel, digest in identities.items():
        if hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() != digest:
            raise RuntimeError('source changed during proof build: ' + rel)
    for rel, digest in identities.items():
        print('source sha256 ' + digest + ' ' + rel, flush=True)
    print(f'fresh source closure: {len(order)} local modules; exact axiom inventories: '
          f'{len(EXACT.THEOREMS)} successful-domain + {len(THEOREMS)} total-outcome roots; '
          'trust-zero controls: 2', flush=True)


if __name__ == '__main__':
    main()
