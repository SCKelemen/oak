#!/usr/bin/env python3
"""Fresh trust-zero check of the bounded extracted-copy memory adapter.

Reuses the existing proof-gate parser/import walker; no toolchain installation
or artifact acceptance profile is added. Source digests are custody checks,
not source/frontend/target-refinement proofs. The Go equipped suite additionally
regenerates extraction and executes the frozen source/layout/refusal fixtures.
"""
import argparse
import hashlib
import os
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
from wasm_module_proof.check import audit_reports, dependency_order, run

SOURCE = ROOT / 'spec' / 'lean'
MODULE = 'Oak.StatefulCopyControls'
THEOREMS = (
    *('Oak.StatefulCopy.' + name for name in (
        'logical_size', 'logical_get', 'represented_read', 'represented_address',
        'represented_store', 'decode_encode', 'decode_exact', 'extracted_total',
        'writeWindow_inside', 'writeWindow_outside', 'writeWindow_original',
        'observed_words_exact', 'writeback_observes', 'liftedCopy_total',
        'liftedCopy_short', 'liftedCopy_empty', 'observes_with_frames')),
    *('Oak.StatefulCopy.Controls.' + name for name in (
        'valid_windows', 'successful_copy', 'successful_contract', 'short_zero_fuel',
        'one_past_empty', 'same_owner_disjoint', 'overlap_refused',
        'dangling_empty_refused', 'uninitialized_refused', 'wrapping_endpoint_refused',
        'malformed_result_refused', 'wrong_live_length', 'success_fuel_exhaustion',
        'corrupt_copy_refused', 'wrong_observed_count', 'scratch_frame_composition')),
)
SOURCE_BINDINGS = {
    'compiler/testdata/stateful_copy/main.oak': 'b7e0745da1b388e29c281c2f15d89ef4061ab33f1c5eb55f8dda7297d87f95f5',
    'stdlib/bytes.oak': 'e4da6755200dbcfe409f9ec11ea928515d7fcd91838ba63e284d1c9f30603f7c',
    'stdlib/std.oak': '10bbc09408ba76fccbac59f06936411e29eff8b81777c788b2b77b8e57eaa0e7',
    'spec/lean/Oak/Stdlib/BytesExtracted.lean': 'fab665c9cf89f45fca96fb4540b727fb3210db6e8b7f243ec9813f735b517631',
    # This freezes the production specialization/layout observations, not their
    # unproved semantic connection to physical ABI execution.
    'compiler/stateful_copy_contract_test.go': '11141b56b70aa5ad63a6daadf8ca979fb6e3ac9746b56fb37b340099342fd0e1',
}


def check_bindings(root=ROOT, bindings=SOURCE_BINDINGS):
    for rel, expected in bindings.items():
        if hashlib.sha256((root / rel).read_bytes()).hexdigest() != expected:
            raise ValueError('frozen source/layout binding changed: ' + rel)


def audit_source():
    return 'import ' + MODULE + '\nset_option format.width 100000\n' + ''.join(
        '#print axioms ' + name + '\n' for name in THEOREMS)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    check_bindings()
    prefix = run([args.lake, 'env', 'lean', '--print-prefix'], cwd=SOURCE).strip().splitlines()[-1]
    if not Path(prefix).is_absolute():
        raise RuntimeError('lake returned a nonabsolute Lean installation prefix')
    lean = Path(prefix) / 'bin' / 'lean'
    version = run([str(lean), '--version']).strip()
    if not version.startswith('Lean (version 4.33.1,'):
        raise RuntimeError('proof gate requires pinned Lean 4.33.1: ' + version)
    committed_audit = SOURCE / 'Oak' / 'StatefulCopyAudit.lean'
    if committed_audit.read_text() != audit_source():
        raise RuntimeError('stateful-copy audit inventory differs from required roots')
    order = dependency_order(MODULE, SOURCE)
    paths = [p for _, p in order] + [committed_audit] + [ROOT / p for p in SOURCE_BINDINGS]
    identities = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    with tempfile.TemporaryDirectory(prefix='oak-stateful-copy-proof-') as tmp:
        build = Path(tmp)
        env = dict(os.environ, LEAN_PATH=str(build), LEAN_NUM_THREADS='1')
        for name, path in order:
            output = build.joinpath(*name.split('.')).with_suffix('.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            log = run([str(lean), '-j1', '-t0', '-M1600', '-o', str(output), str(path)], cwd=SOURCE, env=env)
            if log.strip():
                raise RuntimeError('unexpected Lean diagnostics: ' + log)
            print('kernel checked ' + name, flush=True)
        audit = build / 'StatefulCopyAudit.lean'
        audit.write_text(audit_source())
        log = run([str(lean), '-j1', '-t0', '-M1600', str(audit)], cwd=SOURCE, env=env)
        audit_reports(log, THEOREMS)
        print(log, end='', flush=True)
    check_bindings()
    for rel, digest in identities.items():
        if hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() != digest:
            raise RuntimeError('source changed during proof build: ' + rel)
        print('source sha256 ' + digest + ' ' + rel, flush=True)
    print(f'fresh source closure: {len(order)} local modules; exact axiom inventory: {len(THEOREMS)} theorems; frozen bindings: {len(SOURCE_BINDINGS)}', flush=True)


if __name__ == '__main__':
    main()
