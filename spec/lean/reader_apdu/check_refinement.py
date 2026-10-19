#!/usr/bin/env python3
"""Fixed current-source extraction and generated-reader refinement profile."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import signal
import sys
import time

import check as host
from refinement_audit_consumer import diagnostics
from support import decode, members, read_regular, require, safe_path, verify_file

HERE = Path(__file__).absolute().parent
REPO = HERE.parents[2]
CONTRACT_SHA256 = '2452db779f5c39c630a48f72e3f11c9e25c36d4874bbf1fc6fae275ac3218138'
WHOLE_SECONDS = 600
EXTRACTION_BYTES = 65536
MODULES = ('BoundedReaderModel', 'BoundedReaderExtracted', 'BoundedReaderRefinement')
PHASES = ('controls', 'extract', 'reader', 'extracted', 'refinement', 'audit')
ARTIFACT_CAPS = {'audit-stdout.log': 12 * 1024**2, 'audit-stderr.log': 0,
                 'result.json': 32768, 'object-hashes.json': 32768,
                 'extracted/raw.lean': EXTRACTION_BYTES,
                 'extracted/BoundedReaderExtracted.lean': EXTRACTION_BYTES,
                 'extracted/extraction.json': EXTRACTION_BYTES}


def load_contract(directory=HERE):
    raw = read_regular(directory / 'refinement_contract.json', 1024**2)
    require(hashlib.sha256(raw).hexdigest() == CONTRACT_SHA256, 'locked refinement contract')
    contract = decode(raw)
    require(contract['schema'] == 'oak-reader-refinement-hosted-contract-v1' and
            contract['toolchain'] == 'leanprover/lean4:v4.33.1' and
            contract['flags'] == host.FLAGS and contract['expected_candidate_declarations'] == 753 and
            contract['expected_imports'] == 1050, 'fixed refinement profile')
    return contract


def test_output(stdout, stderr, expected):
    """Direct Go test-binary verbose output; zero children and no skips allowed."""
    require(stderr == b'' and 0 < len(stdout) <= 256 * 1024 and stdout.endswith(b'\n'),
            'complete bounded Go output')
    lines = stdout.decode('ascii', 'strict').splitlines()
    require(lines and lines[-1] == 'PASS' and len(lines) == 2 * len(expected) + 1,
            'exact Go output inventory')
    require(len(expected) == len(set(expected)), 'unique selected test names')
    for index, name in enumerate(expected):
        require(re.fullmatch(r'Test[A-Za-z0-9_]+', name) is not None, 'root-only selector')
        require(lines[2 * index] == '=== RUN   ' + name, 'exact Go run order')
        require(re.fullmatch(r'--- PASS: ' + re.escape(name) + r' \([0-9]+\.[0-9]+s\)',
                             lines[2 * index + 1]) is not None, 'exact Go pass with no skip')
    return {'roots': len(expected), 'children': 0, 'skips': 0}


def bytes_identity(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def extraction_equality(leaves, contract, deadline, repo=REPO):
    """Receipt equality plus independent current-source and generated-span checks."""
    require(time.monotonic() < deadline, 'extraction verification deadline')
    expected = contract['extraction']
    require(set(leaves) == {'raw.lean', 'BoundedReaderExtracted.lean', 'extraction.json'},
            'exact extraction output names')
    for name, data in leaves.items():
        require(time.monotonic() < deadline, 'extraction verification deadline')
        require(type(data) is bytes and len(data) <= EXTRACTION_BYTES and
                bytes_identity(data) == expected['files'][name], 'locked extraction bytes')
    raw = leaves['raw.lean']
    profiled = leaves['BoundedReaderExtracted.lean']
    require(raw == read_regular(repo / expected['raw_reference'], EXTRACTION_BYTES) and
            profiled == read_regular(repo / expected['profiled_reference'], EXTRACTION_BYTES),
            'actual output equals committed references')
    require(raw.replace(b'set_option maxRecDepth 65536\n', b'set_option maxRecDepth 2048\n', 1)
            .replace(b'set_option maxHeartbeats 4000000\n', b'set_option maxHeartbeats 200000\n', 1)
            == profiled, 'only two accepted header budget edits')
    receipt = decode(leaves['extraction.json'])
    require(receipt == expected['receipt'] and receipt['status'] == 'extracted_not_proved',
            'exact accepted extraction receipt')
    # This field identifies the historical extraction profile, not the new whole tree.
    require(receipt['tree_requires_outer_authentication'] == contract['historical_extraction_tree'],
            'historical receipt authority')
    source_bytes = {}
    for pin in receipt['source_pins']:
        require(time.monotonic() < deadline, 'extraction source deadline')
        source = read_regular(repo / pin['Path'], pin['Bytes'])
        require(bytes_identity(source) == {'bytes': pin['Bytes'], 'sha256': pin['SHA256']},
                'current original source binding')
        source_bytes[pin['Path']] = source
    for pin in receipt['fixture_pins']:
        require(time.monotonic() < deadline, 'extraction fixture deadline')
        data = read_regular(repo / contract['fixture'] / pin['Path'], pin['Bytes'])
        require(bytes_identity(data) == {'bytes': pin['Bytes'], 'sha256': pin['SHA256']},
                'current qualified fixture binding')
    require(len(receipt['declarations']) == 16 and len(set(d['name'] for d in receipt['declarations'])) == 16,
            'exact generated declaration inventory')
    spans = set()
    for declaration in receipt['declarations']:
        require(time.monotonic() < deadline, 'extraction span deadline')
        a, b = declaration['raw_start_byte'], declaration['raw_end_byte_exclusive']
        c, d = declaration['profiled_start_byte'], declaration['profiled_end_byte_exclusive']
        require(0 <= a < b <= len(raw) and 0 <= c < d <= len(profiled) and
                raw[a:b] == profiled[c:d] and
                hashlib.sha256(raw[a:b]).hexdigest() == declaration['raw_span_sha256'],
                'exact raw/profiled declaration span')
        for key in ('source_span', 'generic_source_span'):
            if key not in declaration:
                continue
            span = declaration[key]
            lines = source_bytes[span['Path']].splitlines(keepends=True)
            require(1 <= span['FirstLine'] <= span['LastLine'] <= len(lines), 'source span bounds')
            data = b''.join(lines[span['FirstLine'] - 1:span['LastLine']])
            require(bytes_identity(data) == {'bytes': span['Bytes'], 'sha256': span['SHA256']},
                    'current original source span')
            spans.add((span['Path'], span['FirstLine'], span['LastLine']))
    require(len(spans) == 12, 'exact current original source-span inventory')
    require(time.monotonic() < deadline, 'complete extraction verification deadline')
    return {name: bytes_identity(data) for name, data in leaves.items()}


def load_extraction(work, contract, deadline, repo=REPO):
    require(time.monotonic() < deadline, 'extraction read deadline')
    directory = work / 'extracted'
    require(members(directory, 3) == {'raw.lean', 'BoundedReaderExtracted.lean', 'extraction.json'},
            'exact fresh extraction membership')
    leaves = {name: read_regular(directory / name, EXTRACTION_BYTES)
              for name in ('raw.lean', 'BoundedReaderExtracted.lean', 'extraction.json')}
    return leaves, extraction_equality(leaves, contract, deadline, repo)


def validate_retained_result(result, contract):
    require(type(result) is dict and result.get('accepted') is True and
            result.get('generated_definition_refinement') is True and
            result.get('oak_implementation_refinement') is False and
            result.get('source_contract_sha256') == CONTRACT_SHA256,
            'accepted exact generated-definition scope')
    require(type(result.get('checkout_commit')) is str and
            re.fullmatch('[0-9a-f]{40}', result['checkout_commit']) is not None,
            'current checkout identity')
    require(result.get('extraction') == contract['extraction']['files'] and
            result.get('historical_extraction_tree') == contract['historical_extraction_tree'],
            'retained extraction identities')
    require(result.get('controls') == {'roots': 62, 'children': 0, 'skips': 0} and
            result.get('emit') == {'roots': 1, 'children': 0, 'skips': 0}, 'complete selected Go roots')
    for key in ('controls', 'emit'):
        require(all(type(value) is int for value in result[key].values()), 'typed selected test counts')
    audit = result.get('audit', {})
    require(type(audit) is dict and all(type(audit.get(k)) is int for k in
            ('named_theorems', 'named_controls', 'candidate_declarations', 'actual_imports', 'source_examples')),
            'typed retained audit counts')
    require(audit.get('accepted') is True and audit.get('named_theorems') == 117 and
            audit.get('named_controls') == 18 and audit.get('candidate_declarations') == 753 and
            audit.get('actual_imports') == 1050 and
            audit.get('source_examples') == 0 and audit.get('anonymous_examples_persisted') is False and
            audit.get('generated_definition_refinement_established') is True and
            audit.get('oak_implementation_refinement_established') is False and
            audit.get('implementation_refinement_established') is False and
            audit.get('imported_distribution_normal_trust') is True and
            audit.get('allowed_axioms') == sorted(contract['allowed_axioms']), 'retained audit inventory')
    for key, low, high in (('dependency_nodes', 1, 10000), ('dependency_edges', 0, 100000),
                           ('independent_processed_nodes', 1, 1180000),
                           ('independent_edge_occurrences', 0, 11800000)):
        require(type(audit.get(key)) is int and low <= audit[key] <= high, 'bounded retained graph counters')
    objects = result.get('objects')
    require(type(objects) is dict and set(objects) == {n + '.olean' for n in MODULES},
            'three exact retained objects')
    for obj in objects.values():
        require(type(obj) is dict and set(obj) == {'bytes', 'sha256', 'snapshot'} and
                type(obj['bytes']) is int and 0 < obj['bytes'] <= 8 * 1024**2 and
                type(obj['sha256']) is str and re.fullmatch('[0-9a-f]{64}', obj['sha256']) is not None,
                'bounded typed object receipt')
        snap = obj['snapshot']
        require(type(snap) is list and len(snap) == 8 and
                all(type(v) is int and v >= 0 for v in snap) and snap[1] > 0 and
                host.stat.S_ISREG(snap[2]) and snap[2] & 0o077 == 0 and
                snap[4] == 1 and snap[5] == obj['bytes'], 'coherent private object snapshot')
    records = result.get('direct_processes')
    require(type(records) is list and len(records) == 6, 'six exact direct phases')
    for phase, record in zip(PHASES, records):
        require(type(record) is dict and record.get('phase') == phase and
                type(record.get('returncode')) is int and record['returncode'] == 0 and
                record.get('pipe_eof') == ['stderr', 'stdout'] and record.get('overflow') is False and
                record.get('direct_child_joined') is True and
                record.get('arbitrary_descendant_emptiness_established') is False,
                'complete successful direct phase')
        argv = record.get('argv')
        require(type(argv) is list and 1 <= len(argv) <= 32 and
                all(type(v) is str and '\x00' not in v and len(v.encode()) <= 4096 for v in argv),
                'bounded retained argv')
    argv = records[-1]['argv']
    driver = host.retained_path(argv[-1])
    lean = host.retained_path(argv[0])
    require(len(argv) == len(host.FLAGS) + 3 and argv[1:-2] == host.FLAGS and
            argv[-2] == '--root=' + str(driver.parent) and
            driver.parts[-4:] == ('spec', 'lean', 'reader_apdu', 'RefinementAuditDriver.lean') and
            lean.name == 'lean' and lean.parent.name == 'bin' and
            all(r['argv'][0] == str(lean) for r in records[2:]) and
            records[0]['argv'][0] == records[1]['argv'][0], 'exact audit and executable paths')
    repo = driver.parents[3]
    work = host.retained_path(records[1]['argv'][-1].removeprefix('-reader-output=')).parent
    require(records[0]['argv'] == [records[1]['argv'][0], '-test.v', '-test.count=1',
                '-test.timeout=10s', '-test.run=^TestBoundedReaderControl'] and
            records[1]['argv'] == [records[0]['argv'][0], '-test.v', '-test.count=1',
                '-test.timeout=45s', '-test.run=^TestBoundedReaderExtractionEmit$',
                '-reader-source-root=' + str(repo), '-reader-fixture=' + str(repo / contract['fixture']),
                '-reader-output=' + str(work / 'extracted')], 'exact selected extraction argv')
    for record, module in zip(records[2:5], MODULES):
        require(record['argv'] == [str(lean), *host.FLAGS, '--root=' + str(repo / 'spec/lean'),
                    '-o', str(work / 'objects/Oak/Stdlib' / (module + '.olean')),
                    str(repo / 'spec/lean/Oak/Stdlib' / (module + '.lean'))],
                'exact fresh module argv')
    return str(driver)


def retention_manifest(result, leaves, contract):
    driver = validate_retained_result(result, contract)
    require(set(leaves) == set(ARTIFACT_CAPS) - {'result.json', 'object-hashes.json'},
            'exact retained evidence leaves')
    for name, data in leaves.items():
        require(type(data) is bytes and len(data) <= ARTIFACT_CAPS[name], 'retained leaf cap')
    require(leaves['audit-stdout.log'] and leaves['audit-stderr.log'] == b'', 'complete retained audit')
    for name, expected in contract['extraction']['files'].items():
        require(bytes_identity(leaves['extracted/' + name]) == expected, 'retained exact extraction')
    values = dict(leaves, **{'result.json': host.retained_json(result)})
    value = {'schema': 'oak-reader-refinement-hosted-retention-v1',
             'source_contract_sha256': CONTRACT_SHA256, 'source_inputs': contract['inputs'],
             'checkout_commit': result['checkout_commit'], 'historical_extraction_tree': contract['historical_extraction_tree'],
             'toolchain': contract['toolchain'], 'lean_executable_sha256': contract['lean_executable_sha256'],
             'official_linux_archive_sha256': contract['official_linux_archive_sha256'],
             'audit_driver_path': driver, 'files': {n: bytes_identity(d) for n, d in values.items()},
             'objects': {n: {k: v[k] for k in ('bytes', 'sha256')} for n, v in result['objects'].items()},
             'scope': 'full audit replay and exact extraction bytes; objects are hash receipts only'}
    return host.retained_json(value)


def verify_retention(work, deadline):
    # Pre-upload check of the original work directory; not an artifact-only replay.
    expected_names = {'objects', 'home', 'tmp', 'extracted', 'result.json', 'object-hashes.json'} | {
        phase + suffix for phase in PHASES for suffix in ('-stdout.log', '-stderr.log', '-execution.json')}
    require(members(work, 24) == expected_names and
            members(work / 'extracted', 3) == {'raw.lean', 'BoundedReaderExtracted.lean', 'extraction.json'},
            'exact pre-upload work membership')
    contract = load_contract()
    leaves = {}
    for name, cap in ARTIFACT_CAPS.items():
        require(time.monotonic() < deadline, 'retention deadline')
        leaves[name] = read_regular(work / name, cap)
    result_bytes = leaves.pop('result.json')
    result = decode(result_bytes)
    require(host.retained_json(result) == result_bytes, 'canonical retained result')
    manifest = leaves.pop('object-hashes.json')
    require(manifest == retention_manifest(result, leaves, contract), 'exact retained manifest and result')
    require(time.monotonic() < deadline, 'retention deadline')


def main():
    started = time.monotonic()
    deadline = started + WHOLE_SECONDS
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', required=True)
    parser.add_argument('--extractor', required=True)
    parser.add_argument('--checkout-commit', required=True)
    parser.add_argument('--work', required=True)
    args = parser.parse_args()
    def interrupted(signum, frame):
        raise RuntimeError('hosted refinement interrupted')
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    require(sys.platform == 'linux' and platform.machine() == 'x86_64', 'Linux/amd64 profile')
    require(re.fullmatch('[0-9a-f]{40}', args.checkout_commit) is not None, 'checkout SHA')
    lean, extractor, work = map(safe_path, (args.lean, args.extractor, args.work))
    require(lean.name == 'lean' and lean.parent.name == 'bin' and os.access(lean, os.X_OK), 'Lean executable')
    require(os.access(extractor, os.X_OK) and not work.exists(), 'extractor and fresh work')
    sysroot = lean.parent.parent
    os.umask(0o077)
    work.mkdir(mode=0o700)
    result = {'accepted': False, 'generated_definition_refinement': False, 'oak_implementation_refinement': False}
    try:
        setup_deadline = started + 30
        contract = load_contract()
        harness = REPO / '.github/scripts/reader_refinement'
        require(members(harness, 4) == {'adapter.go', 'adapter_test.go', 'emit_test.go', 'fixture'},
                'exact named-file build inputs and no default.pgo')
        host.physical_guards(work)
        fs = os.statvfs(work)
        require(fs.f_bavail * fs.f_frsize >= host.FLOOR_BYTES + host.FRESH_BYTES, 'fresh output admission')
        for relative, expected in contract['inputs'].items():
            verify_file(REPO / relative, expected, setup_deadline)
        binary, snapshot = read_regular(extractor, 80 * 1024**2, snapshot=True)
        require(binary, 'nonempty extraction test binary')
        binary_pin = dict(bytes_identity(binary), snapshot=snapshot)
        del binary
        distribution = decode(read_regular(HERE / 'distribution.json', 2 * 1024**2))
        host.verify_distribution(sysroot, distribution['files'], setup_deadline)
        objects = work / 'objects'
        (objects / 'Oak/Stdlib').mkdir(parents=True, mode=0o700)
        for name in ('home', 'tmp', 'extracted'):
            (work / name).mkdir(mode=0o700)
        env = {'HOME': str(work / 'home'), 'TMPDIR': str(work / 'tmp'), 'LANG': 'C', 'LC_ALL': 'C',
               'PATH': str(sysroot / 'bin') + ':/usr/bin:/bin', 'LEAN_PATH': str(objects),
               'LEAN_SYSROOT': str(sysroot), 'GOMAXPROCS': '1'}
        records = []
        require(time.monotonic() < setup_deadline, 'initial setup deadline')
        extract_stop = min(deadline - 30, time.monotonic() + 60)
        argv = [str(extractor), '-test.v', '-test.count=1', '-test.timeout=10s',
                '-test.run=^TestBoundedReaderControl']
        stdout, stderr, record = host.run_lean(argv, env, work, 'controls',
                                             min(extract_stop, time.monotonic() + 15), 256 * 1024)
        controls = test_output(stdout, stderr, contract['control_roots'])
        records.append(record)
        argv = [str(extractor), '-test.v', '-test.count=1', '-test.timeout=45s',
                '-test.run=^TestBoundedReaderExtractionEmit$', '-reader-source-root=' + str(REPO),
                '-reader-fixture=' + str(REPO / contract['fixture']), '-reader-output=' + str(work / 'extracted')]
        stdout, stderr, record = host.run_lean(argv, env, work, 'extract', extract_stop, 256 * 1024)
        emit = test_output(stdout, stderr, ['TestBoundedReaderExtractionEmit'])
        records.append(record)
        extracted_leaves, extracted_identity = load_extraction(work, contract, extract_stop)
        expected_objects = {}
        for phase, module in zip(('reader', 'extracted', 'refinement'), MODULES):
            stop = host.phase_deadline(deadline, 120, time.monotonic())
            host.inspect_objects(objects, expected_objects, stop)
            source = REPO / 'spec/lean/Oak/Stdlib' / (module + '.lean')
            verify_file(source, contract['inputs'][str(source.relative_to(REPO))], stop)
            target = objects / 'Oak/Stdlib' / (module + '.olean')
            argv = [str(lean), *host.FLAGS, '--root=' + str(REPO / 'spec/lean'), '-o', str(target), str(source)]
            stdout, stderr, record = host.run_lean(argv, env, work, phase, stop, 512 * 1024)
            diagnostics(stdout, stderr, phase, stop, HERE / 'RefinementAuditDriver.lean', contract)
            expected_objects[target.name] = host.object_identity(target)
            host.inspect_objects(objects, expected_objects, stop)
            records.append(record)
        driver = HERE / 'RefinementAuditDriver.lean'
        argv = [str(lean), *host.FLAGS, '--root=' + str(HERE), str(driver)]
        stop = host.phase_deadline(deadline, 120, time.monotonic())
        host.inspect_objects(objects, expected_objects, stop)
        verify_file(driver, contract['inputs'][str(driver.relative_to(REPO))], stop)
        stdout, stderr, record = host.run_lean(argv, env, work, 'audit', stop, 12 * 1024**2)
        summary = diagnostics(stdout, stderr, 'audit', stop, driver, contract)
        records.append(record)
        require(summary['candidate_declarations'] == 753 and summary['actual_imports'] == 1050,
                'exact accepted declaration/import inventory')
        final_deadline = min(deadline, time.monotonic() + 30)
        host.inspect_objects(objects, expected_objects, final_deadline)
        for relative, expected in contract['inputs'].items():
            verify_file(REPO / relative, expected, final_deadline)
        require(load_contract() == contract, 'stable source contract')
        require(members(harness, 4) == {'adapter.go', 'adapter_test.go', 'emit_test.go', 'fixture'},
                'stable named-file build membership')
        observed = verify_file(extractor, {k: binary_pin[k] for k in ('bytes', 'sha256')}, final_deadline)
        require(observed['snapshot'] == binary_pin['snapshot'], 'stable extraction binary')
        require(load_extraction(work, contract, final_deadline)[1] == extracted_identity, 'stable extraction outputs')
        host.verify_distribution(sysroot, distribution['files'], final_deadline)
        expected_names = {'objects', 'home', 'tmp', 'extracted'} | {
            phase + suffix for phase in PHASES for suffix in ('-stdout.log', '-stderr.log', '-execution.json')}
        require(members(work, 24) == expected_names and not members(work / 'home', 1) and
                not members(work / 'tmp', 1), 'exact fresh profile membership')
        host.physical_guards(work)
        result.update(accepted=True, generated_definition_refinement=True, checkout_commit=args.checkout_commit,
                      audit=summary, objects=expected_objects, direct_processes=records, controls=controls, emit=emit,
                      extraction=extracted_identity, extractor=binary_pin, source_contract_sha256=CONTRACT_SHA256,
                      historical_extraction_tree=contract['historical_extraction_tree'],
                      host_tcb='trusted current GitHub checkout/build, Ubuntu/Python/system loader; pinned official Lean imports',
                      limits_scope='hard direct-process AS/FSIZE/core; sampled host/direct-RSS/storage; no escaped-descendant claim',
                      whole_seconds=time.monotonic() - started)
        leaves = {'audit-stdout.log': stdout, 'audit-stderr.log': stderr,
                  **{'extracted/' + n: d for n, d in extracted_leaves.items()}}
        host.write_new(work / 'object-hashes.json', retention_manifest(result, leaves, contract))
    except BaseException as exc:
        result['accepted'] = False
        result['error'] = (type(exc).__name__ + ': ' + str(exc))[:2048]
        raise
    finally:
        host.write_new(work / 'result.json', host.retained_json(result))
        if result['accepted']:
            require(members(work, 24) == expected_names | {'result.json', 'object-hashes.json'}, 'final exact membership')
            host.physical_guards(work)
            require(time.monotonic() < final_deadline, 'final original deadline')
        print(json.dumps({'accepted': result['accepted'], 'result': str(work / 'result.json')}), flush=True)


if __name__ == '__main__':
    main()
