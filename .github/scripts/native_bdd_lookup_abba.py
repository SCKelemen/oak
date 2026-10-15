#!/usr/bin/env python3
"""One finite, experimental race-instrumented BDD lookup comparison.

The checked-out production tree is read only. Two private source snapshots differ
only by the frozen two-byte lookup transformation. This diagnostic gives no proof,
required-native acceptance, performance guarantee, or non-race speedup claim.
"""
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import platform
import re
import signal
import stat
import sys
import time
import unittest

import native_scalar_text_profile as base
from native_arm64 import pattern, validate_events

MiB, GiB = 1024**2, 1024**3
INPUT = '.github/scripts/native_bdd_lookup_abba_inputs.json'
BASE_TREE = '706574c8f69fefb43e60d0cab4004a3b1fa45103'
# The immediate production parent is a complete reviewed tree. Only this
# diagnostic script and its self-excluded input contract differ from it.
INTEGRATION_PATHS = {INPUT, '.github/scripts/native_bdd_lookup_abba.py'}
JOB_SECONDS, SETUP_SECONDS, BUILD_SECONDS = 1800, 420, 900
CONTROL_SECONDS, BENCH_SECONDS, FINAL_SECONDS, UPLOAD_SECONDS = 120, 120, 240, 60
BINARY_LIMIT, EVIDENCE_LIMIT, ARTIFACT_LIMIT = 128*MiB, 32*MiB, 288*MiB
WORK_LIMIT, RESERVE = 4*GiB, 2*GiB
FILE_LIMIT, RECORD_LIMIT, COMMAND_LIMIT = 64*MiB, 8*MiB, 64
OLD = b'\t\te := &t.entries[i]\n'
NEW = b'\t\te := t.entries[i]\n'
EXPECTED_CPU = 4
STEM = 'native-bdd-lookup-abba'
PACKAGE = 'github.com/SCKelemen/oak/asm'
ORDER = ('A', 'B', 'B', 'A')
LEAVES = ('BenchmarkBDDAdd32', 'BenchmarkBDDAdd64', 'BenchmarkBDDOperationMemo/bounded')
BENCHMARKS = (
    ('adds', '^(BenchmarkBDDAdd32|BenchmarkBDDAdd64)$', LEAVES[:2]),
    ('memo', '^BenchmarkBDDOperationMemo$/^bounded$', LEAVES[2:]),
)
CONTROLS = {
    'TestBDDTableGrowthPreservesTriples': [],
    'TestBDDTableGrowthStaysWithinAdmissionEnvelope': [],
    'TestBDDTableGrowthUsesReducedImplicationBudget': [],
    'TestBDDMemoBoundAndCancellation': [],
    'TestBDDBoundedMemoRecomputesCanonicalResults': [],
    'TestBDDRehashCancellationPreservesTables': ['unique', 'memo'],
    'TestBDDStoppedFastPaths': ['unique_hit', 'redundant_node', 'binary_terminal',
        'binary_memo', 'ite_terminal', 'ite_memo', 'restrict_terminal',
        'restrict_unchanged', 'restrict_recursive', 'satisfying_path', 'assignment_evaluation'],
    'TestBDDStoppedExistingNodesDoNotGrowMemo': [],
    'TestBDDBinarySemantics': [],
    'TestBDDITESemantics': [],
    'TestBDDITEBudget': [],
    'TestBDDExhaustionDoesNotMemoizePartialResults': ['binary', 'ite'],
    'TestBDDOrderRaceJoinsCancelledWorkers': [],
    'TestBDDOrderRaceRejectsCancelledResult': [],
    'TestBDDParallelProofSemantics': ['equal', 'different'],
}
PREFIX_CAPS = {'source-A': 512*MiB, 'source-B': 512*MiB,
    'gomodcache': 512*MiB, 'gocache-A': 768*MiB, 'gocache-B': 768*MiB,
    'tmp': 512*MiB, 'bin-A': BINARY_LIMIT, 'bin-B': BINARY_LIMIT}
LOG_CAPS = {'setup.log': 2*MiB, 'build-A.log': 2*MiB, 'build-B.log': 2*MiB,
    'controls-A.jsonl': MiB, 'controls-B.jsonl': MiB,
    'disassembly-A.txt': 256*1024, 'disassembly-B.txt': 256*1024}
for _index in range(1, 9):
    LOG_CAPS[f'benchmark-{_index:02}.log'] = 256*1024
RECORD_NAMES = {'status.json', 'comparison.json', 'source-manifest.json',
                'inputs.json', 'baseline-bdd.go', 'candidate-bdd.go', 'manifest.json'}


PYTHON_CONTROL_METHODS = ('test_allocated_scan_includes_empty_directories', 'test_artifact_partition_refusals', 'test_benchmark_leaf_goldens', 'test_benchmark_refusals', 'test_binary_identity_binds_elf_and_bytes', 'test_build_identity_refusals', 'test_build_native_race_identity', 'test_compare_preserves_order_and_noise', 'test_compare_retains_parity_failures', 'test_complete_artifact_membership', 'test_expired_or_invalid_clock', 'test_git_rows_exact', 'test_git_rows_refuse_bad_members', 'test_git_tree_order_and_empty', 'test_json_refusals', 'test_measured_admission', 'test_original_deadlines', 'test_publish_closed_manifest', 'test_publish_post_fsync_deadline', 'test_semantic_absence_skip_duplicate_refused', 'test_semantic_inventory_exact', 'test_snapshot_inverse_and_source_preservation', 'test_snapshot_reverification_refuses_drift', 'test_source_relation_exact', 'test_source_relation_refuses_changes', 'test_transform_exact_inverse', 'test_transform_refuses_drift', 'test_work_components', 'test_work_monitor_uses_shared_accounting')
EXPECTED_SUBTESTS = 98


def require(ok, message):
    base.require(ok, message)


def deadline(started, phase, now):
    base.checked_number(started, 'original origin')
    base.checked_number(now, 'monotonic time')
    require(started <= now < started+JOB_SECONDS, 'expired original job clock')
    endpoints = {'setup': 420, 'build': 1320, 'controls': 1440,
                 'benchmarks': 1560, 'final': 1740}
    allowances = {'setup': 420, 'build': 900, 'controls': 120,
                  'benchmarks': 120, 'final': 180}
    stop = min(started+endpoints[phase], now+allowances[phase])
    require(stop-now > base.CLEANUP_SECONDS, 'phase has no cleanup allowance')
    return stop


def check_time(stop):
    require(time.monotonic() < stop, 'original phase deadline expired')


def decode_json(raw):
    def invalid(value):
        raise base.DiagnosticError('nonfinite JSON: '+value)
    return json.loads(raw, object_pairs_hook=base.unique_object, parse_constant=invalid)


def transform(raw, pins):
    require(hashlib.sha256(raw).hexdigest() == pins['baseline_sha256'],
            'baseline lookup source changed')
    require(raw.count(OLD) == 2 and NEW not in raw, 'lookup transform is not exact')
    changed = raw.replace(OLD, NEW)
    require(changed.replace(NEW, OLD) == raw and len(changed) == len(raw)-2,
            'lookup transform inverse differs')
    require(hashlib.sha256(changed).hexdigest() == pins['candidate_sha256'],
            'candidate lookup source differs')
    return changed


def git_rows(raw):
    require(raw.endswith(b'\0') and len(raw) <= 2*MiB, 'incomplete tree inventory')
    rows = {}
    for row in raw[:-1].split(b'\0'):
        info, name = row.split(b'\t', 1)
        mode, kind, oid = info.decode('ascii').split()
        path = name.decode('utf-8')
        require(mode in ('100644', '100755') and kind == 'blob'
                and re.fullmatch('[0-9a-f]{40}', oid) is not None,
                'unsupported tree member')
        require(path and len(name) <= 4096 and len(path.split('/')) <= 32
                and not path.startswith('/') and '\\' not in path
                and all(p not in ('', '.', '..') for p in path.split('/'))
                and path not in rows, 'invalid/duplicate source path')
        rows[path] = {'mode': mode, 'blob': oid}
    require(0 < len(rows) <= 32768, 'source member count differs')
    return rows


def git_blob(raw):
    return hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()


def tree_id(rows):
    root = {}
    for path, row in rows.items():
        directory = root
        parts = path.split('/')
        for part in parts[:-1]:
            require(not part in directory or isinstance(directory[part], dict),
                    'file/directory collision')
            directory = directory.setdefault(part, {})
        require(parts[-1] not in directory, 'tree collision')
        directory[parts[-1]] = (row['mode'], row['blob'])
    def descend(directory):
        body = bytearray()
        for name, value in sorted(directory.items(), key=lambda item:
                (item[0]+('/' if isinstance(item[1], dict) else '')).encode()):
            mode, oid = ('40000', descend(value)) if isinstance(value, dict) else value
            body.extend(mode.encode()+b' '+name.encode()+b'\0'+bytes.fromhex(oid))
        return hashlib.sha1(b'tree '+str(len(body)).encode()+b'\0'+body).hexdigest()
    return descend(root)


def validate_source_relation(rows, pins):
    baseline, additions = pins['baseline_tree_members'], pins['integration_members']
    require(tree_id(baseline) == pins['baseline_tree'] == BASE_TREE,
            'baseline inventory does not reconstruct the pinned production tree')
    require(set(additions) == INTEGRATION_PATHS, 'integration exception set changed')
    require(set(rows) == set(baseline) | set(additions), 'unexpected current source membership')
    for path, row in baseline.items():
        if path not in additions:
            require(rows[path] == row, 'production source changed: '+path)
    for path, expected in additions.items():
        if path == INPUT:
            require(rows[path]['mode'] == '100644', 'input contract mode changed')
        else:
            require(rows[path] == expected, 'integration source changed: '+path)
    require('asm/default.pgo' not in rows, 'unexpected automatic PGO profile')


def write_new(path, raw, mode=0o644):
    base.no_symlinks(path)
    require(not path.exists(), 'preexisting output: '+path.name)
    with path.open('xb') as output:
        require(output.write(raw) == len(raw), 'short output write')
        output.flush()
        os.fsync(output.fileno())
    path.chmod(mode)


def snapshots(repo, work, rows, pins, stop):
    records, variants, total = {}, {'A': dict(rows), 'B': dict(rows)}, 0
    for variant in ORDER[:2]:
        (work/('source-'+variant)).mkdir(mode=0o700)
    for name in sorted(rows):
        check_time(stop)
        path = repo/name
        raw = base.file_bytes(path, FILE_LIMIT)
        require(git_blob(raw) == rows[name]['blob'], 'physical source differs from Git: '+name)
        total += len(raw)
        require(total <= 512*MiB, 'source snapshot exceeds 512 MiB')
        changed = transform(raw, pins['lookup']) if name == 'asm/bdd.go' else raw
        records[name] = {'A': hashlib.sha256(raw).hexdigest(),
                         'B': hashlib.sha256(changed).hexdigest(),
                         'bytes_A': len(raw), 'bytes_B': len(changed), 'mode': rows[name]['mode']}
        variants['B'][name] = dict(rows[name], blob=git_blob(changed))
        for variant, content in (('A', raw), ('B', changed)):
            destination = work/('source-'+variant)/name
            destination.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
            write_new(destination, content, int(rows[name]['mode'], 8) & 0o777)
    require(tree_id(variants['A']) == tree_id(rows), 'baseline tree reconstruction differs')
    check_time(stop)
    return {'files': records, 'trees': {v: tree_id(r) for v, r in variants.items()},
            'baseline_logical_bytes': total, 'production_base_tree': pins['baseline_tree'],
            'baseline_is_current_integration_tree': True,
            'candidate_only_change': 'asm/bdd.go: two address operators removed'}


def verify_snapshots(work, records, stop):
    expected = records['files']
    for variant in ('A', 'B'):
        root = work/('source-'+variant)
        sizes = base.tree_sizes(root, max_files=32768, deadline=stop)
        require(set(sizes) == set(expected), 'source snapshot membership changed')
        for name, item in expected.items():
            check_time(stop)
            require(sizes[name] == item['bytes_'+variant]
                    and base.digest(root/name, FILE_LIMIT) == item[variant]
                    and stat.S_IMODE((root/name).lstat().st_mode) == int(item['mode'], 8) & 0o777,
                    'source snapshot changed: '+name)
    check_time(stop)


def artifact_sizes(sizes, complete=False):
    allowed = {'A/asm.test', 'B/asm.test'} | {'evidence/'+n for n in set(LOG_CAPS) | RECORD_NAMES}
    require(not set(sizes)-allowed, 'unexpected artifact member')
    require(all(sizes.get(v+'/asm.test', 0) <= BINARY_LIMIT for v in ('A', 'B')),
            'retained binary exceeds 128 MiB')
    evidence = {n.removeprefix('evidence/'): size for n, size in sizes.items()
                if n.startswith('evidence/')}
    require(sum(evidence.values()) <= EVIDENCE_LIMIT, 'evidence exceeds 32 MiB')
    require(sum(sizes.values()) <= ARTIFACT_LIMIT, 'artifact exceeds 288 MiB')
    for name, cap in LOG_CAPS.items():
        require(evidence.get(name, 0) <= cap, 'individual log cap exceeded')
    require(sum(evidence.get(n, 0) for n in RECORD_NAMES) <= RECORD_LIMIT,
            'source/status/comparison records exceed 8 MiB')
    if complete:
        empty_ok = {'evidence/disassembly-A.txt', 'evidence/disassembly-B.txt'}
        require(set(sizes) == allowed and all(size > 0 or name in empty_ok
                                             for name, size in sizes.items()),
                'complete artifact membership missing/empty')


def work_sizes(sizes):
    totals = {name: 0 for name in PREFIX_CAPS}
    for name, size in sizes.items():
        prefix = name.split('/', 1)[0]
        require(prefix in totals, 'unexpected work component')
        totals[prefix] += size
    require(sum(sizes.values()) <= WORK_LIMIT, 'work exceeds 4 GiB')
    require(all(totals[k] <= cap for k, cap in PREFIX_CAPS.items()),
            'work component exceeds its cap')
    return totals


def allocated_work(root, stop):
    """Include empty directories and the root in the sampled allocated total."""
    _, sample = base.work_tree_sizes(root, deadline=stop, allocated_limit=WORK_LIMIT)
    return sample['allocated_bytes']


class Monitor:
    """Sampled refusal guards; no hard memory/disk isolation claim."""
    def __init__(self, work, artifact, stop):
        self.work, self.artifact, self.deadline = work, artifact, stop
        self.next_sample = self.next_scan = 0
        self.samples = self.max_rss = self.max_work = self.max_allocated = 0
        self.last = None
        self.last_work_scan = None

    def __call__(self, now):
        if now < self.next_sample:
            return
        check_time(self.deadline)
        self.next_sample = now+1
        snap = base.resource_snapshot(os.getpid(), self.work, self.deadline)
        require(snap.get('process_scan') == 'complete'
                and snap.get('process_observation') == 'strict_sample_non_atomic',
                'incomplete process observation')
        rss = base.checked_number(snap.get('tree_rss_sum_bytes'), 'RSS')
        require(rss <= base.RSS_LIMIT and base.memory_available(snap) >= RESERVE,
                'sampled memory envelope exceeded')
        require(base.checked_number(snap.get('disk_available_bytes'), 'disk') >= RESERVE,
                'sampled disk reserve exhausted')
        self.samples += 1
        self.max_rss = max(self.max_rss, rss)
        self.last = snap
        artifact_sizes(base.tree_sizes(self.artifact, max_files=128,
            deadline=self.deadline, allowed_dirs={'A', 'B', 'evidence'}))
        if now >= self.next_scan:
            self.next_scan = now+5
            sizes, self.last_work_scan = base.work_tree_sizes(
                self.work, deadline=self.deadline, allocated_limit=WORK_LIMIT)
            work_sizes(sizes)
            allocated = self.last_work_scan['allocated_bytes']
            self.max_work = max(self.max_work, sum(sizes.values()))
            self.max_allocated = max(self.max_allocated, allocated)
        check_time(self.deadline)

    def record(self):
        return dict(samples=self.samples, max_observed_tree_rss_bytes=self.max_rss,
                    max_observed_work_logical_bytes=self.max_work,
                    max_observed_work_allocated_bytes=self.max_allocated,
                    last_work_scan=self.last_work_scan,
                    last=self.last, sample_seconds=1, work_scan_seconds=5,
                    hard_isolation=False, non_atomic=True)


def admit(snapshot):
    require(base.memory_available(snapshot) >= base.RSS_LIMIT+RESERVE,
            'insufficient measured memory for 8 GiB plus 2 GiB reserve')
    require(base.checked_number(snapshot.get('disk_available_bytes'), 'free disk')
            >= WORK_LIMIT+2*ARTIFACT_LIMIT+RESERVE, 'insufficient measured disk admission')
    require(snapshot.get('process_scan') == 'complete'
            and snapshot.get('process_observation') == 'strict_sample_non_atomic'
            and base.checked_number(snapshot.get('tree_rss_sum_bytes'), 'initial RSS') <= base.RSS_LIMIT,
            'invalid initial owned process observation')


def binary_identity(path):
    before = path.lstat()
    raw = base.file_bytes(path, BINARY_LIMIT)
    after = path.lstat()
    fields = ('st_dev', 'st_ino', 'st_mode', 'st_size', 'st_mtime_ns', 'st_ctime_ns', 'st_nlink')
    require(tuple(getattr(before, f) for f in fields) == tuple(getattr(after, f) for f in fields),
            'binary identity changed during read')
    require(raw[:6] == b'\x7fELF\x02\x01' and int.from_bytes(raw[18:20], 'little') == 183,
            'binary is not native little-endian ELF64 ARM64')
    return {'sha256': hashlib.sha256(raw).hexdigest(), 'bytes': len(raw),
            'physical': {f: getattr(before, f) for f in fields}}


def validate_build(info, pins):
    expected = pins['go_build']
    require(info.get('Path') == PACKAGE+'.test', 'wrong asm test binary path')
    base.validate_go_build(info, expected, '')
    settings = {row['Key']: row.get('Value', '') for row in info['Settings']}
    require(settings == expected['settings'], 'unexpected build setting or VCS metadata')


def parse_benchmarks(raw, leaves):
    require(raw.endswith(b'\n') and len(raw) <= 256*1024, 'incomplete benchmark log')
    rows, passed = [], False
    for line in raw.decode('utf-8').splitlines():
        if not line or line.startswith(('goos: ', 'goarch: ', 'pkg: ', 'cpu: ')):
            continue
        if line == 'PASS':
            require(not passed, 'duplicate benchmark PASS')
            passed = True
            continue
        require(not passed, 'benchmark output after PASS')
        fields = line.split()
        match = re.fullmatch(r'(.+)-([1-9][0-9]*)', fields[0]) if fields else None
        require(match is not None and int(match[2]) == EXPECTED_CPU,
                'benchmark identity/CPU shape differs')
        name = match[1]
        require(name in leaves and len(fields) >= 4 and fields[1] == '1'
                and len(fields[2:]) % 2 == 0, 'benchmark selection/count differs')
        metrics = {}
        for value, unit in zip(fields[2::2], fields[3::2]):
            require(unit not in metrics, 'duplicate benchmark metric')
            number = float(value)
            require(math.isfinite(number) and number >= 0, 'invalid benchmark metric')
            metrics[unit] = number
        expected = {'ns/op', 'B/op', 'allocs/op', 'nodes'}
        expected |= {'nodes/s'} if name in LEAVES[:2] else {'memo_bytes', 'evictions'}
        require(set(metrics) == expected and metrics['ns/op'] > 0 and metrics['nodes'] > 0,
                'missing/extra benchmark metrics')
        require(all(metrics[k].is_integer() for k in expected-{'ns/op', 'nodes/s'}),
                'noninteger count/allocation metric')
        rows.append({'name': name, 'iterations': 1, 'gomaxprocs': EXPECTED_CPU, 'metrics': metrics})
    require(passed and [r['name'] for r in rows] == list(leaves),
            'missing/duplicate/reordered benchmark leaves')
    return rows


def compare(screens):
    require(len(screens) == 4 and [x['variant'] for x in screens] == list(ORDER),
            'ABBA screen order differs')
    for screen in screens:
        require([r['name'] for r in screen['rows']] == list(LEAVES), 'screen leaves differ')
    result = []
    invariant_parity = allocation_parity = True
    for i, name in enumerate(LEAVES):
        metrics = [s['rows'][i]['metrics'] for s in screens]
        invariants = set(metrics[0])-{'ns/op', 'nodes/s', 'B/op', 'allocs/op'}
        semantic = all(all(m[k] == metrics[0][k] for k in invariants) for m in metrics)
        allocation = all(all(m[k] == metrics[0][k] for k in ('B/op', 'allocs/op')) for m in metrics)
        invariant_parity &= semantic
        allocation_parity &= allocation
        pairs = []
        for label, a, b in (('AB', 0, 1), ('BA', 3, 2)):
            av, bv = metrics[a]['ns/op'], metrics[b]['ns/op']
            pairs.append({'order': label, 'A_ns': av, 'B_ns': bv,
                          'B_minus_A_ns': bv-av, 'B_over_A': bv/av})
        av = [metrics[j]['ns/op'] for j in (0, 3)]
        bv = [metrics[j]['ns/op'] for j in (1, 2)]
        result.append({'name': name, 'pairs': pairs, 'invariant_parity': semantic,
            'allocation_parity': allocation, 'A_range_ns': [min(av), max(av)],
            'B_range_ns': [min(bv), max(bv)],
            'ranges_overlap': max(min(av), min(bv)) <= min(max(av), max(bv)),
            'candidate_faster_in_both_pairs': all(p['B_minus_A_ns'] < 0 for p in pairs),
            'raw_metrics_in_ABBA_order': metrics})
    return {'schema_version': 1, 'scope': 'coarse race-instrumented micro screen',
            'pairs': 2, 'screens': 4, 'benchmark_children': 8, 'leaf_workloads': 12,
            'invariant_parity': invariant_parity, 'allocation_parity': allocation_parity,
            'optimization_accepted': False, 'results': result,
            'limits': 'Two pairs do not establish equivalence, no regression, end-to-end benefit or non-race benefit.'}


def publish(artifact, status, stop, complete):
    check_time(stop)
    base.write_json(artifact/'evidence/status.json', status, MiB)
    sizes = base.tree_sizes(artifact, max_files=128, deadline=stop,
                            allowed_dirs={'A', 'B', 'evidence'})
    artifact_sizes(sizes)
    members = []
    for name in sorted(sizes):
        if name == 'evidence/manifest.json':
            continue
        check_time(stop)
        members.append({'path': name, 'bytes': sizes[name],
                        'sha256': base.digest(artifact/name, BINARY_LIMIT)})
    base.write_json(artifact/'evidence/manifest.json',
                    {'schema_version': 1, 'members': members, 'complete_pending_outer_exit': complete,
                     'requires_successful_exact_workflow_step': True, 'retention_days': 14}, MiB)
    artifact_sizes(base.tree_sizes(artifact, max_files=128, deadline=stop,
        allowed_dirs={'A', 'B', 'evidence'}), complete=complete)
    check_time(stop)


def run(repo, started):
    temp = base.no_symlinks(Path(os.environ['RUNNER_TEMP']))
    work, artifact = temp/(STEM+'-work'), temp/(STEM+'-artifact')
    require(not work.exists() and not artifact.exists(), 'experiment paths must be fresh')
    work.mkdir(mode=0o700)
    artifact.mkdir(mode=0o700)
    for name in ('A', 'B', 'evidence'):
        (artifact/name).mkdir(mode=0o700)
    evidence = artifact/'evidence'
    status = {'schema_version': 1, 'diagnostic_complete': False, 'error': '',
              'original_started_monotonic': started, 'commands': [], 'screens': [],
              'production_optimization_accepted': False, 'binary_identities': {}}
    sinks, monitor = {}, None
    final_end = None
    def sink(name):
        if name not in sinks:
            sinks[name] = base.CappedOutput(evidence/name, LOG_CAPS[name])
        return sinks[name]
    try:
        setup = deadline(started, 'setup', time.monotonic())
        require(platform.system() == 'Linux' and platform.machine() in ('arm64', 'aarch64')
                and os.cpu_count() == EXPECTED_CPU and len(os.sched_getaffinity(0)) == EXPECTED_CPU,
                'experiment requires the reviewed four-CPU native ARM64 shape')
        pins_raw = base.file_bytes(repo/INPUT, 2*MiB)
        pins = decode_json(pins_raw)
        require(pins['schema_version'] == 1, 'unknown input contract')
        for path, expected in pins['helpers'].items():
            check_time(setup)
            require(base.digest(repo/path, FILE_LIMIT) == expected, 'helper version changed: '+path)
        for name in PREFIX_CAPS:
            if not name.startswith('source-'):
                (work/name).mkdir(mode=0o700)
        env = base.clean_environment(dict(os.environ), work)
        env['GOCACHE'] = str(work/'gocache-A')
        admission = base.resource_snapshot(os.getpid(), work, setup)
        admit(admission)
        status['admission'] = admission
        monitor = Monitor(work, artifact, setup)
        def command(argv, cap=0, stop=None, log='setup.log', cwd=None, run_env=None):
            require(len(status['commands']) < COMMAND_LIMIT, 'command inventory cap exceeded')
            end = setup if stop is None else stop
            monitor.deadline = end
            output = base.bounded_command(argv, sink(log), end, env if run_env is None else run_env,
                repo if cwd is None else cwd, monitor=monitor, capture_limit=cap,
                evidence=status['commands'])
            check_time(end)
            return output
        tools = {name: base.tool_identity(name, command, env, setup)
                 for name in ('go', 'cc', 'c++', 'clang')}
        env = base.bind_tool_environment(env, tools)
        go = tools['go']['path']
        require(tools['go']['version'].strip() == 'go version go1.27.1 linux/arm64',
                'wrong Go toolchain')
        observed = decode_json(command([go, 'env', '-json', 'GOHOSTARCH', 'GOARCH', 'GOHOSTOS',
            'GOOS', 'CGO_ENABLED', 'GOENV', 'CC', 'CXX'], 4096))
        base.validate_tool_environment(observed, env)
        status['tools'] = tools
        status['toolchain_trust'] = 'official setup-go distribution plus hosted Ubuntu loader/C tools'
        command([sys.executable, str(repo/'.github/scripts/native_scalar_text_profile.py'), '--controls'],
                stop=min(setup, time.monotonic()+60))
        command([sys.executable, str(repo/'.github/scripts/native_bdd_lookup_abba.py'), '--controls'],
                stop=min(setup, time.monotonic()+60))
        identity = base.source_identity(repo, command, env, setup)
        rows = git_rows(command(['git', 'ls-tree', '-r', '-z', 'HEAD'], 2*MiB))
        require(tree_id(rows) == identity['source_tree'], 'current tree reconstruction mismatch')
        validate_source_relation(rows, pins)
        records = snapshots(repo, work, rows, pins, setup)
        require(records['files'][INPUT]['A'] == hashlib.sha256(pins_raw).hexdigest(),
                'the parsed input contract differs from the authenticated source snapshot')
        status['checkout'] = identity
        status['experimental_trees'] = records['trees']
        base.write_json(evidence/'source-manifest.json', records, 4*MiB)
        write_new(evidence/'inputs.json', pins_raw)
        for v, name in (('A', 'baseline-bdd.go'), ('B', 'candidate-bdd.go')):
            write_new(evidence/name, base.file_bytes(work/('source-'+v)/'asm/bdd.go', FILE_LIMIT))
        command([go, 'mod', 'download'], cwd=work/'source-A')
        command([go, 'mod', 'verify'], cwd=work/'source-A')
        verify_snapshots(work, records, setup)
        build_stop = deadline(started, 'build', time.monotonic())
        binaries, envs = {}, {}
        for variant in ('A', 'B'):
            stop = min(build_stop, time.monotonic()+450)
            require(stop-time.monotonic() > base.CLEANUP_SECONDS, 'build allowance exhausted')
            current_env = dict(env, GOCACHE=str(work/('gocache-'+variant)))
            binary = work/('bin-'+variant)/'asm.test'
            command([go, 'test', '-c', '-race', '-mod=readonly', '-o', str(binary), './asm'],
                stop=stop, log='build-'+variant+'.log', cwd=work/('source-'+variant), run_env=current_env)
            build = decode_json(command([go, 'version', '-m', '-json', str(binary)], 65536,
                                        stop=stop, log='build-'+variant+'.log'))
            validate_build(build, pins)
            build_id = command([go, 'tool', 'buildid', str(binary)], 4096,
                                stop=stop, log='build-'+variant+'.log').decode().strip()
            require(build_id and len(build_id) <= 256, 'missing/invalid binary build ID')
            info = binary_identity(binary)
            status['binary_identities'][variant] = dict(info, build_id=build_id,
                build_info=build, source_tree=records['trees'][variant])
            write_new(artifact/variant/'asm.test', base.file_bytes(binary, BINARY_LIMIT), 0o755)
            binaries[variant], envs[variant] = binary, current_env
            check_time(stop)
        control_stop = deadline(started, 'controls', time.monotonic())
        for variant in ('A', 'B'):
            raw = command([go, 'tool', 'test2json', '-t', '-p', PACKAGE, '--', str(binaries[variant]),
                '-test.v=test2json', '-test.count=1', '-test.timeout=55s',
                '-test.run='+pattern(sorted(CONTROLS))], MiB,
                stop=min(control_stop, time.monotonic()+60), log='controls-'+variant+'.jsonl',
                cwd=work/('source-'+variant), run_env=envs[variant])
            require(raw.endswith(b'\n'), 'incomplete semantic control stream')
            validate_events([decode_json(row) for row in raw.splitlines()], './asm',
                            sorted(CONTROLS), CONTROLS)
            status.setdefault('semantic_controls', {})[variant] = {'roots': 15, 'children': 17,
                                                                    'skips': 0}
        regex = r'github\.com/SCKelemen/oak/asm\.\(\*(uniqueTable|opTable)\)\.lookup'
        for variant in ('A', 'B'):
            raw = command([go, 'tool', 'objdump', '-s', regex, str(binaries[variant])], 256*1024,
                stop=control_stop, log='disassembly-'+variant+'.txt')
            text = raw.decode('utf-8')
            status.setdefault('standalone_lookup_symbols', {})[variant] = {
                name: name in text for name in ('(*uniqueTable).lookup', '(*opTable).lookup')}
        check_time(control_stop)
        bench_stop = deadline(started, 'benchmarks', time.monotonic())
        ordinal = 0
        for screen_index, variant in enumerate(ORDER):
            screen = {'screen': screen_index+1, 'variant': variant, 'rows': []}
            for _, selector, leaves in BENCHMARKS:
                ordinal += 1
                raw = command([str(binaries[variant]), '-test.run=^$', '-test.bench='+selector,
                    '-test.benchtime=1x', '-test.count=1', '-test.benchmem', '-test.timeout=30s'],
                    256*1024, stop=min(bench_stop, time.monotonic()+33),
                    log=f'benchmark-{ordinal:02}.log', cwd=work/('source-'+variant), run_env=envs[variant])
                screen['rows'].extend(parse_benchmarks(raw, leaves))
                check_time(bench_stop)
            status['screens'].append(screen)
        comparison = compare(status['screens'])
        base.write_json(evidence/'comparison.json', comparison, MiB)
        require(comparison['invariant_parity'] and comparison['allocation_parity'],
                'semantic node/memo/eviction/allocation parity differs; no comparable timing claim')
        check_time(bench_stop)
        final_end = deadline(started, 'final', time.monotonic())
        monitor.deadline = final_end
        verify_snapshots(work, records, final_end)
        current = base.source_identity(repo, lambda a, c: command(a, c, stop=final_end), env, final_end)
        require(current == identity, 'production checkout changed')
        for variant, binary in binaries.items():
            check_time(final_end)
            require(binary_identity(binary) == {k: status['binary_identities'][variant][k]
                for k in ('sha256', 'bytes', 'physical')}, 'executed binary changed')
            require(base.digest(artifact/variant/'asm.test', BINARY_LIMIT)
                    == status['binary_identities'][variant]['sha256'], 'retained binary changed')
        for tool in tools.values():
            check_time(final_end)
            require(base.digest(Path(tool['path']), 256*MiB, private=False) == tool['sha256'],
                    'authenticated tool changed')
        monitor(time.monotonic())
        status['diagnostic_complete'] = True
    except (Exception, KeyboardInterrupt) as error:
        status['error'] = f'{type(error).__name__}: {error}'[:4096]
    finally:
        if final_end is None:
            final_end = min(started+JOB_SECONDS-UPLOAD_SECONDS, time.monotonic()+180)
        for output in sinks.values():
            try:
                output.close()
            except (Exception, KeyboardInterrupt) as error:
                status['diagnostic_complete'] = False
                status['error'] = f'log close failed: {error}'[:4096]
        status['logs'] = {n: {'bytes': s.count, 'overflow': s.overflow} for n, s in sinks.items()}
        status['resources'] = None if monitor is None else monitor.record()
        status['elapsed_seconds'] = time.monotonic()-started
        if time.monotonic() >= final_end or any(s.overflow for s in sinks.values()):
            status['diagnostic_complete'] = False
            status['error'] = 'original final deadline or output cap exhausted'
        try:
            publish(artifact, status, final_end, status['diagnostic_complete'])
            check_time(final_end)
        except (Exception, KeyboardInterrupt) as error:
            status['diagnostic_complete'] = False
            status['error'] = f'final publication failed: {error}'[:4096]
            (evidence/'manifest.json').unlink(missing_ok=True)
            # Best effort failure record only; it can never authorize acceptance.
            if time.monotonic() < final_end:
                base.write_json(evidence/'status.json', status, MiB)
    return 0 if status['diagnostic_complete'] else 1


def run_controls():
    path = Path(__file__).with_name('test_native_bdd_lookup_abba.py')
    spec = importlib.util.spec_from_file_location('bdd_lookup_controls', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    suite = unittest.defaultTestLoader.loadTestsFromModule(module)
    def identities(group):
        for item in group:
            if isinstance(item, unittest.TestSuite):
                yield from identities(item)
            else:
                yield item.id().rsplit('.', 1)[-1]
    require(tuple(sorted(identities(suite))) == PYTHON_CONTROL_METHODS,
            'Python control method inventory differs')
    class CountedResult(unittest.TextTestResult):
        contexts = 0
        def addSubTest(self, test, subtest, error):
            self.contexts += 1
            super().addSubTest(test, subtest, error)
    result = unittest.TextTestRunner(verbosity=2, resultclass=CountedResult).run(suite)
    require(result.testsRun == len(PYTHON_CONTROL_METHODS) == module.EXPECTED_METHODS
            and result.contexts == EXPECTED_SUBTESTS and not result.skipped,
            'Python control method/context/skip inventory differs')
    print(f'BDD lookup controls: {result.testsRun} methods, {result.contexts} subtest contexts')
    return 0 if result.wasSuccessful() else 1


def main():
    if sys.argv[1:] == ['--controls']:
        return run_controls()
    require(sys.argv[1:] == ['--run'], 'expected --run or --controls')
    def cancelled(signum, _frame):
        raise base.DiagnosticError('cancelled: '+str(signum))
    for sig in (signal.SIGTERM, signal.SIGINT):
        signal.signal(sig, cancelled)
    started = float(os.environ['BDD_LOOKUP_JOB_STARTED'])
    return run(Path(__file__).resolve().parents[2], started)


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (Exception, KeyboardInterrupt) as error:
        print(f'BDD lookup diagnostic refused: {error}', file=sys.stderr)
        raise SystemExit(1)
