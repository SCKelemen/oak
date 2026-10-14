"""Finite synthetic controls. No Go, subprocess, profile or real cache access."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import native_bdd_lookup_abba as target

EXPECTED_METHODS = 28


def sample_snapshot():
    return {'mem_available_bytes': 12*target.GiB,
            'cgroup_scope': 'visible_v2_hierarchy', 'cgroup_headroom_bytes': 12*target.GiB,
            'disk_available_bytes': 8*target.GiB, 'tree_rss_sum_bytes': 0,
            'process_scan': 'complete', 'process_observation': 'strict_sample_non_atomic'}


def lookup_fixture():
    raw = b'first\n'+target.OLD+b'second\n'+target.OLD
    changed = raw.replace(target.OLD, target.NEW)
    return raw, {'baseline_sha256': hashlib.sha256(raw).hexdigest(),
                 'candidate_sha256': hashlib.sha256(changed).hexdigest()}


def benchmark_log(names, value=100):
    rows = ['goos: linux', 'goarch: arm64', 'pkg: '+target.PACKAGE, 'cpu: fixture']
    for name in names:
        fields = f'{name}-4 1 {value} ns/op 200 nodes '
        fields += '2000000000 nodes/s ' if name in target.LEAVES[:2] else '1048576 memo_bytes 3 evictions '
        rows.append(fields+'4096 B/op 2 allocs/op')
    return ('\n'.join(rows)+'\nPASS\n').encode()


def screens():
    return [{'variant': v, 'rows': target.parse_benchmarks(benchmark_log(target.LEAVES, n),
                                                       target.LEAVES)}
            for v, n in zip(target.ORDER, (100, 90, 95, 110))]


def events():
    stream = [{'Action': 'start', 'Package': target.PACKAGE}]
    for root, children in sorted(target.CONTROLS.items()):
        stream.append({'Action': 'run', 'Package': target.PACKAGE, 'Test': root})
        for child in children:
            for action in ('run', 'pass'):
                stream.append({'Action': action, 'Package': target.PACKAGE, 'Test': root+'/'+child})
        stream.append({'Action': 'pass', 'Package': target.PACKAGE, 'Test': root})
    stream.append({'Action': 'pass', 'Package': target.PACKAGE})
    return stream


def build_fixture():
    expected = {'version': 'go1.27.1',
                'main': {'Path': 'github.com/SCKelemen/oak', 'Version': '(devel)'},
                'dependencies': [{'Path': 'github.com/SCKelemen/unicode', 'Version': 'v1.1.1',
                                  'Sum': 'h1:zfDNToPzJcuX8ayJhRipZZd09f+dJO/T4IvIk90d13k='}],
                'settings': {'-buildmode': 'exe', '-compiler': 'gc', '-race': 'true',
                    'CGO_ENABLED': '1', 'CGO_CFLAGS': '', 'CGO_CPPFLAGS': '', 'CGO_CXXFLAGS': '',
                    'CGO_LDFLAGS': '', 'GOARCH': 'arm64', 'GOOS': 'linux', 'GOARM64': 'v8.0'}}
    info = {'GoVersion': expected['version'], 'Path': target.PACKAGE+'.test',
            'Main': copy.deepcopy(expected['main']), 'Deps': copy.deepcopy(expected['dependencies']),
            'Settings': [{'Key': k, 'Value': v} for k, v in expected['settings'].items()]}
    return info, {'go_build': expected}


class BDDLookupControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.process_guard = mock.patch('subprocess.Popen', side_effect=AssertionError('subprocess forbidden'))
        cls.process_guard.start()

    @classmethod
    def tearDownClass(cls):
        cls.process_guard.stop()

    def test_original_deadlines(self):
        for phase, stop in [('setup', 420), ('build', 900), ('controls', 120),
                            ('benchmarks', 120), ('final', 180)]:
            with self.subTest(phase=phase):
                self.assertEqual(target.deadline(0, phase, 0), stop)
        self.assertEqual(target.deadline(0, 'benchmarks', 1500), 1560)
        self.assertEqual(target.deadline(0, 'final', 1700), 1740)

    def test_expired_or_invalid_clock(self):
        for origin, now in [(0, 1800), (10, 9), (0, float('nan')), (-1, 0)]:
            with self.subTest(origin=origin, now=now), self.assertRaises(ValueError):
                target.deadline(origin, 'setup', now)
        for phase, now in [('setup', 418), ('build', 1318), ('controls', 1438),
                           ('benchmarks', 1558), ('final', 1738)]:
            with self.subTest(phase=phase), self.assertRaises(ValueError):
                target.deadline(0, phase, now)

    def test_transform_exact_inverse(self):
        raw, pins = lookup_fixture()
        actual = target.transform(raw, pins)
        self.assertEqual(len(actual), len(raw)-2)
        self.assertEqual(actual.replace(target.NEW, target.OLD), raw)

    def test_transform_refuses_drift(self):
        raw, pins = lookup_fixture()
        for changed in [raw+b'x', raw.replace(target.OLD, b'', 1), raw+target.OLD]:
            with self.subTest(raw=changed), self.assertRaises(ValueError):
                target.transform(changed, pins)
        for field in pins:
            with self.subTest(field=field), self.assertRaises(ValueError):
                target.transform(raw, dict(pins, **{field: '0'*64}))

    def test_git_rows_exact(self):
        blob = 'e69de29bb2d1d6434b8b29ae775ad8c2e48c5391'
        self.assertEqual(target.git_rows(('100644 blob '+blob+'\ta.go\0').encode()),
                         {'a.go': {'mode': '100644', 'blob': blob}})

    def test_git_rows_refuse_bad_members(self):
        oid = '0'*40
        for row in [f'120000 blob {oid}\tx\0', f'100644 tree {oid}\tx\0',
                    f'100644 blob {oid}\t../x\0', f'100644 blob {oid}\t/x\0',
                    f'100644 blob {oid}\tx', f'100644 blob nope\tx\0',
                    (f'100644 blob {oid}\tx\0')*2]:
            with self.subTest(row=row), self.assertRaises(ValueError):
                target.git_rows(row.encode())

    def test_git_tree_order_and_empty(self):
        self.assertEqual(target.tree_id({}), '4b825dc642cb6eb9a060e54bf8d69288fbee4904')
        rows = {p: {'mode': '100644', 'blob': target.git_blob(p.encode())} for p in ['b', 'a/x', 'a.y']}
        self.assertEqual(target.tree_id(rows), target.tree_id(dict(reversed(list(rows.items())))))

    def test_source_relation_exact(self):
        row = {'mode': '100644', 'blob': '0'*40}
        baseline = {'asm/bdd.go': row}
        pins = {'baseline_tree_members': baseline, 'baseline_tree': target.tree_id(baseline),
                'integration_members': {p: row for p in target.INTEGRATION_PATHS}}
        current = dict(baseline, **{p: row for p in target.INTEGRATION_PATHS})
        with mock.patch.object(target, 'BASE_TREE', pins['baseline_tree']):
            target.validate_source_relation(current, pins)

    def test_source_relation_refuses_changes(self):
        row = {'mode': '100644', 'blob': '0'*40}
        baseline = {'asm/bdd.go': row}
        pins = {'baseline_tree_members': baseline, 'baseline_tree': target.tree_id(baseline),
                'integration_members': {p: row for p in target.INTEGRATION_PATHS}}
        original = dict(baseline, **{p: row for p in target.INTEGRATION_PATHS})
        changes = [dict(original, extra=row), {target.INPUT: row},
                   dict(original, **{'asm/bdd.go': dict(row, blob='1'*40)}),
                   dict(original, **{target.INPUT: dict(row, mode='100755')})]
        with mock.patch.object(target, 'BASE_TREE', pins['baseline_tree']):
            for altered in changes:
                with self.subTest(rows=altered), self.assertRaises(ValueError):
                    target.validate_source_relation(altered, pins)
            for changed in [dict(pins, baseline_tree='0'*40),
                    dict(pins, baseline_tree_members={'asm/bdd.go': dict(row, blob='1'*40)}),
                    dict(pins, integration_members=dict(pins['integration_members'], **{'asm/bdd.go': row}))]:
                with self.subTest(pins=changed), self.assertRaises(ValueError):
                    target.validate_source_relation(original, changed)

    def test_artifact_partition_refusals(self):
        for sizes in [{'A/asm.test': target.BINARY_LIMIT+1}, {'B/asm.test': target.BINARY_LIMIT+1},
                      {'extra': 1}, {'evidence/setup.log': 2*target.MiB+1},
                      {'evidence/status.json': target.RECORD_LIMIT+1}]:
            with self.subTest(sizes=sizes), self.assertRaises(ValueError):
                target.artifact_sizes(sizes)
        target.artifact_sizes({'A/asm.test': target.BINARY_LIMIT, 'B/asm.test': target.BINARY_LIMIT})

    def test_complete_artifact_membership(self):
        names = {'A/asm.test', 'B/asm.test'} | {'evidence/'+n for n in set(target.LOG_CAPS)|target.RECORD_NAMES}
        sizes = dict.fromkeys(names, 1)
        target.artifact_sizes(sizes, complete=True)
        for name in ('evidence/disassembly-A.txt', 'evidence/disassembly-B.txt'):
            with self.subTest(name=name):
                target.artifact_sizes(dict(sizes, **{name: 0}), complete=True)
        for altered in [dict(sizes, **{'A/asm.test': 0}), {n: v for n, v in sizes.items() if n != 'A/asm.test'}]:
            with self.subTest(sizes=altered), self.assertRaises(ValueError):
                target.artifact_sizes(altered, complete=True)

    def test_work_components(self):
        for prefix, cap in target.PREFIX_CAPS.items():
            with self.subTest(prefix=prefix):
                target.work_sizes({prefix+'/x': cap})
                with self.assertRaises(ValueError):
                    target.work_sizes({prefix+'/x': cap+1})
        with self.assertRaises(ValueError):
            target.work_sizes({'unexpected/x': 1})

    def test_measured_admission(self):
        good = sample_snapshot()
        target.admit(good)
        for key, value in [('mem_available_bytes', 10*target.GiB-1), ('cgroup_headroom_bytes', 0),
                           ('disk_available_bytes', 0), ('process_scan', 'partial'),
                           ('process_observation', 'best_effort'), ('tree_rss_sum_bytes', 8*target.GiB+1)]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                target.admit(dict(good, **{key: value}))

    def test_json_refusals(self):
        for raw in [b'{"x":1,"x":2}', b'{"x":NaN}', b'{"x":Infinity}', b'{']:
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                target.decode_json(raw)

    def test_benchmark_leaf_goldens(self):
        for leaves in (target.LEAVES[:2], target.LEAVES[2:], target.LEAVES):
            with self.subTest(leaves=leaves):
                rows = target.parse_benchmarks(benchmark_log(leaves), leaves)
                self.assertEqual([r['name'] for r in rows], list(leaves))
                self.assertTrue(all(r['iterations'] == 1 and r['gomaxprocs'] == 4 for r in rows))

    def test_benchmark_refusals(self):
        raw = benchmark_log(target.LEAVES[:2])
        bad = [raw[:-1], raw.replace(b'-4 ', b'-8 '), raw.replace(b' 1 ', b' 2 '),
               raw.replace(b'100 ns/op', b'NaN ns/op'), raw.replace(b'100 ns/op', b'-1 ns/op'),
               raw.replace(b'200 nodes', b'200 wrong'), raw.replace(b'PASS\n', b'SKIP\n'),
               raw+b'PASS\n', raw.replace(b'BenchmarkBDDAdd64', b'BenchmarkBDDMul8'),
               raw.replace(b'4096 B/op', b'1.5 B/op')]
        for changed in bad:
            with self.subTest(raw=changed), self.assertRaises(ValueError):
                target.parse_benchmarks(changed, target.LEAVES[:2])

    def test_compare_preserves_order_and_noise(self):
        result = target.compare(screens())
        self.assertFalse(result['optimization_accepted'])
        self.assertTrue(result['invariant_parity'] and result['allocation_parity'])
        self.assertEqual(result['results'][0]['pairs'][0]['B_minus_A_ns'], -10)
        self.assertEqual(result['results'][0]['pairs'][1]['B_minus_A_ns'], -15)
        self.assertEqual(result['results'][0]['A_range_ns'], [100, 110])

    def test_compare_retains_parity_failures(self):
        for metric, field in [('nodes', 'invariant_parity'), ('B/op', 'allocation_parity'),
                              ('allocs/op', 'allocation_parity'), ('evictions', 'invariant_parity')]:
            with self.subTest(metric=metric):
                rows = screens()
                index = 2 if metric == 'evictions' else 0
                rows[1]['rows'][index]['metrics'][metric] += 1
                self.assertFalse(target.compare(rows)[field])
        with self.assertRaises(ValueError):
            target.compare(list(reversed(screens()[:3])))

    def test_build_native_race_identity(self):
        info, pins = build_fixture()
        target.validate_build(info, pins)

    def test_build_identity_refusals(self):
        info, pins = build_fixture()
        bad = []
        for key, value in [('Path', 'command-line-arguments.test'), ('GoVersion', 'go1.27.0'),
                           ('Deps', []), ('Main', {'Path': 'wrong', 'Version': '(devel)'})]:
            bad.append(dict(info, **{key: value}))
        for key, value in [('-race', 'false'), ('GOARCH', 'amd64'), ('-gcflags', '-N -l'),
                           ('vcs.modified', 'true'), ('DefaultGODEBUG', 'changed')]:
            changed = copy.deepcopy(info)
            changed['Settings'] = [r for r in changed['Settings'] if r['Key'] != key]
            changed['Settings'].append({'Key': key, 'Value': value})
            bad.append(changed)
        for changed in bad:
            with self.subTest(info=changed), self.assertRaises(ValueError):
                target.validate_build(changed, pins)

    def test_binary_identity_binds_elf_and_bytes(self):
        raw = bytearray(64)
        raw[:6], raw[18:20] = b'\x7fELF\x02\x01', (183).to_bytes(2, 'little')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'asm.test'
            path.write_bytes(raw)
            actual = target.binary_identity(path)
            self.assertEqual(actual['sha256'], hashlib.sha256(raw).hexdigest())
            for machine in (62, 0):
                with self.subTest(machine=machine):
                    raw[18:20] = machine.to_bytes(2, 'little')
                    path.write_bytes(raw)
                    with self.assertRaises(ValueError):
                        target.binary_identity(path)

    def test_semantic_inventory_exact(self):
        self.assertEqual(len(target.CONTROLS), 15)
        self.assertEqual(sum(map(len, target.CONTROLS.values())), 17)
        names = target.validate_events(events(), './asm', sorted(target.CONTROLS), target.CONTROLS)
        self.assertEqual(len(names), 32)

    def test_semantic_absence_skip_duplicate_refused(self):
        original = events()
        bad = [original[:-1], original[:2]+original[3:], original[:2]+[original[1]]+original[2:]]
        for action in ('skip', 'fail'):
            changed = copy.deepcopy(original)
            changed[2]['Action'] = action
            bad.append(changed)
        for changed in bad:
            with self.subTest(events=changed), self.assertRaises(ValueError):
                target.validate_events(changed, './asm', sorted(target.CONTROLS), target.CONTROLS)

    def test_allocated_scan_includes_empty_directories(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            child = root/'empty'
            child.mkdir()
            with mock.patch.object(target.time, 'monotonic', return_value=0):
                self.assertEqual(target.allocated_work(root, 1),
                    (root.stat().st_blocks+child.stat().st_blocks)*512)
                (root/'link').symlink_to(child)
                with self.assertRaises(ValueError):
                    target.allocated_work(root, 1)

    def test_snapshot_inverse_and_source_preservation(self):
        raw, pins = lookup_fixture()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo, work = root/'repo', root/'work'
            (repo/'asm').mkdir(parents=True)
            work.mkdir()
            (repo/'asm/bdd.go').write_bytes(raw)
            rows = {'asm/bdd.go': {'mode': '100644', 'blob': target.git_blob(raw)}}
            contract = {'lookup': pins, 'baseline_tree': target.tree_id(rows)}
            with mock.patch.object(target.time, 'monotonic', return_value=0):
                receipt = target.snapshots(repo, work, rows, contract, 1)
                target.verify_snapshots(work, receipt, 1)
            self.assertEqual((repo/'asm/bdd.go').read_bytes(), raw)
            self.assertEqual((work/'source-B/asm/bdd.go').read_bytes().replace(target.NEW, target.OLD), raw)

    def test_snapshot_reverification_refuses_drift(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for variant in ('A', 'B'):
                (root/('source-'+variant)).mkdir()
                (root/('source-'+variant)/'x').write_bytes(b'x')
                (root/('source-'+variant)/'x').chmod(0o644)
            receipt = {'files': {'x': {'A': hashlib.sha256(b'x').hexdigest(),
                'B': hashlib.sha256(b'x').hexdigest(), 'bytes_A': 1, 'bytes_B': 1,
                'mode': '100644'}}}
            with mock.patch.object(target.time, 'monotonic', return_value=0):
                for altered in ('A', 'B'):
                    with self.subTest(variant=altered):
                        path = root/('source-'+altered)/'x'
                        path.write_bytes(b'y')
                        with self.assertRaises(ValueError):
                            target.verify_snapshots(root, receipt, 1)
                        path.write_bytes(b'x')

    def test_publish_closed_manifest(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for folder in ('A', 'B', 'evidence'):
                (root/folder).mkdir()
            names = {'A/asm.test', 'B/asm.test'} | {'evidence/'+n for n in set(target.LOG_CAPS)|target.RECORD_NAMES}
            for name in names-{'evidence/status.json', 'evidence/manifest.json'}:
                (root/name).write_bytes(b'x')
            with mock.patch.object(target.time, 'monotonic', return_value=0):
                target.publish(root, {'diagnostic_complete': True}, 1, True)
            manifest = json.loads((root/'evidence/manifest.json').read_bytes())
            self.assertEqual({r['path'] for r in manifest['members']}, names-{'evidence/manifest.json'})
            self.assertTrue(manifest['requires_successful_exact_workflow_step'])

    def test_publish_post_fsync_deadline(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'evidence').mkdir()
            clock = [0]
            original = target.base.write_json
            def writing(path, value, cap):
                original(path, value, cap)
                if path.name == 'manifest.json':
                    clock[0] = 1
            with mock.patch.object(target.time, 'monotonic', side_effect=lambda: clock[0]), \
                 mock.patch.object(target.base, 'write_json', side_effect=writing), \
                 self.assertRaises(ValueError):
                target.publish(root, {'diagnostic_complete': False}, 1, False)


if __name__ == '__main__':
    unittest.main(verbosity=2)
