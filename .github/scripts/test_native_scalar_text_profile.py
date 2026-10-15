"""Focused controls for the actual scalar_text owner; no Go/profile execution."""
import copy
import hashlib
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest import mock

import native_scalar_text_profile as profile


class ScalarProfileOwnerTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)

    def tearDown(self):
        self.temporary.cleanup()

    def test_phase_deadlines_share_original_origin(self):
        for phase, now, expected in (
                ('setup', 101, 520), ('build', 110, 650), ('build', 900, 1060),
                ('profile', 120, 780), ('profile', 1600, 1720), ('final', 1700, 1820)):
            with self.subTest(phase=phase, now=now):
                self.assertEqual(profile.phase_deadline(100, phase, now), expected)
        for started, now, phase in ((100, 99, 'setup'), (100, 1900, 'final'),
                                    (100, 521, 'setup'), (float('nan'), 100, 'setup')):
            with self.subTest(started=started, now=now):
                with self.assertRaises(profile.DiagnosticError):
                    profile.phase_deadline(started, phase, now)

    def admitted(self):
        return {'mem_available_bytes': profile.RSS_LIMIT + profile.MEMORY_RESERVE,
                'cgroup_scope': 'visible_v2_hierarchy', 'cgroup_headroom_bytes': 'unlimited',
                'disk_available_bytes': profile.WORK_LIMIT + 2 * profile.ARTIFACT_LIMIT + profile.DISK_RESERVE,
                'process_scan': 'complete', 'process_observation': 'strict_sample_non_atomic',
                'tree_rss_sum_bytes': 1024}

    def test_resource_admission_is_measured_and_fail_closed(self):
        profile.admit_resources(self.admitted())
        for key, value in (('mem_available_bytes', 'unsupported'),
                           ('mem_available_bytes', profile.RSS_LIMIT),
                           ('cgroup_scope', 'unsupported'),
                           ('cgroup_headroom_bytes', 'unsupported'),
                           ('cgroup_headroom_bytes', profile.MEMORY_RESERVE),
                           ('disk_available_bytes', profile.DISK_RESERVE),
                           ('process_scan', 'capped'),
                           ('process_observation', 'best_effort'),
                           ('tree_rss_sum_bytes', 'unsupported'),
                           ('tree_rss_sum_bytes', profile.RSS_LIMIT + 1)):
            with self.subTest(key=key, value=value):
                snapshot = self.admitted()
                snapshot[key] = value
                with self.assertRaises(profile.DiagnosticError):
                    profile.admit_resources(snapshot)

    def status_bytes(self, pid=100, parent=1, state='S', rss='4 kB'):
        return (f'Name:\ttest\nState:\t{state} (state)\nPid:\t{pid}\nPPid:\t{parent}\n'
                + (f'VmRSS:\t{rss}\n' if rss is not None else '')).encode()

    def stat_bytes(self, pid=100, parent=1, starttime=42, name='test', state='S'):
        return (f'{pid} ({name}) {state} {parent} ' + '0 ' * 17 + f'{starttime} 0 0\n').encode()

    def proc_fixture(self, pid=100, parent=1, root=None):
        path = (self.root if root is None else root) / str(pid)
        path.mkdir()
        (path / 'stat').write_bytes(self.stat_bytes(pid, parent))
        (path / 'status').write_bytes(self.status_bytes(pid, parent))
        return path

    def read_budget(self):
        return dict(reads=0, identity_reads=0, status_reads=0, bytes=0,
                    confirmations=0, recovered_rss=0, zombies=0, disappearances=0)

    def test_process_status_reads_are_bounded(self):
        for name in ('exact', 'overflow', 'vanished', 'missing_status', 'permission', 'fifo', 'symlink'):
            with self.subTest(name=name):
                directory = self.root / name
                directory.mkdir()
                path = directory / 'status'
                raw = self.status_bytes()
                if name == 'exact':
                    path.write_bytes(raw)
                    self.assertEqual(profile.process_status(path), raw)
                elif name == 'vanished':
                    directory.rmdir()
                    self.assertIsNone(profile.process_status(path))
                elif name == 'permission':
                    with mock.patch.object(profile.os, 'open', side_effect=PermissionError('unreadable')):
                        with self.assertRaises(PermissionError):
                            profile.process_status(path)
                else:
                    if name == 'overflow':
                        path.write_bytes(b'x' * (profile.PROCESS_STATUS_LIMIT + 1))
                    elif name == 'fifo':
                        os.mkfifo(path)
                    elif name == 'symlink':
                        (directory / 'real').write_bytes(raw)
                        path.symlink_to(directory / 'real')
                    with self.assertRaises((profile.DiagnosticError, OSError)):
                        profile.process_status(path)

    def test_process_status_metadata_is_strict(self):
        good = self.status_bytes()
        self.assertEqual(profile.parse_process_status(good, 100), (1, 4096))
        for name, raw in (
                ('missing_parent', good.replace(b'PPid:\t1\n', b'')),
                ('bad_parent', good.replace(b'PPid:\t1', b'PPid:\tunknown')),
                ('negative_parent', good.replace(b'PPid:\t1', b'PPid:\t-1')),
                ('parent_overflow', good.replace(b'PPid:\t1', b'PPid:\t2147483648')),
                ('self_parent', good.replace(b'PPid:\t1', b'PPid:\t100')),
                ('duplicate_parent', good + b'PPid:\t1\n'),
                ('different_pid', good.replace(b'Pid:\t100\n', b'Pid:\t101\n')),
                ('missing_state', good.replace(b'State:\tS (state)\n', b'')),
                ('invalid_state', good.replace(b'State:\tS', b'State:\t12')),
                ('bad_rss', good.replace(b'4 kB', b'unknown kB')),
                ('wrong_units', good.replace(b'4 kB', b'4 bytes')),
                ('rss_overflow', good.replace(b'4 kB', b'18014398509481984 kB'))):
            with self.subTest(name=name):
                with self.assertRaises(profile.DiagnosticError):
                    profile.parse_process_status(raw, 100)

    def test_process_sample_requires_owned_rss(self):
        proc = self.root / 'proc'
        proc.mkdir()
        for pid, parent in ((100, 1), (101, 100), (102, 1)):
            (proc / str(pid)).mkdir()
            (proc / str(pid) / 'status').write_bytes(self.status_bytes(pid, parent))
            (proc / str(pid) / 'stat').write_bytes(self.stat_bytes(pid, parent))
        with mock.patch.object(profile.resources, 'PROC', proc):
            sample = profile.strict_process_rss(100, time.monotonic() + 2)
            self.assertEqual(sample['tree_rss_sum_bytes'], 8192)
            self.assertEqual(sample['tree_processes'], 2)
            for name in ('owned_missing_rss', 'zombie', 'unrelated_missing_rss', 'missing_root',
                         'entry_cap', 'deadline', 'scan_error'):
                with self.subTest(name=name):
                    owned, unrelated = proc / '101/status', proc / '102/status'
                    if name in ('owned_missing_rss', 'zombie'):
                        owned.write_bytes(self.status_bytes(101, 100,
                                                           'Z' if name == 'zombie' else 'S', None))
                        (proc / '101/stat').write_bytes(self.stat_bytes(101, 100,
                                                                      state='Z' if name == 'zombie' else 'S'))
                    if name == 'unrelated_missing_rss':
                        unrelated.write_bytes(self.status_bytes(102, 1, rss=None))
                    try:
                        if name in ('zombie', 'unrelated_missing_rss'):
                            sample = profile.strict_process_rss(100, time.monotonic() + 2)
                            self.assertEqual(sample['tree_rss_sum_bytes'],
                                             4096 if name == 'zombie' else 8192)
                        elif name == 'entry_cap':
                            with mock.patch.object(profile, 'PROCESS_LIMIT', 2):
                                with self.assertRaises(profile.DiagnosticError):
                                    profile.strict_process_rss(100, time.monotonic() + 2)
                        elif name == 'scan_error':
                            with mock.patch.object(profile.os, 'scandir', side_effect=PermissionError('scan')):
                                with self.assertRaises(PermissionError):
                                    profile.strict_process_rss(100, time.monotonic() + 2)
                        else:
                            with self.assertRaises(profile.DiagnosticError):
                                profile.strict_process_rss(999 if name == 'missing_root' else 100,
                                                          time.monotonic() + (-1 if name == 'deadline' else 2))
                    finally:
                        owned.write_bytes(self.status_bytes(101, 100))
                        (proc / '101/stat').write_bytes(self.stat_bytes(101, 100))
                        unrelated.write_bytes(self.status_bytes(102, 1))

    def test_resource_snapshot_uses_strict_local_observation(self):
        with mock.patch.object(profile.resources, 'read_text', return_value='MemAvailable: 42 kB\n'), \
                mock.patch.object(profile.resources, 'disk_available', return_value=100), \
                mock.patch.object(profile.resources, 'cgroup_memory', return_value={'cgroup_headroom_bytes': 200}), \
                mock.patch.object(profile.resources, 'snapshot', side_effect=AssertionError('best effort')), \
                mock.patch.object(profile.resources, 'process_rss', side_effect=AssertionError('best effort')), \
                mock.patch.object(profile, 'strict_process_rss', return_value={'tree_rss_sum_bytes': 300}) as strict:
            snapshot = profile.resource_snapshot(100, self.root, 999)
        strict.assert_called_once_with(100, 999)
        self.assertEqual(snapshot['mem_available_bytes'], 42 * 1024)
        self.assertEqual(snapshot['cgroup_headroom_bytes'], 200)
        self.assertEqual(snapshot['tree_rss_sum_bytes'], 300)

    def test_process_identity_fields(self):
        for name in ('space', 'parentheses'):
            with self.subTest(name=name):
                raw = self.stat_bytes(name='some name' if name == 'space' else 'some ) ( name)')
                self.assertEqual(profile.parse_process_identity(raw, 100),
                                 {'pid': 100, 'parent': 1, 'starttime': 42, 'state': 'S'})
        for raw in (self.stat_bytes(pid=101), b'100 missing separator\n', b'100 (x) S 1\n',
                    self.stat_bytes(parent=-1), self.stat_bytes(parent=100),
                    self.stat_bytes(parent=2**31), self.stat_bytes(starttime=-1),
                    self.stat_bytes(starttime=2**64)):
            with self.subTest(raw=raw), self.assertRaises(profile.DiagnosticError):
                profile.parse_process_identity(raw, 100)

    def test_process_confirmation_paths(self):
        cases = [('numeric', [('S', '4 kB')], 4096, 0, 0, 0),
                 ('recovered', [('S', None), ('S', '8 kB')], 8192, 1, 1, 0),
                 ('zombie_after', [('S', None), ('Z', None)], 0, 1, 0, 1),
                 ('stat_zombie', [('S', None), ('S', None)], 0, 1, 0, 1),
                 ('unknown', [('S', None), ('S', None)], None, 1, 0, 0),
                 ('dead_final', [('Z', None), ('Z', None)], None, 1, 0, 0),
                 ('unknown_final', [('S', None), ('S', None)], None, 1, 0, 0),
                 ('zombie_first', [('Z', None), ('Z', None)], 0, 1, 0, 1)]
        for name, values, rss, confirmations, recovered, zombies in cases:
            with self.subTest(name=name):
                root = self.root/name; root.mkdir(); path = self.proc_fixture(root=root)
                original = profile.process_status; calls = []
                def reading(file, **kwargs):
                    if file == 'status':
                        state, value = values[len(calls)]; calls.append(kwargs['dir_fd'])
                        (path/'status').write_bytes(self.status_bytes(state=state, rss=value))
                        if name in ('stat_zombie', 'zombie_after', 'zombie_first') and len(calls) == 2:
                            (path/'stat').write_bytes(self.stat_bytes(state='Z'))
                        if name in ('dead_final', 'unknown_final') and len(calls) == 2:
                            (path/'stat').write_bytes(self.stat_bytes(
                                state='X' if name == 'dead_final' else 'Q'))
                    return original(file, **kwargs)
                budget = self.read_budget()
                with mock.patch.object(profile, 'process_status', side_effect=reading):
                    row = profile.observe_process(path, 100, time.monotonic()+2, budget)
                self.assertEqual(row['rss'], rss)
                self.assertEqual(row['parent'], 1)
                self.assertEqual(row['starttime'], 42)
                self.assertEqual(len(set(calls)), 1)
                self.assertEqual(budget['confirmations'], confirmations)
                self.assertEqual(budget['recovered_rss'], recovered)
                self.assertEqual(budget['zombies'], zombies)
                self.assertEqual(budget['status_reads'], len(values))
                self.assertEqual(budget['identity_reads'], len(values))
                if name == 'stat_zombie':
                    self.assertEqual((row['state'], row['first_state'], row['identity_state'],
                                      row['confirmation']), ('S', 'S', 'Z', 'stat_zombie'))

    def test_process_confirmation_identity_refusals(self):
        for name in ('pid', 'status_parent', 'stat_parent', 'starttime', 'replacement'):
            with self.subTest(name=name):
                root = self.root/name; root.mkdir(); path = self.proc_fixture(root=root)
                original = profile.process_status; calls = []
                def reading(file, **kwargs):
                    if file == 'status':
                        calls.append(file); location = path
                        if len(calls) == 1:
                            (path/'status').write_bytes(self.status_bytes(rss=None))
                        else:
                            if name == 'replacement':
                                location = root/'old'; path.rename(location); path.mkdir()
                            (location/'status').write_bytes(self.status_bytes(
                                pid=101 if name == 'pid' else 100,
                                parent=2 if name == 'status_parent' else 1))
                            (location/'stat').write_bytes(self.stat_bytes(
                                parent=2 if name == 'stat_parent' else 1,
                                starttime=43 if name == 'starttime' else 42, state='Z'))
                    return original(file, **kwargs)
                with mock.patch.object(profile, 'process_status', side_effect=reading), \
                        self.assertRaises(profile.DiagnosticError):
                    profile.observe_process(path, 100, time.monotonic()+2, self.read_budget())

    def test_process_confirmed_disappearance(self):
        for phase, code in ((1, profile.errno.ENOENT), (1, profile.errno.ESRCH),
                            (2, profile.errno.ENOENT), (2, profile.errno.ESRCH),
                            (3, profile.errno.ENOENT)):
            with self.subTest(phase=phase, code=code):
                root = self.root/f'{phase}-{code}'; root.mkdir(); path = self.proc_fixture(root=root)
                (path/'status').write_bytes(self.status_bytes(rss=None))
                original = profile.process_status; calls = []
                def reading(file, **kwargs):
                    if file == 'status':
                        calls.append(file)
                        if phase == 3 and len(calls) == 2:
                            (path/'status').write_bytes(self.status_bytes(state='R', rss=None))
                    if ((file == 'status' and len(calls) == phase)
                            or (phase == 3 and file == 'stat' and len(calls) == 2)):
                        (path/'status').unlink(); (path/'stat').unlink(); path.rmdir()
                        raise OSError(code, 'synthetic process exit')
                    return original(file, **kwargs)
                budget = self.read_budget()
                with mock.patch.object(profile, 'process_status', side_effect=reading):
                    row = profile.observe_process(path, 100, time.monotonic()+2, budget)
                self.assertEqual((row['parent'], row['starttime'], row['rss'], row['state']),
                                 (1, 42, 0, 'gone'))
                self.assertEqual(budget['disappearances'], 1)
                if phase == 3:
                    self.assertEqual((row['first_state'], row['last_status_state']), ('S', 'R'))
                self.assertEqual(row['confirmation'],
                                 'anchored_enoent_or_esrch_and_named_directory_absent')

    def test_process_disappearance_refusals(self):
        for name, code in (('present_enoent', profile.errno.ENOENT),
                           ('present_esrch', profile.errno.ESRCH),
                           ('permission', profile.errno.EACCES), ('io', profile.errno.EIO),
                           ('malformed_after_gone', None)):
            with self.subTest(name=name):
                root = self.root/name; root.mkdir(); path = self.proc_fixture(root=root)
                (path/'status').write_bytes(self.status_bytes(rss=None))
                original = profile.process_status; calls = []
                def reading(file, **kwargs):
                    if file == 'status':
                        calls.append(file)
                        if len(calls) == 2:
                            if code is None:
                                (path/'status').unlink(); (path/'stat').unlink(); path.rmdir()
                                return b'malformed\n'
                            raise OSError(code, 'synthetic unconfirmed failure')
                    return original(file, **kwargs)
                budget = self.read_budget()
                with mock.patch.object(profile, 'process_status', side_effect=reading), \
                        self.assertRaises((profile.DiagnosticError, OSError)):
                    profile.observe_process(path, 100, time.monotonic()+2, budget)
                self.assertEqual(budget['disappearances'], 0)

    def test_process_confirmation_preserves_descendants(self):
        for state, rss in (('gone', 0), ('Z', 0), ('S', 8192)):
            with self.subTest(state=state):
                root = self.root/state; root.mkdir()
                for pid, parent in ((100, 1), (101, 100), (102, 101)):
                    self.proc_fixture(pid, parent, root)
                original = profile.observe_process
                def observing(path, pid, deadline, budget):
                    if pid == 101:
                        return {'parent': 100, 'rss': rss, 'state': state,
                                'starttime': 42, 'confirmation': 'synthetic', 'rss_present': rss > 0,
                                'identity_state': 'S'}
                    return original(path, pid, deadline, budget)
                with mock.patch.object(profile.resources, 'PROC', root), \
                        mock.patch.object(profile, 'observe_process', side_effect=observing):
                    sample = profile.strict_process_rss(100, time.monotonic()+2)
                self.assertEqual(sample['tree_processes'], 3)
                self.assertEqual(sample['tree_rss_sum_bytes'], 8192+rss)

    def test_process_confirmation_read_bounds(self):
        for name in ('deadline', 'bytes', 'reads', 'identity_oversize'):
            with self.subTest(name=name):
                root = self.root/name; root.mkdir(); path = self.proc_fixture(root=root)
                budget = self.read_budget(); deadline = time.monotonic()+2
                if name == 'deadline': deadline = time.monotonic()-1
                if name == 'bytes': budget['bytes'] = profile.PROCESS_SAMPLE_READ_LIMIT
                if name == 'reads': budget['reads'] = 4*profile.PROCESS_LIMIT
                if name == 'identity_oversize':
                    (path/'stat').write_bytes(b'x'*(profile.PROCESS_IDENTITY_LIMIT+1))
                with mock.patch.object(profile.os, 'close', wraps=os.close) as closed, \
                        self.assertRaises(profile.DiagnosticError):
                    profile.observe_process(path, 100, deadline, budget)
                self.assertEqual(closed.call_count, 0 if name == 'deadline' else 1)
        budget = self.read_budget()
        with self.assertRaises(profile.DiagnosticError):
            profile.process_status(self.root/'absent', budget=budget, deadline=time.monotonic()+2)
        self.assertEqual((budget['reads'], budget['bytes']), (1, profile.PROCESS_STATUS_LIMIT+1))

    def test_process_unknown_rss_refusal_detail(self):
        for pid, parent in ((100, 1), (101, 100)):
            path = self.proc_fixture(pid, parent)
            if pid == 101:
                (path/'status').write_bytes(self.status_bytes(pid, parent, rss=None))
        with mock.patch.object(profile.resources, 'PROC', self.root), \
                self.assertRaisesRegex(profile.DiagnosticError,
                    'pid=101 parent=100 starttime=42 state=S first_state=S confirmation=reread'):
            profile.strict_process_rss(100, time.monotonic()+2)

    def test_process_confirmation_detail_cap(self):
        for pid, parent in ((100, 1), (101, 100), (102, 101)):
            path = self.proc_fixture(pid, parent)
            if pid != 100:
                (path/'status').write_bytes(self.status_bytes(pid, parent, 'Z', None))
                (path/'stat').write_bytes(self.stat_bytes(pid, parent, state='Z'))
        for limit in (2, 1):
            with self.subTest(limit=limit), mock.patch.object(profile.resources, 'PROC', self.root), \
                    mock.patch.object(profile, 'PROCESS_CONFIRMATION_LIMIT', limit):
                if limit == 1:
                    with self.assertRaisesRegex(profile.DiagnosticError, 'detail cap'):
                        profile.strict_process_rss(100, time.monotonic()+2)
                else:
                    sample = profile.strict_process_rss(100, time.monotonic()+2)
                    self.assertEqual(sample['tree_processes'], 3)
                    self.assertEqual(sample['tree_rss_sum_bytes'], 4096)
                    self.assertEqual(sample['owned_process_confirmations'], [
                        {'pid': pid, 'parent': parent, 'starttime': 42, 'state': 'Z',
                         'first_state': 'Z', 'last_status_state': 'Z', 'identity_state': 'Z',
                         'confirmation': 'stat_zombie', 'rss_bytes': 0}
                        for pid, parent in ((101, 100), (102, 101))])

    def test_log_cap_keeps_bounded_prefix_and_records_overflow(self):
        output = profile.CappedOutput(self.root / 'log', 4)
        try:
            output.write(b'ab')
            with self.assertRaises(profile.DiagnosticError):
                output.write(b'cdef')
            self.assertTrue(output.overflow)
            self.assertEqual(output.count, 4)
        finally:
            output.close()
        self.assertEqual((self.root / 'log').read_bytes(), b'abcd')

    def test_log_write_failure_propagates(self):
        output = profile.CappedOutput(self.root / 'log', 4)
        output.file.close()
        with self.assertRaises(ValueError):
            output.write(b'ab')

    def test_log_flush_failure_propagates(self):
        output = profile.CappedOutput(self.root / 'log', 4)
        with mock.patch.object(profile.os, 'fsync', side_effect=OSError('flush failed')):
            with self.assertRaises(OSError):
                output.close()
        output.file.close()

    def test_bounded_reads_refuse_links_special_files_and_overflow(self):
        path = self.root / 'regular'
        path.write_bytes(b'data')
        self.assertEqual(profile.file_bytes(path, 4), b'data')
        with self.assertRaises(profile.DiagnosticError):
            profile.file_bytes(path, 3)
        link = self.root / 'link'
        link.symlink_to(path)
        with self.assertRaises(profile.DiagnosticError):
            profile.file_bytes(link, 4)
        hard = self.root / 'hard'
        os.link(path, hard)
        with self.assertRaises(profile.DiagnosticError):
            profile.file_bytes(hard, 4)
        fifo = self.root / 'fifo'
        os.mkfifo(fifo)
        with self.assertRaises(profile.DiagnosticError):
            profile.file_bytes(fifo, 4)

    def test_duplicate_json_and_nonfinite_numbers_fail(self):
        for raw in (b'{"x":1,"x":2}', b'{"x":NaN}', b'{"x":Infinity}', b'{"x":'):
            with self.subTest(raw=raw):
                path = self.root / 'json'
                path.write_bytes(raw)
                with self.assertRaises(profile.DiagnosticError):
                    profile.read_json(path)

    def test_source_tree_count_and_deadline_are_bounded(self):
        for name in ('one', 'two'):
            (self.root / name).write_bytes(b'a')
        with self.assertRaises(profile.DiagnosticError):
            profile.tree_sizes(self.root, max_files=1, deadline=time.monotonic() + 1)
        with self.assertRaises(profile.DiagnosticError):
            profile.tree_sizes(self.root, max_files=10, deadline=time.monotonic() - 1)

    def test_artifact_partitions_and_exact_membership(self):
        sizes = {name: 1 for name in profile.PROFILE_NAMES + profile.RECORD_NAMES}
        profile.validate_artifact_sizes(sizes, {}, complete=True)
        mutations = [('missing', lambda d: d.pop('cpu.pprof')),
                     ('unknown', lambda d: d.update({'solver': 1})),
                     ('empty', lambda d: d.update({'cpu.pprof': 0})),
                     ('profile', lambda d: d.update({'cpu.pprof': profile.PROFILE_LIMIT + 1})),
                     ('records', lambda d: d.update({'context.json': profile.RECORD_LIMIT})),
                     ('log', lambda d: d.update({'diagnostic.log': profile.LOG_LIMIT + 1})),
                     ('reserve', lambda d: d.update({'runner-status.json': profile.RESERVE_LIMIT + 1}))]
        for name, mutate in mutations:
            with self.subTest(name=name):
                value = dict(sizes)
                mutate(value)
                with self.assertRaises(profile.DiagnosticError):
                    profile.validate_artifact_sizes(value, {}, complete=True)

    def report_fixture(self):
        inputs = [{'name': name, 'source_sha256': 'b' * 64, 'extern_symbol': ''}
                  for name in ('unselected', 'scalar_text')]
        supplied = {'input': {'name': 'supplied', 'source_sha256': 'c' * 64,
                              'extern_symbol': ''}, 'arch': 'arm64', 'body_sha256': 'd' * 64}
        inventory = {'eligible': inputs, 'supplied': [supplied], 'externs': []}
        names = ['first', 'second', 'identity']
        candidates = [{'name': name, 'cached': False, 'outcome': 'proven', 'message': 'checked',
                       'body_sha256': 'e' * 64, 'recipe_sha256': 'f' * 64} for name in names]
        report = {'schema_version': 2, 'inventory': copy.deepcopy(inventory),
                  'functions': [{'input': copy.deepcopy(inputs[0]), 'validations': [],
                                 'selected': None, 'status': 'c-fallback', 'reason': 'filtered'},
                                {'input': copy.deepcopy(inputs[1]), 'validations': candidates,
                                 'selected': copy.deepcopy(candidates[-1]), 'status': 'proven',
                                 'reason': 'checked'}],
                  'supplied': [dict(supplied, status='proven', reason='checked')]}
        return report, inventory, names

    def test_report_requires_full_uncached_three_candidate_search(self):
        report, inventory, names = self.report_fixture()
        profile.validate_report(report, inventory, names)
        mutations = [
            ('missing_row', lambda r: r['functions'].pop()),
            ('duplicate_row', lambda r: r['functions'].__setitem__(0, r['functions'][1])),
            ('extra_row', lambda r: r['functions'].append(r['functions'][1])),
            ('selector', lambda r: r['functions'][0].update(selected=r['functions'][1]['selected'])),
            ('missing_candidate', lambda r: r['functions'][1]['validations'].pop()),
            ('extra_candidate', lambda r: r['functions'][1]['validations'].append(r['functions'][1]['selected'])),
            ('order', lambda r: r['functions'][1]['validations'].reverse()),
            ('cached', lambda r: r['functions'][1]['validations'][0].update(cached=True)),
            ('digest', lambda r: r['functions'][1]['validations'][0].update(body_sha256='invalid')),
            ('verdict', lambda r: r['functions'][1]['validations'][0].update(outcome='pending')),
            ('selection', lambda r: r['functions'][1].update(selected=None)),
            ('inventory', lambda r: r['inventory'].update(externs=[{}])),
            ('supplied_missing', lambda r: r['supplied'].clear()),
            ('supplied_unfinished', lambda r: r['supplied'][0].update(status='pending')),
        ]
        for name, mutate in mutations:
            with self.subTest(name=name):
                value = copy.deepcopy(report)
                mutate(value)
                with self.assertRaises(profile.DiagnosticError):
                    profile.validate_report(value, inventory, names)

    def test_environment_does_not_erase_experiments(self):
        clean = profile.clean_environment({'CGO_ENABLED': '1', 'GOFLAGS': ''}, self.root)
        self.assertEqual(clean['GOCACHE'], str(self.root / 'gocache'))
        self.assertNotIn('GOMAXPROCS', clean)
        self.assertEqual(clean['GOENV'], 'off')
        for name in ('OAK_NATIVE_ONLY', 'OAK_NATIVE_PREREQUISITE', 'OAKOPT', 'OAKCACHE',
                     'GOMAXPROCS', 'GOGC', 'GOMEMLIMIT', 'GORACE', 'GOFLAGS', 'GODEBUG', 'GOWORK',
                     'CC', 'CXX', 'GOENV'):
            with self.subTest(name=name):
                with self.assertRaises(profile.DiagnosticError):
                    profile.clean_environment({name: 'override'}, self.root)

    def test_tool_environment_binds_authenticated_paths(self):
        tools = {name: {'path': '/tools/' + name} for name in ('go', 'cc', 'c++')}
        env = profile.clean_environment({}, self.root)
        bound = profile.bind_tool_environment(env, tools)
        self.assertEqual(bound['CC'], '/tools/cc')
        self.assertEqual(bound['CXX'], '/tools/c++')
        self.assertEqual(bound['GOENV'], 'off')
        self.assertNotIn('CC', env)
        for name in ('incoming_cc', 'incoming_cxx', 'persistent_goenv', 'relative_go', 'space_cc', 'quote_cxx'):
            with self.subTest(name=name):
                changed_env, changed_tools = dict(env), copy.deepcopy(tools)
                if name == 'incoming_cc':
                    changed_env['CC'] = 'override'
                elif name == 'incoming_cxx':
                    changed_env['CXX'] = 'override'
                elif name == 'persistent_goenv':
                    changed_env['GOENV'] = '/persistent/config'
                elif name == 'relative_go':
                    changed_tools['go']['path'] = 'go'
                elif name == 'space_cc':
                    changed_tools['cc']['path'] = '/tools/cc wrapper'
                else:
                    changed_tools['c++']['path'] = '/tools/"c++"'
                with self.assertRaises(profile.DiagnosticError):
                    profile.bind_tool_environment(changed_env, changed_tools)

    def test_go_environment_matches_bound_compilers(self):
        env = {'CC': '/tools/cc', 'CXX': '/tools/c++', 'GOENV': 'off'}
        observed = dict(env, GOENV='', GOHOSTARCH='arm64', GOARCH='arm64', GOHOSTOS='linux',
                        GOOS='linux', CGO_ENABLED='1')
        profile.validate_tool_environment(observed, env)
        for key, value in (('CC', 'wrapper'), ('CXX', 'wrapper'), ('GOENV', '/persistent/config'),
                           ('GOARCH', 'amd64')):
            with self.subTest(key=key):
                with self.assertRaises(profile.DiagnosticError):
                    profile.validate_tool_environment(dict(observed, **{key: value}), env)

    def test_exact_source_and_support_membership(self):
        source = self.root / 'raw' / 'source'
        source.mkdir(parents=True)
        (self.root / 'stdlib').mkdir()
        pins = {'sources': {}, 'support_sources': {}}
        for index in range(19):
            raw = b'x' * (47870 if index < 18 else 47873)
            name = f'input{index}.oak'
            (source / name).write_bytes(raw)
            pins['sources'][name] = hashlib.sha256(raw).hexdigest()
        for name in ('stdlib/host.oak', 'stdlib/std.oak'):
            (self.root / name).write_bytes(b'support')
            pins['support_sources'][name] = hashlib.sha256(b'support').hexdigest()
        deadline = time.monotonic() + 5
        profile.validate_inputs(self.root, source.parent, pins, deadline)
        original = (source / 'input0.oak').read_bytes()
        for name in ('changed', 'missing', 'extra', 'extra_directory', 'support'):
            with self.subTest(name=name):
                if name == 'changed':
                    (source / 'input0.oak').write_bytes(b'y' * len(original))
                elif name == 'missing':
                    (source / 'input0.oak').unlink()
                elif name == 'extra':
                    (source / 'unexpected').write_bytes(b'')
                elif name == 'extra_directory':
                    (source / 'unexpected_dir').mkdir()
                else:
                    (self.root / 'stdlib/host.oak').write_bytes(b'changed')
                with self.assertRaises(profile.DiagnosticError):
                    profile.validate_inputs(self.root, source.parent, pins, deadline)
                (source / 'input0.oak').write_bytes(original)
                (source / 'unexpected').unlink(missing_ok=True)
                if (source / 'unexpected_dir').exists():
                    (source / 'unexpected_dir').rmdir()
                (self.root / 'stdlib/host.oak').write_bytes(b'support')

    def test_build_settings_bind_native_race_and_disallow_overrides(self):
        expected = {'version': 'go1.27.1', 'main': {'Path': 'oak', 'Version': '(devel)'},
                    'dependencies': [], 'settings': {'-race': 'true', 'GOARCH': 'arm64',
                                                      'GOOS': 'linux', 'CGO_ENABLED': '1',
                                                      'CGO_CFLAGS': ''}}
        build = {'GoVersion': 'go1.27.1', 'Main': dict(expected['main'], Sum='', Replace=None),
                 'Deps': [], 'Settings': [{'Key': key, 'Value': value}
                                          for key, value in expected['settings'].items()]}
        profile.validate_go_build(build, expected, 'a' * 40)
        omitted_empty = copy.deepcopy(build)
        omitted_empty['Settings'][-1].pop('Value')
        profile.validate_go_build(omitted_empty, expected, 'a' * 40)
        for name, mutate in (
                ('version', lambda b: b.update(GoVersion='go1.0')),
                ('race', lambda b: b['Settings'][0].update(Value='false')),
                ('duplicate', lambda b: b['Settings'].append(b['Settings'][0])),
                ('tags', lambda b: b['Settings'].append({'Key': '-tags', 'Value': 'override'})),
                ('pgo', lambda b: b['Settings'].append({'Key': '-pgo', 'Value': 'default.pgo'})),
                ('asan', lambda b: b['Settings'].append({'Key': '-asan', 'Value': 'true'})),
                ('asmflags', lambda b: b['Settings'].append({'Key': '-asmflags', 'Value': 'override'})),
                ('trimpath', lambda b: b['Settings'].append({'Key': '-trimpath', 'Value': 'true'})),
                ('malformed_value', lambda b: b['Settings'][-1].update(Value=None)),
                ('empty_key', lambda b: b['Settings'][-1].update(Key='')),
                ('dirty', lambda b: b['Settings'].append({'Key': 'vcs.modified', 'Value': 'true'})),
                ('source', lambda b: b['Settings'].append({'Key': 'vcs.revision', 'Value': 'b' * 40}))):
            with self.subTest(name=name):
                changed = copy.deepcopy(build)
                mutate(changed)
                with self.assertRaises(profile.DiagnosticError):
                    profile.validate_go_build(changed, expected, 'a' * 40)

    def test_child_receipt_rejects_incomplete_or_unbound_evidence(self):
        report, inventory, names = self.report_fixture()
        expected_build = {'version': 'go1.27.1', 'main': {'Path': 'oak', 'Version': '(devel)'},
                          'dependencies': [], 'settings': {'-race': 'true'}}
        pins = {'sources': {}, 'support_sources': {}, 'candidate_names': names,
                'go_build': expected_build}
        context = {'inputs': pins, 'outer_context_sha256': 'a' * 64,
                   'harness_sha256': 'c' * 64, 'target': 'linux/arm64', 'c_opt_level': 1,
                   'gogc_environment': '', 'num_cpu': 4, 'gomaxprocs': 4,
                   'go_build': {'GoVersion': 'go1.27.1', 'Main': expected_build['main'], 'Deps': [],
                                'Settings': [{'Key': '-race', 'Value': 'true'}]}}
        receipt = {'schema_version': 1, 'kind': 'scalar-text-profile-diagnostic',
                   'status': 'diagnostic_complete_pending_outer_validation', 'error': '',
                   'selector': 'scalar_text', 'comparable': True, 'emit_completed': True,
                   'report_count': 1, 'candidate_names': names,
                   'profiles': {name: {'bytes': 4, 'sha256': 'a' * 64} for name in profile.PROFILE_NAMES},
                   'inputs_sha256': 'a' * 64, 'outer_context_sha256': 'a' * 64,
                   'harness_sha256': 'c' * 64, 'block_rate_ns': 1000000, 'mutex_fraction': 100,
                   'elapsed_ns': 3, 'profile_started_unix_ns': 1, 'profile_stopped_unix_ns': 2}
        for name in profile.PROFILE_NAMES:
            (self.root / name).write_bytes(b'data')
        def validate(value):
            records = {'context.json': context, 'report.json': report, 'result.json': value,
                       'native_prover_inventory.json': inventory}
            with mock.patch.object(profile, 'read_json', side_effect=lambda path: records[path.name]), \
                    mock.patch.object(profile, 'digest', return_value='a' * 64):
                return profile.validate_child(self.root, self.root, self.root, pins,
                                              {'source_sha': 'd' * 40}, 'c' * 64)
        validate(receipt)
        for name, mutate in (
                ('incomplete', lambda r: r.update(status='incomplete')),
                ('emit', lambda r: r.update(emit_completed=False)),
                ('comparable', lambda r: r.update(comparable=False)),
                ('multiple_reports', lambda r: r.update(report_count=2)),
                ('selector', lambda r: r.update(selector='entry_text')),
                ('missing_profile', lambda r: r['profiles'].pop('cpu.pprof')),
                ('profile_hash', lambda r: r['profiles']['cpu.pprof'].update(sha256='b' * 64)),
                ('inputs', lambda r: r.update(inputs_sha256='b' * 64)),
                ('outer', lambda r: r.update(outer_context_sha256='b' * 64)),
                ('harness', lambda r: r.update(harness_sha256='b' * 64)),
                ('rates', lambda r: r.update(mutex_fraction=1)),
                ('unflushed', lambda r: r.update(profile_stopped_unix_ns=0))):
            with self.subTest(name=name):
                changed = copy.deepcopy(receipt)
                mutate(changed)
                with self.assertRaises(profile.DiagnosticError):
                    validate(changed)

    def command(self, chunks, *, cap=4096, seconds=4, exited=True, returncode=0):
        """Exercise the owner with synthetic pipes/processes, never launch one."""
        sink = profile.CappedOutput(self.root / 'command.log', cap)
        evidence = []
        chunks = list(chunks)
        now = [100.0]
        def tick():
            now[0] += 0.01
            return now[0]
        process = mock.Mock(pid=123, returncode=None)
        process.stdout.fileno.return_value = 321
        def wait(**kwargs):
            process.returncode = returncode
            return returncode
        process.wait.side_effect = wait
        selector = mock.MagicMock()
        selector.__enter__.return_value = selector
        selector.select.side_effect = lambda timeout: [(None, None)] if chunks else []
        exit_info = SimpleNamespace(si_code=os.CLD_EXITED, si_status=returncode) if exited else None
        try:
            with mock.patch.object(profile.subprocess, 'Popen', return_value=process) as popen, \
                    mock.patch.object(profile.os, 'set_blocking'), \
                    mock.patch.object(profile.os, 'read', side_effect=lambda fd, cap: chunks.pop(0)), \
                    mock.patch.object(profile.os, 'killpg'), \
                    mock.patch.object(profile.selectors, 'DefaultSelector', return_value=selector), \
                    mock.patch.object(profile, 'child_exit', return_value=exit_info), \
                    mock.patch.object(profile.time, 'monotonic', side_effect=tick), \
                    mock.patch.object(profile.time, 'sleep'):
                result = profile.bounded_command(['synthetic-child'], sink, 100 + seconds,
                                                 {}, self.root, capture_limit=cap, evidence=evidence)
                self.assertTrue(popen.call_args.kwargs['start_new_session'])
                return result, evidence
        finally:
            sink.close()
            self.evidence = evidence

    def test_command_success_requires_eof_and_direct_join(self):
        raw, evidence = self.command([b'out', b'err', b''])
        self.assertEqual(raw, b'outerr')
        self.assertTrue(evidence[0]['pipe_eof'])
        self.assertTrue(evidence[0]['direct_child_joined'])
        self.assertEqual(evidence[0]['returncode'], 0)

    def test_command_output_overflow_kills_and_joins(self):
        with self.assertRaises(profile.DiagnosticError):
            self.command([b'x' * 10000], cap=4)
        self.assertTrue(self.evidence[0]['direct_child_joined'])
        self.assertEqual((self.root / 'command.log').stat().st_size, 4)

    def test_command_timeout_kills_and_joins(self):
        with self.assertRaises(profile.DiagnosticError):
            self.command([], seconds=3.1, exited=False, returncode=-15)
        self.assertTrue(self.evidence[0]['timed_out'])
        self.assertTrue(self.evidence[0]['direct_child_joined'])

    def test_profile_parser_nonzero_is_not_complete(self):
        with self.assertRaises(profile.DiagnosticError):
            self.command([b'invalid profile', b''], returncode=1)
        self.assertTrue(self.evidence[0]['pipe_eof'])
        self.assertTrue(self.evidence[0]['direct_child_joined'])
        self.assertEqual(self.evidence[0]['returncode'], 1)

    def test_exited_leader_with_inherited_pipe_is_not_success(self):
        with self.assertRaises(profile.DiagnosticError):
            self.command([], seconds=3.2)
        self.assertTrue(self.evidence[0]['timed_out'])
        self.assertFalse(self.evidence[0]['pipe_eof'])
        self.assertTrue(self.evidence[0]['direct_child_joined'])

    def test_group_is_killed_before_reaping_direct_child(self):
        operations = []
        child = mock.Mock(pid=123)
        child.wait.side_effect = lambda **kwargs: operations.append(('wait', kwargs)) or 0
        with mock.patch.object(profile, 'signal_group',
                               side_effect=lambda p, sig: operations.append(('signal', sig))), \
                mock.patch.object(profile, 'child_exit', return_value=object()):
            profile.terminate_join(child, time.monotonic() + 3)
        self.assertEqual([operation[0] for operation in operations], ['signal', 'signal', 'wait'])
        self.assertEqual(operations[1][1], signal.SIGKILL)

    def test_waitid_observation_never_reaps(self):
        child = mock.Mock(pid=123)
        with mock.patch.object(profile.os, 'waitid', return_value=None) as waitid:
            self.assertIsNone(profile.child_exit(child))
        self.assertEqual(waitid.call_args.args,
                         (os.P_PID, 123, os.WEXITED | os.WNOHANG | os.WNOWAIT))
        child.poll.assert_not_called()
        child.wait.assert_not_called()

    def test_cleanup_always_attempts_direct_reap(self):
        for name in ('term_failure', 'observation_failure', 'kill_failure', 'wait_timeout',
                     'repeat_term', 'repeat_int'):
            with self.subTest(name=name):
                operations, handlers = [], {}
                child = mock.Mock(pid=123, returncode=None)
                def install(sig, handler):
                    old = handlers.get(sig, signal.SIG_DFL)
                    handlers[sig] = handler
                    return old
                def send(process, sig):
                    operations.append(('signal', sig))
                    if ((name == 'term_failure' and sig == signal.SIGTERM)
                            or (name == 'kill_failure' and sig == signal.SIGKILL)):
                        raise OSError('signal failed')
                def observe(process):
                    if name == 'observation_failure':
                        raise KeyboardInterrupt('observation interrupted')
                    if name in ('repeat_term', 'repeat_int'):
                        sig = signal.SIGTERM if name == 'repeat_term' else signal.SIGINT
                        handlers[sig](sig, None)
                        handlers[sig](sig, None)
                    return object()
                def wait(**kwargs):
                    operations.append(('wait', kwargs))
                    if name == 'wait_timeout':
                        raise subprocess.TimeoutExpired('synthetic', 1)
                    child.returncode = -9
                    return -9
                child.wait.side_effect = wait
                with mock.patch.object(profile.signal, 'signal', side_effect=install), \
                        mock.patch.object(profile, 'signal_group', side_effect=send), \
                        mock.patch.object(profile, 'child_exit', side_effect=observe):
                    with self.assertRaises(profile.DiagnosticError):
                        profile.terminate_join(child, time.monotonic() + 3)
                child.wait.assert_called_once()
                self.assertEqual([row[0] for row in operations], ['signal', 'signal', 'wait'])
                self.assertEqual(operations[1][1], signal.SIGKILL)
                self.assertEqual(handlers, {signal.SIGTERM: signal.SIG_DFL, signal.SIGINT: signal.SIG_DFL})

    def test_bounded_upload_omits_oversized_and_compiled_outputs(self):
        result, artifact = self.root / 'raw', self.root / 'artifact'
        result.mkdir()
        artifact.mkdir()
        (result / 'cpu.pprof').write_bytes(b'profile')
        with (result / 'block.pprof').open('wb') as output:
            output.write(b'x' * 17)
        (result / 'solver').write_bytes(b'compiled')
        (result / 'root-harness').write_bytes(b'compiled')
        status = {'diagnostic_complete': False}
        with mock.patch.object(profile.resources, 'disk_available', return_value=3 * profile.GiB), \
                mock.patch.object(profile, 'PROFILE_LIMIT', 16):
            profile.stage_evidence(result, artifact, {'sources': {}}, status, time.monotonic() + 5)
        self.assertEqual((artifact / 'cpu.pprof').read_bytes(), b'profile')
        self.assertFalse((artifact / 'block.pprof').exists())
        self.assertFalse((artifact / 'solver').exists())
        self.assertFalse((artifact / 'root-harness').exists())
        self.assertFalse(status['diagnostic_complete'])
        self.assertTrue(status['staging_omissions'])


if __name__ == '__main__':
    unittest.main()
