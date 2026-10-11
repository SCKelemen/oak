"""Runner deadline and process evidence tests; no Oak/native builds are run."""
import io
import copy
import ctypes
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

import native_arm64_prerequisite as prerequisite


def _fixture_process_identity(pid):
    raw = Path(f'/proc/{pid}/stat').read_text()
    fields = raw.rsplit(') ', 1)[1].split()
    return dict(pid=int(raw.split(' ', 1)[0]), parent_pid=int(fields[1]),
                group=int(fields[2]), session=int(fields[3]), starttime=int(fields[19]),
                state=fields[0])


_FORK_DESCENDANT_SOURCE = (
    "import json,os,pathlib,sys,time\n"
    "child=os.fork()\n"
    "if child:\n"
    " record={'pid':child,'parent_pid':os.getpid(),'owner_pid':os.getppid()}\n"
    " if sys.platform.startswith('linux'):\n"
    "  child_stat=pathlib.Path(f'/proc/{child}/stat').read_text().rsplit(') ',1)[1].split()\n"
    "  parent_stat=pathlib.Path('/proc/self/stat').read_text().rsplit(') ',1)[1].split()\n"
    "  record.update(starttime=int(child_stat[19]),original_parent_pid=int(child_stat[1]),\n"
    "                parent_starttime=int(parent_stat[19]),group=int(child_stat[2]),session=int(child_stat[3]))\n"
    " print(json.dumps(record),flush=True)\n"
    " os._exit(0)\n"
    "else:\n")


class _FixtureDescendant:
    """Join only this fixture's killed orphan, without concealing a survivor."""
    def __init__(self, case):
        self.case = case
        self.linux = sys.platform.startswith('linux')
        self.popen = subprocess.Popen
        self.leader = None
        self.record = None

    def _subreaper_state(self):
        value = ctypes.c_int()
        if self.prctl(37, ctypes.byref(value), 0, 0, 0) != 0:  # PR_GET_CHILD_SUBREAPER
            raise OSError(ctypes.get_errno(), 'cannot read fixture subreaper state')
        return value.value

    def _set_subreaper(self, value):
        if self.prctl(36, value, 0, 0, 0) != 0:  # PR_SET_CHILD_SUBREAPER
            raise OSError(ctypes.get_errno(), 'cannot set fixture subreaper state')

    def __enter__(self):
        if self.linux:
            self.owner = _fixture_process_identity(os.getpid())
            self.prctl = ctypes.CDLL(None, use_errno=True).prctl
            self.prctl.restype = ctypes.c_int
            self.previous_subreaper = self._subreaper_state()
            self._set_subreaper(1)
        return self

    def launch(self, *args, **kwargs):
        self.case.assertIsNone(self.leader)
        self.leader = self.popen(*args, **kwargs)
        if self.linux:
            # Capture the direct child's identity before handing it to the
            # production wait path. An exited leader is still ours to reap.
            self.leader_identity = _fixture_process_identity(self.leader.pid)
            self.case.assertEqual(self.leader_identity['parent_pid'], os.getpid())
        return self.leader

    def observe(self, raw):
        record = json.loads(raw)
        fields = {'pid', 'parent_pid', 'owner_pid'}
        if self.linux:
            fields |= {'starttime', 'original_parent_pid', 'parent_starttime', 'group', 'session'}
        self.case.assertEqual(set(record), fields)
        self.case.assertTrue(all(type(value) is int and value > 0 for value in record.values()))
        self.case.assertNotIn(record['pid'], (os.getpid(), self.leader.pid))
        self.case.assertEqual(record['parent_pid'], self.leader.pid)
        self.case.assertEqual(record['owner_pid'], os.getpid())
        if self.linux:
            self.case.assertEqual(record['original_parent_pid'], self.leader.pid)
            self.case.assertEqual(record['parent_starttime'], self.leader_identity['starttime'])
            self.case.assertEqual((record['group'], record['session']), (self.leader.pid, self.leader.pid))
        self.record = record

    def _owned_child(self):
        current_owner = _fixture_process_identity(os.getpid())
        self.case.assertEqual(current_owner['starttime'], self.owner['starttime'])
        child = _fixture_process_identity(self.record['pid'])
        self.case.assertEqual(child['pid'], self.record['pid'])
        self.case.assertEqual(child['starttime'], self.record['starttime'])
        self.case.assertEqual(child['parent_pid'], self.owner['pid'])
        self.case.assertEqual((child['group'], child['session']),
                              (self.record['group'], self.record['session']))
        return child

    def assert_stopped(self, message):
        deadline = time.monotonic() + 1
        while True:
            if self.linux:
                if self._owned_child()['state'] == 'Z':
                    return
            else:
                # Other POSIX systems keep init as the orphan's parent. Do not
                # wait on a PID we do not own; still require it to disappear.
                try:
                    os.kill(self.record['pid'], 0)
                except ProcessLookupError:
                    return
            if time.monotonic() >= deadline:
                self.case.fail(message)
            time.sleep(0.005)

    def __exit__(self, kind, error, trace):
        if self.linux:
            try:
                if self.record is not None:
                    # This runs after the original kill/timing/evidence
                    # assertions. A survivor fails; cleanup never kills it.
                    self.case.assertEqual(self._owned_child()['state'], 'Z')
                    joined, status = os.waitpid(self.record['pid'], os.WNOHANG)
                    self.case.assertEqual(joined, self.record['pid'])
                    self.case.assertTrue(os.WIFSIGNALED(status))
                    self.case.assertEqual(os.WTERMSIG(status), signal.SIGKILL)
            finally:
                self._set_subreaper(self.previous_subreaper)
                self.case.assertEqual(self._subreaper_state(), self.previous_subreaper)
        return False


class PrerequisiteExecutionTests(unittest.TestCase):
    def setUp(self):
        temporary = self.enterContext(tempfile.TemporaryDirectory())
        self.directory = Path(temporary)
        self.untracked = self.enterContext(mock.patch.object(prerequisite, 'check_untracked_inputs'))

    def test_budget_covers_all_stages_once_and_preserves_exact_harness_bytes(self):
        harness = self.directory / prerequisite.HARNESS
        native = self.directory / prerequisite.NATIVE
        stages = []
        def bounded(command, log, deadline, env):
            stages.append((command, deadline))
            self.assertEqual(env['GOFLAGS'], '')
            self.assertNotIn(prerequisite.ENVIRONMENT, env)
            if log.stem == 'root-harness-build':
                harness.write_bytes(b'persisted race harness')
            elif log.stem == 'root-harness-list':
                log.write_text('TestOne\nTestTwo\n')
            else:
                native.mkdir()
                (native / 'success.json').write_text('{}')
        with mock.patch.object(prerequisite, '_bounded_command', side_effect=bounded), \
             mock.patch.object(prerequisite, 'validate_manifest') as validate, \
             mock.patch.dict(os.environ, {'GOFLAGS': '-short', prerequisite.ENVIRONMENT: '/stale'}):
            result = prerequisite.prepare(self.directory, self.directory, ['TestOne', 'TestTwo'], {'fixture': True})
        self.assertEqual(len(stages), 3)
        self.assertEqual(len({deadline for _, deadline in stages}), 1)
        self.assertEqual(stages[0][0], ['go', 'test', '-c', '-race', '-o', str(harness), '.'])
        self.assertEqual(stages[1][0], [str(harness), '-test.list=^(TestOne|TestTwo)$'])
        self.assertEqual(stages[2][0], [str(harness), 'native-prover-build', str(native)])
        self.assertEqual(result['harness_sha256'], prerequisite.digest(harness))
        self.assertEqual(result['budget_seconds'], 5400)
        validate.assert_called_once_with(self.directory, self.directory, {'fixture': True},
                                         prerequisite.digest(harness), str(self.directory))

    def test_failed_stage_or_changed_harness_cannot_write_success(self):
        for mutation in ('failure', 'changed', 'missing-root', 'validation'):
            calls = []
            def bounded(command, log, deadline, env):
                calls.append(log.stem)
                harness = self.directory / prerequisite.HARNESS
                if log.stem == 'root-harness-build':
                    harness.write_bytes(b'original')
                elif log.stem == 'root-harness-list':
                    if mutation == 'failure':
                        raise ValueError('failed list')
                    if mutation == 'changed':
                        harness.write_bytes(b'changed')
                    log.write_text('TestOther\n' if mutation == 'missing-root' else 'TestOne\n')
            with self.subTest(mutation=mutation), \
                 mock.patch.object(prerequisite, '_bounded_command', side_effect=bounded), \
                 mock.patch.object(prerequisite, 'validate_manifest', side_effect=ValueError('invalid artifact')), \
                 self.assertRaises(ValueError):
                prerequisite.prepare(self.directory, self.directory, ['TestOne'], {})
            self.assertFalse((self.directory / 'prerequisite-status.json').exists())
            self.assertLessEqual(len(calls), 3)

    def test_timeout_kills_entire_process_group_and_preserves_failed_status(self):
        process = mock.Mock(pid=424242)
        process.wait.side_effect = [subprocess.TimeoutExpired('compile', 1), -9]
        log = self.directory / 'native-prover-build.log'
        with mock.patch.object(prerequisite.subprocess, 'Popen', return_value=process) as popen, \
             mock.patch.object(prerequisite.os, 'killpg') as killpg, self.assertRaises(ValueError):
            prerequisite._bounded_command(['compiler', 'args'], log, time.monotonic() + 1, {'GOFLAGS': ''})
        self.assertTrue(popen.call_args.kwargs['start_new_session'])
        self.assertIs(popen.call_args.kwargs['stderr'], subprocess.STDOUT)
        killpg.assert_called_once_with(process.pid, signal.SIGKILL)
        status = json.loads(log.with_name(log.stem + '-status.json').read_text())
        self.assertEqual(status['returncode'], -9)
        self.assertIs(status['timed_out'], True)
        self.assertEqual(status['command'], ['compiler', 'args'])

    def test_untracked_compiler_input_blocks_every_build_stage(self):
        self.untracked.side_effect = ValueError('untracked compiler input')
        with mock.patch.object(prerequisite, '_bounded_command') as bounded, self.assertRaises(ValueError):
            prerequisite.prepare(self.directory, self.directory, ['TestOne'], {})
        bounded.assert_not_called()
        self.assertFalse((self.directory / 'prerequisite-status.json').exists())

    def test_expired_total_budget_never_launches_another_stage(self):
        with mock.patch.object(prerequisite.subprocess, 'Popen') as popen, self.assertRaises(ValueError):
            prerequisite._bounded_command(['compiler'], self.directory / 'next.log', time.monotonic() - 1, {})
        popen.assert_not_called()

    def test_failed_and_successful_processes_record_actual_exit_and_arguments(self):
        for code in (0, 73):
            process = mock.Mock()
            process.wait.return_value = code
            log = self.directory / 'root-harness-build.log'
            with mock.patch.object(prerequisite.subprocess, 'Popen', return_value=process), \
                 mock.patch.object(prerequisite.os, 'killpg') as killpg:
                if code:
                    with self.assertRaises(ValueError):
                        prerequisite._bounded_command(['go', 'test', '-c', '-race'], log, time.monotonic() + 5, {})
                else:
                    prerequisite._bounded_command(['go', 'test', '-c', '-race'], log, time.monotonic() + 5, {})
            killpg.assert_called_once_with(process.pid, signal.SIGKILL)
            status = json.loads(log.with_name(log.stem + '-status.json').read_text())
            self.assertEqual(status['returncode'], code)
            self.assertIs(status['timed_out'], False)

    @unittest.skipUnless(hasattr(os, 'fork'), 'requires POSIX process groups')
    def test_successful_producer_cannot_leave_a_child_to_publish_late_evidence(self):
        log = self.directory / 'native-prover-build.log'
        late_receipt = self.directory / 'late-success.json'
        source = (_FORK_DESCENDANT_SOURCE +
                  " time.sleep(2)\n pathlib.Path(sys.argv[1]).write_text('late success')\n")
        with _FixtureDescendant(self) as descendant:
            with mock.patch.object(prerequisite.subprocess, 'Popen', side_effect=descendant.launch):
                status = prerequisite._bounded_command([sys.executable, '-c', source, str(late_receipt)],
                                                        log, time.monotonic() + 5, dict(os.environ))
            descendant.observe(log.read_text())
            self.assertEqual(status['returncode'], 0)
            self.assertIs(status['timed_out'], False)
            descendant.assert_stopped('producer descendant survived group cleanup')
            self.assertFalse(late_receipt.exists())

    def test_producer_exception_still_kills_group_and_reaps_leader(self):
        process = mock.Mock(pid=424243)
        process.wait.side_effect = [OSError('failed wait'), -9]
        with mock.patch.object(prerequisite.subprocess, 'Popen', return_value=process), \
             mock.patch.object(prerequisite.os, 'killpg') as killpg, \
             self.assertRaisesRegex(OSError, 'failed wait'):
            prerequisite._bounded_command(['compiler'], self.directory / 'failed.log', time.monotonic() + 5, {})
        killpg.assert_called_once_with(process.pid, signal.SIGKILL)
        self.assertEqual(process.wait.call_count, 2)
        self.assertEqual(process.wait.call_args, mock.call(timeout=5))
        self.assertFalse((self.directory / 'failed-status.json').exists())


class RuntimeProcessGroupTests(unittest.TestCase):
    @unittest.skipUnless(hasattr(os, 'fork'), 'requires POSIX process groups')
    def test_orphan_holding_stdout_is_killed_by_wall_deadline(self):
        self.check_orphan(hold_stdout=True)

    @unittest.skipUnless(hasattr(os, 'fork'), 'requires POSIX process groups')
    def test_successful_leader_cannot_leave_a_running_descendant(self):
        self.check_orphan(hold_stdout=False)

    def check_orphan(self, hold_stdout):
        source = (_FORK_DESCENDANT_SOURCE +
                  " " + ("pass" if hold_stdout else "os.close(1)") +
                  "\n time.sleep(60)\n")
        with _FixtureDescendant(self) as descendant:
            process = descendant.launch([sys.executable, '-c', source], stdout=subprocess.PIPE,
                                        text=True, start_new_session=True)
            watcher = prerequisite.RuntimeDeadline(process, 0.5)
            try:
                with watcher:
                    descendant.observe(process.stdout.readline())
                    # The leader has exited; only the descendant can hold this pipe.
                    self.assertEqual(process.stdout.read(), '')
                    self.assertEqual(process.wait(timeout=2), 0)
            finally:
                process.stdout.close()
            self.assertEqual(watcher.timed_out.is_set(), hold_stdout)
            self.assertLess(watcher.elapsed_seconds, 3)
            descendant.assert_stopped('descendant survived group cleanup')

    def test_exception_also_kills_group_and_reaps_leader(self):
        process = mock.Mock(pid=987654)
        with mock.patch.object(prerequisite.os, 'killpg') as killpg, self.assertRaisesRegex(ValueError, 'broken stream'):
            with prerequisite.RuntimeDeadline(process, 5):
                raise ValueError('broken stream')
        killpg.assert_called_once_with(process.pid, signal.SIGKILL)
        process.wait.assert_called_once_with(timeout=5)


class UntrackedSourceTests(unittest.TestCase):
    def test_compiler_and_embed_input_suffixes_fail_closed(self):
        for name in ('root.go', 'helper.s', 'helper.S', 'native.c', 'header.h', 'solver.oak',
                     'nested/go.mod', 'nested/go.sum', 'embedded.txt', 'results-copy/file.json'):
            with self.subTest(name=name), \
                 mock.patch.object(prerequisite.subprocess, 'check_output', return_value=name.encode()+b'\0'), \
                 self.assertRaises(ValueError):
                prerequisite.check_untracked_inputs(Path('.'), Path('results'), 10)
        for raw in (b'', b'results/log.txt\0', b'results/identity.json\0'):
            with mock.patch.object(prerequisite.subprocess, 'check_output', return_value=raw):
                prerequisite.check_untracked_inputs(Path('.'), Path('results'), 10)


class SuppliedUnitEvidenceTests(unittest.TestCase):
    """Synthetic identities exercise v2 without inventing the reviewed inventory."""
    def setUp(self):
        self.counts = {'eligible': 3, 'supplied': 2, 'externs': 1}
        self.enterContext(mock.patch.object(prerequisite, 'REVIEWED_INVENTORY_COUNTS', self.counts))
        def declaration(name, extern_symbol=''):
            return dict(name=name, source_sha256=hashlib.sha256(name.encode()).hexdigest(),
                        extern_symbol=extern_symbol)
        self.inventory = dict(
            eligible=[declaration(name) for name in ('ordinary', 'witness', 'fallback')],
            supplied=[dict(input=declaration(name), arch='arm64',
                           body_sha256=hashlib.sha256((name + ' body').encode()).hexdigest())
                      for name in ('guard_one', 'guard_two')],
            externs=[declaration('external', 'write')])
        functions = []
        for item in self.inventory['eligible']:
            candidate = dict(name='fixture candidate', body_sha256='a' * 64,
                             recipe_sha256='b' * 64, outcome='proven',
                             message='fixture proof', cached=False)
            functions.append(dict(input=copy.deepcopy(item), status='proven', reason='fixture proof',
                                  callees=[], considered=1, materialized=1,
                                  selected=copy.deepcopy(candidate), validations=[candidate]))
        self.report = dict(schema_version=2, inventory=copy.deepcopy(self.inventory), functions=functions,
                           supplied=[dict(**copy.deepcopy(item), status='proven',
                                          reason='fixture actual supplied proof', callees=[])
                                     for item in self.inventory['supplied']])

    def validate(self, report=None, inventory=None):
        prerequisite._report(self.report if report is None else report,
                             self.inventory if inventory is None else inventory)

    def test_supplied_verdicts_preserve_status_without_optimizer_records(self):
        self.assertEqual(prerequisite._inventory(self.inventory), self.inventory)
        for status in ('proven', 'witnessed', 'trusted'):
            report = copy.deepcopy(self.report)
            report['supplied'][0].update(status=status, reason='actual ' + status,
                                         callees=['ordinary', 'guard_two', 'external'])
            report['functions'][0]['callees'] = ['guard_one', 'guard_two']
            report['functions'][2].update(status='c-fallback', reason='unsupported lowering',
                                          selected=None, validations=[])
            with self.subTest(status=status):
                self.validate(report)

    def test_report_schema_is_exact_and_rejects_legacy_versions(self):
        for version in (None, True, False, 1, 2.0, '2', 3):
            report = copy.deepcopy(self.report)
            report['schema_version'] = version
            with self.subTest(version=version), self.assertRaises(ValueError):
                self.validate(report)
        for field in self.report:
            report = copy.deepcopy(self.report)
            del report[field]
            with self.subTest(missing=field), self.assertRaises(ValueError):
                self.validate(report)
        report = dict(self.report, unexpected=[])
        with self.assertRaises(ValueError):
            self.validate(report)

    def test_unreviewed_count_prevents_manifest_acceptance(self):
        for kind in self.counts:
            counts = dict(self.counts, **{kind: None})
            with self.subTest(kind=kind), \
                 mock.patch.object(prerequisite, 'REVIEWED_INVENTORY_COUNTS', counts), \
                 self.assertRaisesRegex(ValueError, 'await fresh frontend generation and review'):
                self.validate()

    def test_inventory_counts_fields_and_declaration_names_fail_closed(self):
        for kind in self.inventory:
            for mutation in ('missing', 'extra', 'duplicate', 'not-list'):
                inventory = copy.deepcopy(self.inventory)
                if mutation == 'missing':
                    inventory[kind].pop()
                elif mutation == 'extra':
                    inventory[kind].append(copy.deepcopy(inventory[kind][0]))
                elif mutation == 'duplicate':
                    if len(inventory[kind]) == 1:
                        inventory[kind][0]['name'] = inventory['eligible'][0]['name']
                    else:
                        inventory[kind][1] = copy.deepcopy(inventory[kind][0])
                else:
                    inventory[kind] = {}
                with self.subTest(kind=kind, mutation=mutation), self.assertRaises(ValueError):
                    prerequisite._inventory(inventory)
        for target in ('eligible', 'externs'):
            inventory = copy.deepcopy(self.inventory)
            inventory['supplied'][0]['input']['name'] = inventory[target][0]['name']
            with self.subTest(collision=target), self.assertRaises(ValueError):
                prerequisite._inventory(inventory)
        for field in self.inventory:
            inventory = copy.deepcopy(self.inventory)
            del inventory[field]
            with self.subTest(missing_field=field), self.assertRaises(ValueError):
                prerequisite._inventory(inventory)
        with self.assertRaises(ValueError):
            prerequisite._inventory(dict(self.inventory, unexpected=[]))

    def test_supplied_inventory_identity_and_target_are_strict(self):
        for field, value in (('arch', 'rv64'), ('arch', ''), ('body_sha256', ''),
                             ('body_sha256', 'g' * 64), ('body_sha256', True)):
            inventory = copy.deepcopy(self.inventory)
            inventory['supplied'][0][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                prerequisite._inventory(inventory)
        for field, value in (('name', ''), ('name', True), ('source_sha256', 'bad'),
                             ('extern_symbol', 'write'), ('extern_symbol', False)):
            inventory = copy.deepcopy(self.inventory)
            inventory['supplied'][0]['input'][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                prerequisite._inventory(inventory)
        for field in self.inventory['supplied'][0]:
            inventory = copy.deepcopy(self.inventory)
            del inventory['supplied'][0][field]
            with self.subTest(missing=field), self.assertRaises(ValueError):
                prerequisite._inventory(inventory)
        for field in ('input', 'body_sha256'):
            inventory = copy.deepcopy(self.inventory)
            inventory['supplied'][0]['input' if field == 'input' else 'body_sha256'] = None
            with self.subTest(null=field), self.assertRaises(ValueError):
                prerequisite._inventory(inventory)
        inventory = copy.deepcopy(self.inventory)
        inventory['supplied'][0]['system'] = True
        with self.assertRaises(ValueError):
            prerequisite._inventory(inventory)

    def test_supplied_report_count_order_identity_status_and_callees_fail_closed(self):
        mutations = ('missing', 'extra', 'duplicate', 'reordered', 'not-list',
                     'wrong-name', 'wrong-source', 'wrong-extern', 'wrong-arch', 'wrong-body',
                     'unfinished', 'error', 'mismatch', 'refused', 'c-fallback', 'invalid-status',
                     'empty-reason', 'invalid-reason', 'missing-callees', 'not-list-callees',
                     'unknown-callee', 'duplicate-callee', 'empty-callee', 'invalid-callee',
                     'forged-selected', 'forged-validations', 'forged-considered', 'forged-cached',
                     'forged-system-flag', 'reclassified', 'changed-inventory')
        for mutation in mutations:
            report = copy.deepcopy(self.report)
            row = report['supplied'][0]
            if mutation == 'missing':
                report['supplied'].pop()
            elif mutation == 'extra':
                report['supplied'].append(copy.deepcopy(row))
            elif mutation == 'duplicate':
                report['supplied'][1] = copy.deepcopy(row)
            elif mutation == 'reordered':
                report['supplied'].reverse()
            elif mutation == 'not-list':
                report['supplied'] = {}
            elif mutation == 'wrong-name':
                row['input']['name'] = 'other'
            elif mutation == 'wrong-source':
                row['input']['source_sha256'] = '0' * 64
            elif mutation == 'wrong-extern':
                row['input']['extern_symbol'] = 'write'
            elif mutation == 'wrong-arch':
                row['arch'] = 'rv64'
            elif mutation == 'wrong-body':
                row['body_sha256'] = '0' * 64
            elif mutation in ('unfinished', 'error', 'mismatch', 'refused', 'c-fallback'):
                row['status'] = mutation
            elif mutation == 'invalid-status':
                row['status'] = True
            elif mutation == 'empty-reason':
                row['reason'] = ''
            elif mutation == 'invalid-reason':
                row['reason'] = False
            elif mutation == 'missing-callees':
                del row['callees']
            elif mutation == 'not-list-callees':
                row['callees'] = None
            elif mutation == 'unknown-callee':
                row['callees'] = ['absent']
            elif mutation == 'duplicate-callee':
                row['callees'] = ['external', 'external']
            elif mutation == 'empty-callee':
                row['callees'] = ['']
            elif mutation == 'invalid-callee':
                row['callees'] = [False]
            elif mutation == 'forged-selected':
                row['selected'] = copy.deepcopy(report['functions'][0]['selected'])
            elif mutation == 'forged-validations':
                row['validations'] = []
            elif mutation == 'forged-considered':
                row['considered'] = 0
            elif mutation == 'forged-cached':
                row['cached'] = False
            elif mutation == 'forged-system-flag':
                row['system'] = True
            elif mutation == 'reclassified':
                row['input'] = copy.deepcopy(self.inventory['eligible'][0])
            else:
                report['inventory']['supplied'][0]['body_sha256'] = '0' * 64
                row['body_sha256'] = '0' * 64
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                self.validate(report)

    def test_supplied_report_missing_identity_fields_fail_closed(self):
        for field in self.report['supplied'][0]:
            report = copy.deepcopy(self.report)
            del report['supplied'][0][field]
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.validate(report)

    def test_supplied_units_do_not_replace_required_optimizer_native_selection(self):
        report = copy.deepcopy(self.report)
        for row in report['functions']:
            row.update(status='c-fallback', selected=None, validations=[])
        with self.assertRaisesRegex(ValueError, 'C-only substitution'):
            self.validate(report)


class SuppliedSourceEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.repo = Path(self.enterContext(tempfile.TemporaryDirectory()))
        (self.repo / 'prove/solver').mkdir(parents=True)
        for name in prerequisite.SOLVER_SOURCE_NAMES:
            (self.repo / 'prove/solver' / name).write_bytes(('fixture source ' + name).encode())
        (self.repo / 'oaksolver.go').write_text('const oakSolverDriverSource = `fixture driver`\n')

    def test_complete_source_map_binds_both_selected_and_foreign_lanes(self):
        sources = prerequisite.source_bytes(self.repo)
        self.assertEqual(len(sources), 19)
        self.assertEqual(set(sources), set(prerequisite.SOURCE_NAMES))
        self.assertEqual({name for name in sources if name.endswith('.oakasm')},
                         {'lrat.arm64.oakasm', 'lrat.rv64.oakasm'})
        self.assertEqual(prerequisite.native_files(),
                         {'recipe.json', 'report.json', 'success.json', 'program.c', 'asm.o', 'solver'}
                         | {'source/' + name for name in sources})
        for name in ('lrat.arm64.oakasm', 'lrat.rv64.oakasm'):
            original = sources[name]
            path = self.repo / 'prove/solver' / name
            path.write_bytes(original + b'\n  system\n')
            changed = prerequisite.source_bytes(self.repo)
            self.assertNotEqual(hashlib.sha256(changed[name]).digest(), hashlib.sha256(original).digest())
            self.assertEqual({key for key in sources if changed[key] != sources[key]}, {name})
            path.write_bytes(original)

    def test_neither_architecture_source_may_be_missing(self):
        for name in ('lrat.arm64.oakasm', 'lrat.rv64.oakasm'):
            path = self.repo / 'prove/solver' / name
            original = path.read_bytes()
            path.unlink()
            with self.subTest(name=name), self.assertRaises(OSError):
                prerequisite.source_bytes(self.repo)
            path.write_bytes(original)


if __name__ == '__main__':
    unittest.main()
