"""Runner deadline and process evidence tests; no Oak/native builds are run."""
import io
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
        source = ("import os,time,pathlib,sys\n"
                  "child=os.fork()\n"
                  "if child:\n print(child,flush=True)\n os._exit(0)\n"
                  "else:\n time.sleep(2)\n pathlib.Path(sys.argv[1]).write_text('late success')\n")
        status = prerequisite._bounded_command([sys.executable, '-c', source, str(late_receipt)],
                                                log, time.monotonic() + 5, dict(os.environ))
        self.assertEqual(status['returncode'], 0)
        self.assertIs(status['timed_out'], False)
        child = int(log.read_text())
        deadline = time.monotonic() + 1
        while True:
            try:
                state = Path(f'/proc/{child}/stat').read_text().split()[2]
            except (FileNotFoundError, ProcessLookupError):
                break
            if state == 'Z':
                break
            if time.monotonic() >= deadline:
                self.fail('producer descendant survived group cleanup')
            time.sleep(0.005)
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
        source = ("import os,time\n"
                  "child=os.fork()\n"
                  "if child:\n print(child,flush=True)\n os._exit(0)\n"
                  "else:\n " + ("pass" if hold_stdout else "os.close(1)") +
                  "\n time.sleep(60)\n")
        process = subprocess.Popen([sys.executable, '-c', source], stdout=subprocess.PIPE,
                                   text=True, start_new_session=True)
        watcher = prerequisite.RuntimeDeadline(process, 0.5)
        try:
            with watcher:
                child = int(process.stdout.readline())
                # The leader has exited; only the descendant can hold this pipe.
                self.assertEqual(process.stdout.read(), '')
                self.assertEqual(process.wait(timeout=2), 0)
        finally:
            process.stdout.close()
        self.assertEqual(watcher.timed_out.is_set(), hold_stdout)
        self.assertLess(watcher.elapsed_seconds, 3)
        deadline = time.monotonic() + 1
        while True:
            try:
                state = Path(f'/proc/{child}/stat').read_text().split()[2]
            except (FileNotFoundError, ProcessLookupError):
                break
            if state == 'Z':
                break
            if time.monotonic() >= deadline:
                self.fail('descendant survived group cleanup')
            # SIGKILL delivery is asynchronous for the already-orphaned child.
            time.sleep(0.005)

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


if __name__ == '__main__':
    unittest.main()
