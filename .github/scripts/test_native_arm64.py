import copy
from contextlib import ExitStack
import io
import json
from pathlib import Path
import re
import select
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

import native_arm64 as gate
import native_arm64_resources as resources


def event(action, name=None):
    result = {'Package': gate.MODULE + '/compiler', 'Action': action}
    if name is not None:
        result['Test'] = name
    return result


def passing_events():
    return [event('start'), event('run', 'TestOne'), event('run', 'TestOne/child'),
            event('pass', 'TestOne/child'), event('pass', 'TestOne'), event('pass')]


class ExecutionEvidenceTests(unittest.TestCase):
    def verify(self, events):
        return gate.validate_events(events, './compiler', ['TestOne'], {'TestOne': ['child']})

    def test_complete_pass(self):
        self.assertEqual(self.verify(passing_events()), ['TestOne', 'TestOne/child'])

    def test_every_root_and_child_must_run_and_pass_once(self):
        for index in range(1, 6):
            with self.subTest(index=index):
                events = passing_events()
                events.pop(index)
                with self.assertRaises(ValueError):
                    self.verify(events)
        for duplicate in (event('run', 'TestOne'), event('pass', 'TestOne'), event('pass')):
            with self.assertRaises(ValueError):
                self.verify(passing_events() + [duplicate])

    def test_skip_or_fail_is_never_a_pass(self):
        for action in ('skip', 'fail'):
            for name in (None, 'TestOne', 'TestOne/child'):
                with self.subTest(action=action, name=name), self.assertRaises(ValueError):
                    self.verify(passing_events() + [event(action, name)])

    def test_unknown_children_and_packages_fail(self):
        for extra in (event('pass', 'TestOther'), event('pass', 'TestOne/new_child'),
                      {'Action': 'pass', 'Package': gate.MODULE + '/other'}):
            with self.assertRaises(ValueError):
                self.verify(passing_events() + [extra])

    def test_malformed_and_empty_streams_fail(self):
        for events in ([], [None], [{}], [{'Action': 3}]):
            with self.assertRaises(ValueError):
                self.verify(events)

    def test_selector_is_exact_and_rejects_empty_or_duplicate(self):
        pattern = gate.pattern(['TestOne', 'TestTwo'])
        self.assertTrue(re.search(pattern, 'TestOne'))
        self.assertFalse(re.search(pattern, 'TestOneMore'))
        for names in ([], ['TestOne', 'TestOne']):
            with self.assertRaises(ValueError):
                gate.pattern(names)

    def test_nonzero_exit_and_bad_json_fail_even_with_pass_events(self):
        valid = '\n'.join(map(json.dumps, passing_events())) + '\n'
        for stream, status in ((valid, 1), (valid + 'not JSON\n', 0)):
            with self.subTest(status=status), tempfile.TemporaryDirectory() as directory:
                process = mock.Mock(stdout=io.StringIO(stream))
                process.wait.return_value = status
                with mock.patch.object(gate.subprocess, 'Popen', return_value=process), self.assertRaises(ValueError):
                    gate.run_package('./compiler', ['TestOne'], {'TestOne': ['child']}, Path(directory))
                self.assertFalse(list(Path(directory).glob('*-passed.json')))
                self.assertEqual((Path(directory) / 'compiler.jsonl').read_text(), stream)
                receipt = json.loads((Path(directory) / 'compiler-status.json').read_text())
                self.assertEqual(receipt['returncode'], status)
                self.assertEqual(receipt['command'][:5], ['go', 'test', '-json', '-race', '-count=1'])

    def test_run_preserves_race_timeout_and_uncached_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            process = mock.Mock(stdout=io.StringIO('\n'.join(map(json.dumps, passing_events())) + '\n'))
            process.wait.return_value = 0
            with mock.patch.object(gate.subprocess, 'Popen', return_value=process) as popen:
                gate.run_package('./compiler', ['TestOne'], {'TestOne': ['child']}, Path(directory))
            command = popen.call_args.args[0]
            self.assertEqual(command[:9], ['go', 'test', '-json', '-race', '-count=1', '-timeout', '90m', '-p', '1'])
            self.assertEqual(popen.call_args.kwargs['env']['GOFLAGS'], '')
            self.assertTrue((Path(directory) / 'compiler-passed.json').exists())

    def test_root_runtime_uses_persisted_harness_exact_test2json_flags_and_environment(self):
        for changed in (False, True):
            with self.subTest(changed=changed), tempfile.TemporaryDirectory() as temporary:
                directory = Path(temporary)
                (directory / 'identity.json').write_text('{}')
                harness = directory / gate.prerequisite.HARNESS
                harness.write_bytes(b'original race harness')
                native = directory / gate.prerequisite.NATIVE
                native.mkdir()
                (native / 'success.json').write_text('{}')
                prepared = {'directory': str(directory),
                            'harness_sha256': gate.prerequisite.digest(harness),
                            'success_sha256': gate.prerequisite.digest(native / 'success.json')}
                events = [{'Package': gate.MODULE, 'Action': 'start'},
                          {'Package': gate.MODULE, 'Action': 'run', 'Test': 'TestOne'},
                          {'Package': gate.MODULE, 'Action': 'pass', 'Test': 'TestOne'},
                          {'Package': gate.MODULE, 'Action': 'pass'}]
                process = mock.Mock(stdout=io.StringIO(''.join(json.dumps(e)+'\n' for e in events)))
                def finish(*args, **kwargs):
                    if changed:
                        harness.write_bytes(b'replaced race harness')
                    return 0
                process.wait.side_effect = finish
                with mock.patch.object(gate.prerequisite, 'validate', return_value=prepared), \
                     mock.patch.object(gate.subprocess, 'Popen', return_value=process) as popen, \
                     mock.patch.object(gate.prerequisite.os, 'killpg') as killpg:
                    if changed:
                        with self.assertRaisesRegex(ValueError, 'changed during root runtime'):
                            gate.run_package('.', ['TestOne'], {}, directory)
                    else:
                        gate.run_package('.', ['TestOne'], {}, directory)
                self.assertTrue(popen.call_args.kwargs['start_new_session'])
                killpg.assert_called_once()
                self.assertEqual(popen.call_args.args[0],
                                 ['go', 'tool', 'test2json', '-t', '-p', gate.MODULE, '--', str(harness),
                                  '-test.v=test2json', '-test.count=1', '-test.timeout=45m', '-test.run=^(TestOne)$'])
                self.assertEqual(popen.call_args.kwargs['env']['OAK_NATIVE_PREREQUISITE'], str(native))
                self.assertEqual((directory / 'root-passed.json').exists(), not changed)

    def test_live_inventory_mismatch_and_subprocess_error_fail(self):
        result = mock.Mock(stdout='TestOneMore\nok\n')
        with mock.patch.object(gate.subprocess, 'run', return_value=result), self.assertRaises(ValueError):
            gate.check_live_roots('./compiler', ['TestOne'])
        failure = gate.subprocess.CalledProcessError(1, ['go'])
        with mock.patch.object(gate.subprocess, 'run', side_effect=failure), self.assertRaises(type(failure)):
            gate.check_live_roots('./compiler', ['TestOne'])

    def test_x86_host_refused_before_starting_tests(self):
        with mock.patch.object(gate.platform, 'system', return_value='Linux'), \
             mock.patch.object(gate.platform, 'machine', return_value='x86_64'), \
             mock.patch.object(gate.subprocess, 'check_output') as command, self.assertRaises(ValueError):
            gate.preflight()
        command.assert_not_called()

    def test_wrong_target_or_no_cgo_is_refused(self):
        for env in (dict(GOHOSTARCH='amd64'), dict(GOHOSTARCH='arm64', GOARCH='arm64', GOHOSTOS='linux', GOOS='linux', CGO_ENABLED='0')):
            with mock.patch.object(gate.platform, 'system', return_value='Linux'), \
                 mock.patch.object(gate.platform, 'machine', return_value='aarch64'), \
                 mock.patch.object(gate.subprocess, 'check_output', return_value=json.dumps(env)), self.assertRaises(ValueError):
                gate.preflight()

    def test_compiler_or_execution_failure_is_not_skipped(self):
        env = dict(GOHOSTARCH='arm64', GOARCH='arm64', GOHOSTOS='linux', GOOS='linux', CGO_ENABLED='1')
        for responses in ([FileNotFoundError('cc')], [mock.Mock(), gate.subprocess.CalledProcessError(1, ['smoke'])]):
            with mock.patch.object(gate.platform, 'system', return_value='Linux'), \
                 mock.patch.object(gate.platform, 'machine', return_value='aarch64'), \
                 mock.patch.object(gate.subprocess, 'check_output', return_value=json.dumps(env)), \
                 mock.patch.object(gate.subprocess, 'run', side_effect=responses), self.assertRaises((OSError, gate.subprocess.CalledProcessError)):
                gate.preflight()


class SourceInventoryTests(unittest.TestCase):
    def setUp(self):
        self.manifest = json.loads(gate.MANIFEST.read_text())
        self.source = {'roots': [], 'skips': []}
        for package, roots in self.manifest['roots'].items():
            self.source['roots'] += [dict(package=package, test=test, file=file) for test, file in roots.items()]
        for key, calls in self.manifest['skip_sites'].items():
            file, function = key.split('::')
            self.source['skips'] += [dict(file=file, function=function, call=call) for call in calls]

    def test_exact_coverage_and_platform_exclusions(self):
        selected = gate.check_inventory(self.manifest, self.source)
        self.assertEqual({p: len(n) for p, n in selected.items()}, {'.': 2, './asm': 1, './compiler': 193, './testrunner': 1, './semir': 1})
        self.assertEqual(sum(len(c) for roots in self.manifest['children'].values() for c in roots.values()), 61)
        for package, name in gate.EXCLUSIONS:
            self.assertNotIn(name, selected[package])

    def test_added_removed_root_or_new_skip_site_requires_review(self):
        for mutation in ('add-root', 'remove-root', 'add-skip'):
            source = copy.deepcopy(self.source)
            if mutation == 'add-root':
                source['roots'].append(dict(package='./compiler', test='TestFutureNative', file='compiler/future_test.go'))
            elif mutation == 'remove-root':
                source['roots'].pop()
            else:
                source['skips'].append(dict(file='compiler/future_test.go', function='TestFuture', call='t.Skip("needs native host")'))
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                gate.check_inventory(self.manifest, source)

    def test_stale_exclusion_and_unknown_child_root_are_rejected(self):
        with mock.patch.dict(gate.EXCLUSIONS, {('./compiler', 'TestMissing'): 'platform'}, clear=False), self.assertRaises(ValueError):
            gate.check_inventory(self.manifest, self.source)
        self.manifest['children']['./compiler']['TestMissing'] = ['child']
        with self.assertRaises(ValueError):
            gate.check_inventory(self.manifest, self.source)


class ShardExecutionTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name) / 'results'
        self.manifest = json.loads(gate.MANIFEST.read_text())
        self.source = {'roots': [], 'skips': []}
        for package, roots in self.manifest['roots'].items():
            self.source['roots'].extend(dict(package=package, test=name, file=file)
                                       for name, file in roots.items())
        for location, calls in self.manifest['skip_sites'].items():
            file, function = location.split('::')
            self.source['skips'].extend(dict(file=file, function=function, call=call) for call in calls)
        self.stack = self.enterContext(ExitStack())
        self.stack.enter_context(mock.patch.object(gate.os, 'chdir'))
        self.stack.enter_context(mock.patch.object(gate.subprocess, 'run',
                                 return_value=mock.Mock(stdout=json.dumps(self.source))))
        self.stack.enter_context(mock.patch.object(gate, 'identity', return_value={'fixture': True}))
        self.preflight = self.stack.enter_context(mock.patch.object(gate, 'preflight'))
        self.live = self.stack.enter_context(mock.patch.object(gate, 'check_live_roots'))
        self.run = self.stack.enter_context(mock.patch.object(gate, 'run_package'))
        self.prepare = self.stack.enter_context(mock.patch.object(gate.prerequisite, 'prepare'))

    def execute(self, shard, check=False):
        gate.execute(SimpleNamespace(check=check, shard=shard, results_dir=self.directory))

    def test_every_shard_runs_only_its_own_roots_and_children(self):
        selected = gate.select_tests(self.manifest)
        shards = gate.load_shards(selected, self.manifest, gate.PLAN)
        for shard, packages in shards.items():
            with self.subTest(shard=shard):
                self.directory = Path(self.temporary.name) / shard
                self.run.reset_mock()
                self.preflight.reset_mock()
                self.execute(shard)
                self.preflight.assert_called_once_with()
                expected = []
                for package in gate.TIMEOUTS:
                    if package in packages:
                        roots = packages[package]
                        children = {root: names for root, names in self.manifest['children'].get(package, {}).items()
                                    if root in roots}
                        expected.append(mock.call(package, roots, children, self.directory))
                self.assertEqual(self.run.call_args_list, expected)
                receipt = json.loads((self.directory / 'lane-result.json').read_text())
                self.assertEqual(receipt, dict(schema_version=1, shard=shard, success=True, packages=sorted(packages)))

    def test_source_check_and_bad_shard_never_execute(self):
        self.execute(None, check=True)
        with self.assertRaises(ValueError):
            self.execute('unreviewed')
        self.preflight.assert_not_called()
        self.run.assert_not_called()
        self.assertFalse(self.directory.exists())

    def test_stale_results_directory_never_reuses_a_receipt(self):
        self.directory.mkdir()
        (self.directory / 'lane-result.json').write_text('{}')
        with self.assertRaisesRegex(ValueError, 'must be empty'):
            self.execute('support')
        self.preflight.assert_not_called()
        self.run.assert_not_called()

    def test_preflight_failure_cannot_write_success_receipt(self):
        self.preflight.side_effect = ValueError('wrong host')
        with self.assertRaises(ValueError):
            self.execute('compiler-a')
        self.run.assert_not_called()
        self.assertFalse((self.directory / 'lane-result.json').exists())

    def test_support_collects_failures_but_never_writes_success(self):
        self.run.side_effect = [ValueError('failure'), None, None, None]
        with self.assertRaises(ValueError):
            self.execute('support')
        self.assertEqual([call.args[0] for call in self.run.call_args_list], ['./semir', '.', './asm', './testrunner'])
        self.assertFalse((self.directory / 'lane-result.json').exists())

    def test_live_selector_failure_is_fatal_and_remaining_support_runs(self):
        self.live.side_effect = [ValueError('missing tool child'), None, None, None]
        with self.assertRaises(ValueError):
            self.execute('support')
        self.assertEqual([call.args[0] for call in self.run.call_args_list], ['.', './asm', './testrunner'])
        self.assertFalse((self.directory / 'lane-result.json').exists())

    def test_prerequisite_failure_blocks_root_but_keeps_independent_support(self):
        self.prepare.side_effect = ValueError('native prerequisite failed')
        with self.assertRaisesRegex(ValueError, 'native prerequisite failed'):
            self.execute('support')
        self.assertEqual([call.args[0] for call in self.run.call_args_list],
                         ['./semir', './asm', './testrunner'])
        self.assertEqual([call.args[0] for call in self.live.call_args_list],
                         ['./semir', './asm', './testrunner'])
        self.assertFalse((self.directory / 'lane-result.json').exists())

    def test_support_prepares_one_harness_before_any_runtime(self):
        order = []
        self.prepare.side_effect = lambda *args: order.append('prepare')
        self.run.side_effect = lambda package, *args: order.append(package)
        self.execute('support')
        self.assertEqual(order, ['prepare', './semir', '.', './asm', './testrunner'])
        self.assertNotIn('.', [call.args[0] for call in self.live.call_args_list])
        self.prepare.assert_called_once()

    def test_run_requires_explicit_shard_and_check_is_global(self):
        for argv in (['--run'], ['--check', '--shard', 'support']):
            with mock.patch.object(sys, 'argv', ['native_arm64.py'] + argv), \
                 mock.patch.object(sys, 'stderr', io.StringIO()), self.assertRaises(SystemExit):
                gate.main()


class WorkflowContractTests(unittest.TestCase):
    def test_native_matrix_is_bounded_and_retains_required_aggregate(self):
        # No YAML dependency is needed by the native guard. actionlint separately
        # checks the parsed workflow; these assertions pin the critical wiring.
        workflow = (gate.REPO / '.github/workflows/native-arm64.yml').read_text()
        native, aggregate = workflow.split('  host-tests:', 1)
        self.assertIn('shard: [support, compiler-a, compiler-b, compiler-c]', native)
        self.assertIn('fail-fast: false', native)
        self.assertIn('max-parallel: 2', native)
        self.assertIn('runs-on: ubuntu-24.04-arm', native)
        self.assertIn('timeout-minutes: 240', native)
        self.assertIn('group: ${{ github.workflow }}-host-tests-${{ matrix.shard }}-', native)
        self.assertIn("--run --shard '${{ matrix.shard }}'", native)
        self.assertIn('name: native-arm64-${{ github.run_id }}-${{ github.run_attempt }}-${{ matrix.shard }}', native)
        self.assertIn('if-no-files-found: error', native)
        self.assertNotIn('continue-on-error:', native)
        self.assertIn('name: Native ARM64 host tests', aggregate)
        self.assertIn('needs: native-shards', aggregate)
        self.assertEqual(aggregate.count('if: ${{ always() }}'), 2)
        self.assertIn('MATRIX_RESULT: ${{ needs.native-shards.result }}', aggregate)
        self.assertIn('DOWNLOAD_OUTCOME: ${{ steps.evidence.outcome }}', aggregate)
        self.assertIn('merge-multiple: false', aggregate)
        self.assertIn('--matrix-result "$MATRIX_RESULT" || status=$?', aggregate)
        self.assertIn('if [ "$DOWNLOAD_OUTCOME" != success ]; then', aggregate)
        self.assertIn('exit "$status"', aggregate)


class ResourceTelemetryTests(unittest.TestCase):
    def test_sample_count_line_size_and_frequency_are_bounded(self):
        output = io.StringIO()
        with mock.patch.object(resources.os, 'getppid', return_value=42), \
             mock.patch.object(resources, 'snapshot', return_value={'mem_available_bytes': 123}) as snapshot, \
             mock.patch.object(resources.time, 'sleep') as sleep, \
             mock.patch.object(resources.sys, 'stderr', output):
            resources.sample(42, Path('.'))
        lines = output.getvalue().splitlines(keepends=True)
        self.assertEqual(len(lines), 481)
        self.assertEqual(snapshot.call_count, 481)
        self.assertEqual(sleep.call_args_list, [mock.call(30)] * 480)
        self.assertLess(len(output.getvalue().encode()), 1024 * 1024)
        for index, line in enumerate(lines):
            self.assertLessEqual(len(line.encode()), resources.MAX_LINE_BYTES)
            record = json.loads(line.removeprefix('NATIVE_ARM64_RESOURCE '))
            self.assertEqual(record['sample'], index + 1)
            self.assertRegex(record['timestamp'], r'^\d{4}-\d\d-\d\dT.*\+00:00$')

    def test_sampler_failure_and_oversize_output_stop_without_error_dump(self):
        for failure in (RuntimeError('private details'), {'bad': 'private details' * 300}):
            output = io.StringIO()
            kwargs = {'side_effect': failure} if isinstance(failure, Exception) else {'return_value': failure}
            with mock.patch.object(resources.os, 'getppid', return_value=42), \
                 mock.patch.object(resources, 'snapshot', **kwargs), \
                 mock.patch.object(resources.time, 'sleep') as sleep, \
                 mock.patch.object(resources.sys, 'stderr', output):
                resources.sample(42, Path('.'))
            self.assertEqual(len(output.getvalue().splitlines()), 1)
            self.assertIn('sampler_failed', output.getvalue())
            self.assertNotIn('private details', output.getvalue())
            sleep.assert_not_called()

    def test_closed_log_and_orphan_do_not_raise_or_keep_sampling(self):
        with mock.patch.object(resources.sys.stderr, 'write', side_effect=OSError('closed')):
            resources.notice('sampler_failed')
        with mock.patch.object(resources.os, 'getppid', return_value=1), \
             mock.patch.object(resources, 'snapshot') as snapshot:
            resources.sample(42, Path('.'))
        snapshot.assert_not_called()

    def test_start_failure_preserves_success_and_original_test_exit(self):
        for status in (None, 37):
            output = io.StringIO()
            with mock.patch.object(sys, 'argv', ['native_arm64.py', '--run', '--shard', 'support']), \
                 mock.patch.object(gate, 'execute', side_effect=None if status is None else SystemExit(status)) as execute, \
                 mock.patch.object(resources.subprocess, 'Popen', side_effect=OSError('private details')), \
                 mock.patch.object(resources.sys, 'stderr', output):
                if status is None:
                    self.assertIsNone(gate.main())
                else:
                    with self.assertRaises(SystemExit) as failure:
                        gate.main()
                    self.assertEqual(failure.exception.code, status)
                execute.assert_called_once()
            self.assertIn('sampler_start_failed', output.getvalue())
            self.assertNotIn('private details', output.getvalue())

    def test_source_only_check_does_not_launch_sampler(self):
        with mock.patch.object(sys, 'argv', ['native_arm64.py', '--check']), \
             mock.patch.object(gate, 'execute') as execute, \
             mock.patch.object(gate, 'ResourceTelemetry') as telemetry:
            gate.main()
        telemetry.assert_not_called()
        execute.assert_called_once()

    def test_live_sampler_is_reaped_on_success_or_test_exception(self):
        original_popen = subprocess.Popen
        def capture(*args, **kwargs):
            return original_popen(*args, **kwargs, stderr=subprocess.PIPE, text=True)
        for status in (None, 37):
            telemetry = resources.ResourceTelemetry(Path.cwd())
            with mock.patch.object(resources.subprocess, 'Popen', side_effect=capture):
                try:
                    with telemetry:
                        process = telemetry.process
                        self.assertIsNotNone(process)
                        self.assertTrue(select.select([process.stderr], [], [], 5)[0], 'sampler did not emit')
                        line = process.stderr.readline()
                        record = json.loads(line.removeprefix('NATIVE_ARM64_RESOURCE '))
                        self.assertIn('mem_available_bytes', record)
                        self.assertIn('runner_rss_bytes', record)
                        self.assertLessEqual(len(line.encode()), resources.MAX_LINE_BYTES)
                        if status is not None:
                            raise SystemExit(status)
                except SystemExit as error:
                    self.assertEqual(error.code, status)
            self.assertIsNotNone(process.poll())
            self.assertEqual(process.wait(timeout=1), 0)
            process.stderr.close()

    def test_already_failed_sampler_and_stubborn_sampler_are_reaped(self):
        with subprocess.Popen([sys.executable, '-c', 'raise SystemExit(73)']) as process:
            self.assertEqual(process.wait(timeout=5), 73)
            telemetry = resources.ResourceTelemetry(Path('.'))
            telemetry.process = process
            self.assertFalse(telemetry.__exit__(None, None, None))
            self.assertEqual(process.returncode, 73)
        process = mock.Mock()
        process.wait.side_effect = [subprocess.TimeoutExpired('sampler', 1), -9]
        telemetry.process = process
        self.assertFalse(telemetry.__exit__(SystemExit, SystemExit(37), None))
        process.terminate.assert_called_once()
        process.kill.assert_called_once()
        self.assertEqual(process.wait.call_args_list, [mock.call(timeout=1), mock.call(timeout=1)])

    def test_cleanup_failure_never_replaces_test_error(self):
        process = mock.Mock()
        process.wait.side_effect = OSError('private details')
        telemetry = resources.ResourceTelemetry(Path('.'))
        telemetry.process = process
        output = io.StringIO()
        with mock.patch.object(resources.sys, 'stderr', output):
            self.assertFalse(telemetry.__exit__(SystemExit, SystemExit(37), None))
        process.kill.assert_called_once()
        self.assertIn('sampler_cleanup_failed', output.getvalue())
        self.assertNotIn('private details', output.getvalue())

    def test_process_rss_is_numeric_descendants_only_and_scan_is_capped(self):
        with tempfile.TemporaryDirectory() as directory:
            proc = Path(directory)
            for pid, parent, rss in ((10, 1, 10), (11, 10, 20), (12, 11, 30), (13, 1, 1000)):
                (proc / str(pid)).mkdir()
                (proc / str(pid) / 'status').write_text(
                    f'Name:\tprivate-name\nPPid:\t{parent}\nVmRSS:\t{rss} kB\n')
            with mock.patch.object(resources, 'PROC', proc):
                sample = resources.process_rss(10)
                self.assertEqual(sample['runner_rss_bytes'], 10 * 1024)
                self.assertEqual(sample['tree_rss_sum_bytes'], 60 * 1024)
                self.assertEqual(sample['tree_max_rss_bytes'], 30 * 1024)
                self.assertEqual(sample['tree_processes'], 3)
                self.assertNotIn('private-name', str(sample))
                with mock.patch.object(resources, 'MAX_PROCESSES', 2):
                    self.assertEqual(resources.process_rss(10)['process_scan'], 'capped')

    def test_cgroup_visible_ancestors_and_oom_counters(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            proc, mount = root / 'proc', root / 'cgroup'
            (proc / '10').mkdir(parents=True)
            (proc / 'self').mkdir()
            (proc / '10/cgroup').write_text('0::/runner/job\n')
            (proc / 'self/mountinfo').write_text(f'1 0 0:1 / {mount} rw - cgroup2 cgroup rw\n')
            # A genuine cgroup v2 root has no memory.current or memory.max.
            for suffix, current, maximum in (('runner', 500, '800'), ('runner/job', 300, '1000')):
                path = mount / suffix
                path.mkdir(parents=True, exist_ok=True)
                (path / 'memory.current').write_text(str(current))
                (path / 'memory.max').write_text(maximum)
            (mount / 'cgroup.controllers').write_text('memory\n')
            leaf = mount / 'runner/job'
            (leaf / 'memory.events').write_text('oom 3\noom_kill 2\noom_group_kill 1\n')
            with mock.patch.object(resources, 'PROC', proc):
                sample = resources.cgroup_memory(10)
                self.assertEqual(sample['cgroup_current_bytes'], 300)
                self.assertEqual(sample['cgroup_limit_bytes'], 1000)
                self.assertEqual(sample['cgroup_headroom_bytes'], 300)
                self.assertEqual(sample['cgroup_oom'], 3)
                self.assertEqual(sample['cgroup_oom_kill'], 2)
                self.assertEqual(sample['cgroup_oom_group_kill'], 1)
                # A partially missing root interface is not an unlimited root.
                (mount / 'memory.current').write_text('600')
                self.assertEqual(resources.cgroup_memory(10)['cgroup_headroom_bytes'], resources.UNSUPPORTED)
                (mount / 'memory.current').unlink()
                # Missing non-root ancestor accounting remains unsupported.
                (mount / 'runner/memory.current').unlink()
                self.assertEqual(resources.cgroup_memory(10)['cgroup_headroom_bytes'], resources.UNSUPPORTED)
                (mount / 'runner/memory.current').write_text('500')
                # A delegated mount must account for its boundary as well.
                (proc / 'self/mountinfo').write_text(f'1 0 0:1 /runner {mount / "runner"} rw - cgroup2 cgroup rw\n')
                self.assertEqual(resources.cgroup_memory(10)['cgroup_headroom_bytes'], 300)
                (mount / 'runner/memory.current').unlink()
                (mount / 'runner/memory.max').unlink()
                self.assertEqual(resources.cgroup_memory(10)['cgroup_headroom_bytes'], resources.UNSUPPORTED)
                (leaf / 'memory.events').unlink()
                self.assertEqual(resources.cgroup_memory(10)['cgroup_oom'], resources.UNSUPPORTED)
                (proc / '10/cgroup').write_text('5:memory:/legacy\n')
                self.assertTrue(all(value == resources.UNSUPPORTED for value in resources.cgroup_memory(10).values()))

    def test_unreadable_or_missing_mount_is_not_an_unlimited_root(self):
        with tempfile.TemporaryDirectory() as directory:
            mount = Path(directory)
            self.assertFalse(resources.root_without_memory_limit(Path('/'), mount))
            (mount / 'cgroup.controllers').write_text('memory\n')
            self.assertTrue(resources.root_without_memory_limit(Path('/'), mount))
            self.assertFalse(resources.root_without_memory_limit(Path('/delegated'), mount))
            self.assertFalse(resources.root_without_memory_limit(Path('/'), mount / 'gone'))
            (mount / 'cgroup.type').write_text('domain\n')
            self.assertFalse(resources.root_without_memory_limit(Path('/'), mount))
            (mount / 'cgroup.type').unlink()
            original_stat = Path.stat
            def unreadable(path, *args, **kwargs):
                if path == mount / 'memory.current':
                    raise PermissionError('unreadable')
                return original_stat(path, *args, **kwargs)
            with mock.patch.object(Path, 'stat', unreadable):
                self.assertFalse(resources.root_without_memory_limit(Path('/'), mount))

    def test_missing_fields_are_explicit_and_reads_are_bounded(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'meminfo').write_text('MemTotal: 100 kB\nSwapTotal: 0 kB\n')
            with mock.patch.object(resources, 'PROC', root), \
                 mock.patch.object(resources.os, 'statvfs', side_effect=OSError('missing')):
                sample = resources.snapshot(10, root)
            self.assertEqual(sample['mem_total_bytes'], 102400)
            self.assertEqual(sample['mem_available_bytes'], resources.UNSUPPORTED)
            self.assertEqual(sample['swap_total_bytes'], 0)
            self.assertEqual(sample['swap_free_bytes'], resources.UNSUPPORTED)
            self.assertEqual(sample['disk_available_bytes'], resources.UNSUPPORTED)
            self.assertEqual(sample['runner_rss_bytes'], resources.UNSUPPORTED)
            self.assertEqual(resources.read_text(root / 'meminfo', 2), '')


if __name__ == '__main__':
    unittest.main()
