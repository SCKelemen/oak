import copy
import io
import json
from pathlib import Path
import re
import tempfile
import unittest
from unittest import mock

import native_arm64 as gate


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
        self.assertEqual({p: len(n) for p, n in selected.items()}, {'.': 2, './asm': 1, './compiler': 192, './testrunner': 1})
        self.assertEqual(sum(len(c) for roots in self.manifest['children'].values() for c in roots.values()), 57)
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


if __name__ == '__main__':
    unittest.main()
