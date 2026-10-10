"""Adversarial tests for the native ARM64 partition and aggregate contract.

Fixtures replay the complete reviewed inventory without building or running Go.
Every validator remains real; only the local git HEAD query is mocked.
"""
import contextlib
import copy
import hashlib
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest import mock

import native_arm64 as runner
import native_arm64_shards as gate


class ShardEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.repo = self.root / 'checkout'
        self.repo.mkdir()
        self.manifest_path = self.repo / 'inventory.json'
        self.manifest_path.write_bytes(runner.MANIFEST.read_bytes())
        self.manifest = json.loads(self.manifest_path.read_text())
        self.source = {'roots': [], 'skips': []}
        for package, roots in self.manifest['roots'].items():
            self.source['roots'].extend(dict(package=package, test=name, file=file)
                                        for name, file in roots.items())
        for location, calls in self.manifest['skip_sites'].items():
            file, function = location.split('::')
            self.source['skips'].extend(dict(file=file, function=function, call=call) for call in calls)
        with contextlib.redirect_stdout(io.StringIO()):
            self.selected = runner.check_inventory(self.manifest, self.source)
        self.plan = {'schema_version': 1, 'measurement': {'fixture': True}, 'shards': {}}
        for index, shard in enumerate(gate.SHARDS[:-1]):
            self.plan['shards'][shard] = {'./compiler': self.selected['./compiler'][index::3]}
        self.plan['shards']['support'] = {p: names for p, names in self.selected.items() if p != './compiler'}
        self.plan_path = self.repo / 'plan.json'
        self.write_json(self.plan_path, self.plan)
        self.sha = 'a' * 40
        self.env = {'GITHUB_SHA': self.sha, 'GITHUB_RUN_ID': '12345', 'GITHUB_RUN_ATTEMPT': '2'}
        patcher = mock.patch.object(gate.subprocess, 'check_output', return_value=self.sha + '\n')
        self.git = patcher.start()
        self.addCleanup(patcher.stop)
        self.results = self.root / 'results'
        self.seed_artifacts()

    @staticmethod
    def write_json(path, value):
        path.write_text(json.dumps(value, indent=2) + '\n')

    @staticmethod
    def label(package):
        return 'root' if package == '.' else package[2:].replace('/', '-')

    @staticmethod
    def event(package, action, name=None):
        item = {'Action': action, 'Package': runner.MODULE if package == '.' else runner.MODULE + package[1:]}
        if name is not None:
            item['Test'] = name
        return item

    def artifact(self, shard='compiler-a'):
        return self.results / ('native-arm64-12345-2-' + shard)

    def seed_artifacts(self):
        if self.results.exists():
            shutil.rmtree(self.results)
        self.results.mkdir()
        for shard, packages in self.plan['shards'].items():
            artifact = self.artifact(shard)
            artifact.mkdir()
            self.write_json(artifact / 'identity.json',
                            gate.identity(self.repo, self.manifest_path, self.plan_path, shard, self.env))
            self.write_json(artifact / 'source-inventory.json', self.source)
            self.write_json(artifact / 'lane-result.json',
                            dict(schema_version=1, shard=shard, success=True, packages=sorted(packages)))
            for package, names in packages.items():
                names = sorted(names)
                label = self.label(package)
                command = ['go', 'test', '-json', '-race', '-count=1', '-timeout', runner.TIMEOUTS[package],
                           '-p', '1', package, '-run', runner.pattern(names)]
                self.write_json(artifact / (label + '-status.json'),
                                dict(schema_version=1, returncode=0, command=command))
                events = [self.event(package, 'start')]
                for name in names:
                    events.append(self.event(package, 'run', name))
                    for child in self.manifest['children'].get(package, {}).get(name, []):
                        events.extend((self.event(package, 'run', name + '/' + child),
                                       self.event(package, 'pass', name + '/' + child)))
                    events.append(self.event(package, 'pass', name))
                events.append(self.event(package, 'pass'))
                self.write_events(artifact / (label + '.jsonl'), events)

    @staticmethod
    def write_events(path, events):
        path.write_text(''.join(json.dumps(event) + '\n' for event in events))

    def aggregate(self, result='success', directory=None):
        with contextlib.redirect_stdout(io.StringIO()):
            return gate.aggregate(self.repo, self.results if directory is None else directory,
                                  self.manifest_path, self.plan_path, result, self.env)

    def reject(self, result='success', directory=None):
        with self.assertRaises((ValueError, OSError)):
            self.aggregate(result, directory)

    def test_complete_evidence_covers_every_root_and_child_exactly_once(self):
        self.assertEqual(self.aggregate(), {'shards': list(gate.SHARDS), 'roots': 197, 'children': 59})
        # These files are conveniences for readers, never proof for the gate.
        for shard, packages in self.plan['shards'].items():
            for package in packages:
                (self.artifact(shard) / (self.label(package) + '-passed.json')).write_text('not authoritative JSON')
        self.assertEqual(self.aggregate()['roots'], 197)

    def test_artifact_and_event_permutations_preserve_exact_coverage(self):
        for artifact in self.results.iterdir():
            for path in artifact.glob('*.jsonl'):
                events = [json.loads(line) for line in path.read_text().splitlines()]
                # Root scheduling may differ, but each root's Go lifecycle and
                # the package start/completion boundaries must remain intact.
                blocks = []
                for event in events[1:-1]:
                    if event['Action'] == 'run' and '/' not in event['Test']:
                        blocks.append([])
                    blocks[-1].append(event)
                permuted = [events[0]] + [event for block in reversed(blocks) for event in block] + [events[-1]]
                self.write_events(path, permuted)
        iterdir = Path.iterdir
        with mock.patch.object(Path, 'iterdir', lambda path: iter(reversed(list(iterdir(path))))):
            self.assertEqual(self.aggregate(), {'shards': list(gate.SHARDS), 'roots': 197, 'children': 59})
            # A permutation must not hide a missing root or malformed event.
            path = self.artifact() / 'compiler.jsonl'
            events = [json.loads(line) for line in path.read_text().splitlines()]
            events.pop(next(i for i, event in enumerate(events) if event['Action'] == 'run'))
            self.write_events(path, events)
            self.reject()

    def test_cli_uses_repository_paths_and_requires_all_inputs(self):
        repo = Path(gate.__file__).resolve().parents[2]
        with mock.patch.object(gate, 'aggregate', return_value={'roots': 197}) as aggregate:
            self.assertEqual(gate.main(['--aggregate', '--results-dir', str(self.results),
                                        '--matrix-result', 'success']), {'roots': 197})
            aggregate.assert_called_once_with(repo, self.results,
                                              repo / '.github/scripts/native_arm64_inventory.json',
                                              repo / '.github/scripts/native_arm64_shards.json', 'success')
        complete = ['--aggregate', '--results-dir', str(self.results), '--matrix-result', 'success']
        for args in ([], complete[1:], complete[:1] + complete[3:], complete[:3]):
            with self.subTest(args=args), contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                gate.main(args)

    def test_reviewed_repository_plan_is_a_complete_disjoint_partition(self):
        plan = runner.MANIFEST.with_name('native_arm64_shards.json')
        shards = gate.load_shards(self.selected, self.manifest, plan)
        roots = [(package, name) for packages in shards.values() for package, names in packages.items() for name in names]
        self.assertEqual(len(roots), 197)
        self.assertEqual(len(set(roots)), 197)
        self.assertEqual(set(roots), {(p, name) for p, names in self.selected.items() for name in names})
        self.assertEqual(sum(len(names) for roots in self.manifest['children'].values() for names in roots.values()), 59)

    def test_shard_selection_is_sorted_and_children_stay_with_their_root(self):
        for packages in self.plan['shards'].values():
            for names in packages.values():
                names.reverse()
        self.write_json(self.plan_path, self.plan)
        shards = gate.load_shards(self.selected, self.manifest, self.plan_path)
        for packages in shards.values():
            for names in packages.values():
                self.assertEqual(names, sorted(names))
        for package, roots in self.manifest['children'].items():
            for root in roots:
                self.assertEqual(sum(root in packages.get(package, []) for packages in shards.values()), 1)

    def test_partition_omissions_overlaps_unknown_roots_and_empty_shards_fail(self):
        for mutation in ('omit', 'duplicate', 'overlap', 'unknown', 'excluded', 'child', 'empty'):
            plan = copy.deepcopy(self.plan)
            a = plan['shards']['compiler-a']['./compiler']
            b = plan['shards']['compiler-b']['./compiler']
            if mutation == 'omit':
                a.pop()
            elif mutation == 'duplicate':
                a.append(a[0])
            elif mutation == 'overlap':
                b.append(a[0])
            elif mutation == 'unknown':
                a.append('TestUnknown')
            elif mutation == 'excluded':
                a.append('TestE2EExampleSMEPackage')
            elif mutation == 'child':
                a.append(a[0] + '/child')
            else:
                a.clear()
            self.write_json(self.plan_path, plan)
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                gate.load_shards(self.selected, self.manifest, self.plan_path)

    def test_compiler_and_support_package_ownership_cannot_change(self):
        for mutation in ('support-in-compiler', 'compiler-in-support', 'support-omitted', 'unknown-package'):
            plan = copy.deepcopy(self.plan)
            a, support = plan['shards']['compiler-a'], plan['shards']['support']
            if mutation == 'support-in-compiler':
                a['.'] = support.pop('.')
            elif mutation == 'compiler-in-support':
                support['./compiler'] = a.pop('./compiler')
            elif mutation == 'support-omitted':
                support.pop('.')
            else:
                support['./unknown'] = ['TestUnknown']
            self.write_json(self.plan_path, plan)
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                gate.load_shards(self.selected, self.manifest, self.plan_path)

    def test_missing_extra_and_malformed_shard_plan_entries_fail(self):
        for replacement in (None, [], {}, {'compiler-a': {}}, dict(self.plan['shards'], extra={})):
            self.write_json(self.plan_path, {'schema_version': 1, 'shards': replacement})
            with self.subTest(replacement=replacement), self.assertRaises(ValueError):
                gate.load_shards(self.selected, self.manifest, self.plan_path)
        for replacement in (None, {}, [None], [1], 'TestOne'):
            plan = copy.deepcopy(self.plan)
            plan['shards']['compiler-a']['./compiler'] = replacement
            self.write_json(self.plan_path, plan)
            with self.subTest(replacement=replacement), self.assertRaises(ValueError):
                gate.load_shards(self.selected, self.manifest, self.plan_path)

    def test_missing_unsupported_or_noninteger_plan_schema_versions_fail(self):
        for version in (None, True, False, 0, 2, '1', 1.0):
            plan = copy.deepcopy(self.plan)
            if version is None:
                del plan['schema_version']
            else:
                plan['schema_version'] = version
            self.write_json(self.plan_path, plan)
            with self.subTest(version=version), self.assertRaisesRegex(ValueError, 'schema_version'):
                gate.load_shards(self.selected, self.manifest, self.plan_path)
    def test_invalid_required_children_cannot_be_dropped_or_reassigned(self):
        for roots in ({'TestUnknown': ['child']}, {self.selected['./compiler'][0]: []},
                      {self.selected['./compiler'][0]: ['child', 'child']},
                      {self.selected['./compiler'][0]: [None]}):
            manifest = copy.deepcopy(self.manifest)
            manifest['children']['./compiler'] = roots
            with self.subTest(roots=roots), self.assertRaises(ValueError):
                gate.load_shards(self.selected, manifest, self.plan_path)

    def test_duplicate_json_keys_in_plan_are_rejected(self):
        self.plan_path.write_text('{"shards": {}, "shards": ' + json.dumps(self.plan['shards']) + '}')
        with self.assertRaisesRegex(ValueError, 'duplicate JSON'):
            gate.load_shards(self.selected, self.manifest, self.plan_path)

    def test_identity_is_bound_to_raw_files_and_actual_checkout(self):
        actual = gate.identity(self.repo, self.manifest_path, self.plan_path, 'compiler-a', self.env)
        self.assertEqual(actual['source_sha'], self.sha)
        self.assertEqual(actual['inventory_sha256'], hashlib.sha256(self.manifest_path.read_bytes()).hexdigest())
        self.assertEqual(actual['plan_sha256'], hashlib.sha256(self.plan_path.read_bytes()).hexdigest())
        self.git.assert_called_with(['git', 'rev-parse', 'HEAD'], cwd=self.repo, text=True)
        for field in self.env:
            env = dict(self.env)
            env.pop(field)
            with self.subTest(field=field), self.assertRaises(ValueError):
                gate.identity(self.repo, self.manifest_path, self.plan_path, 'compiler-a', env)
        for field, value in (('GITHUB_SHA', 'b' * 40), ('GITHUB_RUN_ID', 12345),
                             ('GITHUB_RUN_ID', '../other'), ('GITHUB_RUN_ATTEMPT', '0')):
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                gate.identity(self.repo, self.manifest_path, self.plan_path, 'compiler-a', dict(self.env, **{field: value}))

    def test_missing_cancelled_failed_or_skipped_matrix_dependency_fails(self):
        for result in (None, '', 'cancelled', 'failure', 'skipped', 'pending', 'Success', True):
            with self.subTest(result=result):
                self.reject(result)

    def test_missing_or_cancelled_lane_artifacts_cannot_pass(self):
        for shard in gate.SHARDS:
            self.seed_artifacts()
            shutil.rmtree(self.artifact(shard))
            with self.subTest(shard=shard):
                self.reject()
        shutil.rmtree(self.results)
        self.reject()

    def test_extra_duplicate_and_stale_artifacts_cannot_pass(self):
        for name in ('native-arm64-12345-2-compiler-a-copy', 'native-arm64-12345-1-support', 'unexpected'):
            self.seed_artifacts()
            shutil.copytree(self.artifact(), self.results / name)
            with self.subTest(name=name):
                self.reject()
        self.seed_artifacts()
        self.write_json(self.artifact('compiler-b') / 'identity.json',
                        json.loads((self.artifact() / 'identity.json').read_text()))
        self.reject()

    def test_each_required_evidence_file_and_success_receipt_is_mandatory(self):
        for file in ('identity.json', 'source-inventory.json', 'lane-result.json', 'compiler-status.json', 'compiler.jsonl'):
            self.seed_artifacts()
            (self.artifact() / file).unlink()
            with self.subTest(file=file):
                self.reject()
        self.seed_artifacts()
        (self.artifact('support') / 'root-status.json').unlink()
        self.reject()

    def test_wrong_source_inventory_plan_run_attempt_or_shard_identity_fails(self):
        for field, value in (('schema_version', True), ('schema_version', 2), ('shard', 'compiler-b'),
                             ('source_sha', 'b' * 40), ('inventory_sha256', '0' * 64),
                             ('plan_sha256', '0' * 64), ('run_id', '12346'),
                             ('run_attempt', '1'), ('run_attempt', 2)):
            self.seed_artifacts()
            path = self.artifact() / 'identity.json'
            context = json.loads(path.read_text())
            context[field] = value
            self.write_json(path, context)
            with self.subTest(field=field, value=value):
                self.reject()

    def test_changed_raw_manifest_or_plan_invalidates_recorded_identity(self):
        for path in (self.manifest_path, self.plan_path):
            original = path.read_bytes()
            path.write_bytes(original + b'\n')
            with self.subTest(path=path):
                self.reject()
            path.write_bytes(original)

    def test_failed_malformed_or_incomplete_success_receipts_fail(self):
        for field, value in (('success', False), ('success', 1), ('shard', 'compiler-b'),
                             ('packages', []), ('packages', ['./compiler', './compiler']),
                             ('packages', ['./semir']), ('schema_version', True)):
            self.seed_artifacts()
            path = self.artifact() / 'lane-result.json'
            receipt = json.loads(path.read_text())
            receipt[field] = value
            self.write_json(path, receipt)
            with self.subTest(field=field, value=value):
                self.reject()

    def test_changed_source_scanner_roots_skip_sites_and_malformed_inventory_fail(self):
        for mutation in ('missing', 'duplicate', 'skip', 'malformed'):
            self.seed_artifacts()
            source = copy.deepcopy(self.source)
            if mutation == 'missing':
                source['roots'].pop()
            elif mutation == 'duplicate':
                source['roots'].append(source['roots'][0])
            elif mutation == 'skip':
                source['skips'].append(dict(file='compiler/new_test.go', function='TestNew', call='t.Skip("new")'))
            else:
                source = {'roots': [None]}
            self.write_json(self.artifact() / 'source-inventory.json', source)
            with self.subTest(mutation=mutation):
                self.reject()

    def test_nonzero_and_malformed_returncodes_are_never_success(self):
        for code in (1, -9, 124, None, False, True, '0', 0.0, [], {}):
            self.seed_artifacts()
            path = self.artifact() / 'compiler-status.json'
            status = json.loads(path.read_text())
            status['returncode'] = code
            self.write_json(path, status)
            with self.subTest(code=code):
                self.reject()

    def test_every_command_flag_timeout_package_and_selector_must_match(self):
        for index in range(12):
            self.seed_artifacts()
            path = self.artifact() / 'compiler-status.json'
            status = json.loads(path.read_text())
            status['command'][index] = 'changed'
            self.write_json(path, status)
            with self.subTest(index=index):
                self.reject()
        for added in ('-short', '-skip=.', '-count=2', '-run=.'):
            self.seed_artifacts()
            path = self.artifact() / 'compiler-status.json'
            status = json.loads(path.read_text())
            status['command'].append(added)
            self.write_json(path, status)
            with self.subTest(added=added):
                self.reject()

    def test_malformed_truncated_and_duplicate_key_json_is_rejected(self):
        for file in ('identity.json', 'source-inventory.json', 'lane-result.json', 'compiler-status.json'):
            for raw in ('{', 'null', '[]', '{"schema_version": 1, "schema_version": 1}'):
                self.seed_artifacts()
                (self.artifact() / file).write_text(raw)
                with self.subTest(file=file, raw=raw):
                    self.reject()
        for suffix in (b'not JSON\n', b'{}\n', b'null\n', b'\n',
                       b'{"Action":"pass","Action":"skip"}\n', b'{"Action":NaN}\n'):
            self.seed_artifacts()
            path = self.artifact() / 'compiler.jsonl'
            path.write_bytes(path.read_bytes() + suffix)
            with self.subTest(suffix=suffix):
                self.reject()
        for trim in (1, 8, 80):
            self.seed_artifacts()
            path = self.artifact() / 'compiler.jsonl'
            path.write_bytes(path.read_bytes()[:-trim])
            with self.subTest(trim=trim):
                self.reject()

    def test_skipped_or_failed_roots_children_and_package_are_rejected(self):
        path = self.artifact() / 'compiler.jsonl'
        original = [json.loads(line) for line in path.read_text().splitlines()]
        root = next(event['Test'] for event in original if event['Action'] == 'run' and '/' not in event['Test'])
        child = next(event['Test'] for event in original if event['Action'] == 'run' and '/' in event['Test'])
        for action in ('skip', 'fail'):
            for name in (None, root, child):
                self.write_events(path, original + [self.event('./compiler', action, name)])
                with self.subTest(action=action, name=name):
                    self.reject()

    def test_missing_duplicate_or_unreviewed_roots_children_and_package_completion_fail(self):
        path = self.artifact() / 'compiler.jsonl'
        original = [json.loads(line) for line in path.read_text().splitlines()]
        root = next(event['Test'] for event in original if event['Action'] == 'run' and '/' not in event['Test'])
        child = next(event['Test'] for event in original if event['Action'] == 'run' and '/' in event['Test'])
        for name in (root, child, None):
            actions = ('pass',) if name is None else ('run', 'pass')
            for action in actions:
                target = next(event for event in original if event['Action'] == action and event.get('Test') == name)
                missing = list(original)
                missing.remove(target)
                for events in (missing, original + [target]):
                    self.write_events(path, events)
                    with self.subTest(action=action, name=name, count=len(events)):
                        self.reject()
        for extra in (self.event('./compiler', 'run', 'TestUnknown'),
                      self.event('./compiler', 'run', root + '/unknown'),
                      self.event('./asm', 'output'), {'Action': 'bogus', 'Package': runner.MODULE + '/compiler'},
                      {'Action': 'pass', 'Package': runner.MODULE + '/compiler', 'Test': False}):
            self.write_events(path, original + [extra])
            with self.subTest(extra=extra):
                self.reject()

    def test_pass_before_run_and_early_package_completion_are_rejected(self):
        path = self.artifact() / 'compiler.jsonl'
        original = [json.loads(line) for line in path.read_text().splitlines()]
        for mutation in ('root-pass-before-run', 'child-pass-before-run', 'package-pass-before-tests'):
            events = copy.deepcopy(original)
            if mutation == 'package-pass-before-tests':
                completion = events.pop()
            else:
                child = mutation == 'child-pass-before-run'
                index = next(i for i, event in enumerate(events)
                             if event['Action'] == 'pass' and event.get('Test')
                             and ('/' in event['Test']) == child)
                completion = events.pop(index)
            events.insert(1, completion)
            self.write_events(path, events)
            with self.subTest(mutation=mutation):
                self.reject()

    def test_passing_summaries_cannot_cover_missing_or_failed_raw_events(self):
        self.write_json(self.artifact() / 'compiler-passed.json', self.selected['./compiler'])
        (self.artifact() / 'compiler.jsonl').write_text('')
        self.reject()

    def test_unexpected_package_evidence_or_nested_files_fail(self):
        for name in ('asm.jsonl', 'compiler-copy.jsonl', 'extra.txt'):
            path = self.artifact() / name
            path.write_text('ignored evidence must not sneak in')
            with self.subTest(name=name):
                self.reject()
            path.unlink()
        (self.artifact() / 'nested').mkdir()
        self.reject()

    def test_symlink_files_directories_and_ancestors_are_rejected(self):
        for file in ('compiler.jsonl', 'identity.json', 'lane-result.json', 'compiler-passed.json'):
            self.seed_artifacts()
            path = self.artifact() / file
            if path.exists():
                path.unlink()
            path.symlink_to(self.artifact('compiler-b') / 'compiler.jsonl')
            with self.subTest(file=file):
                self.reject()
        self.seed_artifacts()
        backup = self.root / 'backup'
        self.artifact().rename(backup)
        self.artifact().symlink_to(backup, target_is_directory=True)
        self.reject()
        self.seed_artifacts()
        alias = self.root / 'alias'
        alias.symlink_to(self.root, target_is_directory=True)
        self.reject(directory=alias / 'results')


if __name__ == '__main__':
    unittest.main()
