"""Adversarial tests for the native ARM64 partition and aggregate contract.

Fixtures replay the complete reviewed inventory without building or running Go.
Every validator remains real; local Git identity and tracked-file queries are mocked.
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
import native_arm64_prerequisite as prerequisite


class ShardEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.repo = self.root / 'checkout'
        self.repo.mkdir()
        for name in ('oaksolver.go', 'go.sum', 'stdlib/std.oak', 'stdlib/host.oak',
                     '.github/scripts/native_prover_inventory.json',
                     *('prove/solver/' + name for name in prerequisite.SOURCE_NAMES[:15])):
            path = self.repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((runner.REPO / name).read_bytes())
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
        def git_output(command, **kwargs):
            if command == ['git', 'ls-files', '-z']:
                return b''.join(path.relative_to(self.repo).as_posix().encode() + b'\0'
                                for path in sorted(self.repo.rglob('*')) if path.is_file())
            return self.sha + '\n'
        patcher = mock.patch.object(gate.subprocess, 'check_output', side_effect=git_output)
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
            prepared = None
            if shard == 'support':
                prepared = self.seed_prerequisite(artifact, packages['.'])
            for package, names in packages.items():
                names = sorted(names)
                label = self.label(package)
                command = ['go', 'test', '-json', '-race', '-count=1', '-timeout', runner.TIMEOUTS[package],
                           '-p', '1', package, '-run', runner.pattern(names)]
                extra = {}
                if package == '.':
                    command = prerequisite.root_command(prepared['directory'], names)
                    extra = {'timeout_seconds': 2700, 'elapsed_seconds': 1, 'timed_out': False,
                             'harness_sha256': prepared['harness_sha256'],
                             'success_sha256': prepared['success_sha256'],
                             'environment': {prerequisite.ENVIRONMENT: prepared['directory'] + '/native-prover'}}
                self.write_json(artifact / (label + '-status.json'),
                                dict(schema_version=1, returncode=0, command=command, **extra))
                events = [self.event(package, 'start')]
                for name in names:
                    events.append(self.event(package, 'run', name))
                    for child in self.manifest['children'].get(package, {}).get(name, []):
                        events.extend((self.event(package, 'run', name + '/' + child),
                                       self.event(package, 'pass', name + '/' + child)))
                    events.append(self.event(package, 'pass', name))
                events.append(self.event(package, 'pass'))
                self.write_events(artifact / (label + '.jsonl'), events)

    def seed_prerequisite(self, artifact, names):
        native = artifact / prerequisite.NATIVE
        (native / 'source').mkdir(parents=True)
        sources = prerequisite.source_bytes(self.repo)
        for name, raw in sources.items():
            (native / 'source' / name).write_bytes(raw)
        def elf(kind):
            raw = bytearray(128)
            raw[:6] = b'\x7fELF\x02\x01'
            raw[16:18] = kind.to_bytes(2, 'little')
            raw[18:20] = (183).to_bytes(2, 'little')
            return raw
        (artifact / prerequisite.HARNESS).write_bytes(elf(2))
        (native / 'asm.o').write_bytes(elf(1))
        (native / 'solver').write_bytes(elf(2))
        (native / 'program.c').write_text('/* fixture generated C */\n')
        original = '/home/runner/work/oak/oak/native-arm64-results'
        context = gate.identity(self.repo, self.manifest_path, self.plan_path, 'support', self.env)
        inventory = json.loads((self.repo / '.github/scripts/native_prover_inventory.json').read_text())
        cc = '/usr/bin/aarch64-linux-gnu-gcc-13'
        runtime = '/usr/lib/aarch64-linux-gnu/libc.so.6'
        dependencies = []
        for line in (self.repo / 'go.sum').read_text().splitlines():
            name, version, checksum = line.split()
            if not version.endswith('/go.mod'):
                dependencies.append({'Path': name, 'Version': version, 'Sum': checksum})
        recipe = dict(schema_version=1,
                      recipe_version='hybrid-native-c-v1/fresh-verdicts/default-search/race',
                      context={k: v for k, v in context.items() if k != 'schema_version'},
                      harness_sha256=prerequisite.digest(artifact / prerequisite.HARNESS),
                      sources={name: hashlib.sha256(raw).hexdigest() for name, raw in sources.items()},
                      support_sources={name: prerequisite.digest(self.repo / name)
                                       for name in ('stdlib/std.oak', 'stdlib/host.oak')},
                      inventory=inventory, platform='linux/arm64', target='linux/arm64',
                      asm_mode='native', object_format='ELF', cpu='', c_opt_level=1,
                      go_build=dict(version='go1.27.1',
                                    main={'Path': runner.MODULE, 'Version': '(devel)'},
                                    dependencies=dependencies,
                                    settings={'-race': 'true', '-compiler': 'gc', '-buildmode': 'exe',
                                              'CGO_ENABLED': '1', 'GOOS': 'linux', 'GOARCH': 'arm64'}),
                      cc=dict(path=cc, sha256='c' * 64, version='GCC Free Software Foundation',
                              args=prerequisite.CC_ARGS),
                      toolchain_files={cc: 'c' * 64, runtime: 'd' * 64}, link_inputs=[])
        self.write_json(native / 'recipe.json', recipe)
        functions = []
        for row in inventory['eligible']:
            candidate = dict(name='fixture candidate', body_sha256='e' * 64,
                             recipe_sha256='f' * 64, outcome='proven', message='fixture proof', cached=False)
            functions.append(dict(input=row, status='proven', reason='fixture proof', callees=[],
                                  considered=1, materialized=1, selected=candidate, validations=[candidate]))
        self.write_json(native / 'report.json', dict(schema_version=1, inventory=inventory, functions=functions))
        self.write_json(native / 'success.json', dict(
            schema_version=1, recipe_sha256=prerequisite.digest(native / 'recipe.json'),
            report_sha256=prerequisite.digest(native / 'report.json'),
            program_sha256=prerequisite.digest(native / 'program.c'),
            object_sha256=prerequisite.digest(native / 'asm.o'),
            solver_sha256=prerequisite.digest(native / 'solver'),
            link_command=[cc, *prerequisite.CC_ARGS, '-o', original + '/native-prover/solver',
                          '/tmp/oak-build-fixture/program.c', '/tmp/oak-build-fixture/asm.o', '-lm'],
            runtime_files={runtime: 'd' * 64}))
        commands = prerequisite.commands(original, names)
        for index, stage in enumerate(prerequisite.STAGES):
            self.write_json(artifact / (stage + '-status.json'),
                            dict(schema_version=1, command=commands[stage], returncode=0,
                                 timeout_seconds=5400-index, elapsed_seconds=0.1, timed_out=False))
            (artifact / (stage + '.log')).write_text('\n'.join(sorted(names)) + '\n' if index == 1 else '')
        receipt = dict(schema_version=1, success=True, context=context, directory=original,
                       budget_seconds=5400, elapsed_seconds=1,
                       harness_sha256=prerequisite.digest(artifact / prerequisite.HARNESS),
                       success_sha256=prerequisite.digest(native / 'success.json'))
        self.write_json(artifact / 'prerequisite-status.json', receipt)
        return receipt

    def reseal_prerequisite(self):
        artifact = self.artifact('support')
        native = artifact / prerequisite.NATIVE
        success = json.loads((native / 'success.json').read_text())
        for field, filename in (('recipe_sha256', 'recipe.json'), ('report_sha256', 'report.json'),
                                ('program_sha256', 'program.c'), ('object_sha256', 'asm.o'),
                                ('solver_sha256', 'solver')):
            success[field] = prerequisite.digest(native / filename)
        self.write_json(native / 'success.json', success)
        receipt = json.loads((artifact / 'prerequisite-status.json').read_text())
        receipt['success_sha256'] = prerequisite.digest(native / 'success.json')
        self.write_json(artifact / 'prerequisite-status.json', receipt)
        status = json.loads((artifact / 'root-status.json').read_text())
        status['success_sha256'] = receipt['success_sha256']
        self.write_json(artifact / 'root-status.json', status)

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
        self.assertEqual(self.aggregate(), {'shards': list(gate.SHARDS), 'roots': 198, 'children': 61})
        # These files are conveniences for readers, never proof for the gate.
        for shard, packages in self.plan['shards'].items():
            for package in packages:
                (self.artifact(shard) / (self.label(package) + '-passed.json')).write_text('not authoritative JSON')
        self.assertEqual(self.aggregate()['roots'], 198)

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
            self.assertEqual(self.aggregate(), {'shards': list(gate.SHARDS), 'roots': 198, 'children': 61})
            # A permutation must not hide a missing root or malformed event.
            path = self.artifact() / 'compiler.jsonl'
            events = [json.loads(line) for line in path.read_text().splitlines()]
            events.pop(next(i for i, event in enumerate(events) if event['Action'] == 'run'))
            self.write_events(path, events)
            self.reject()

    def test_cli_uses_repository_paths_and_requires_all_inputs(self):
        repo = Path(gate.__file__).resolve().parents[2]
        with mock.patch.object(gate, 'aggregate', return_value={'roots': 198}) as aggregate:
            self.assertEqual(gate.main(['--aggregate', '--results-dir', str(self.results),
                                        '--matrix-result', 'success']), {'roots': 198})
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
        self.assertEqual(len(roots), 198)
        self.assertEqual(len(set(roots)), 198)
        self.assertEqual(set(roots), {(p, name) for p, names in self.selected.items() for name in names})
        self.assertEqual(sum(len(names) for roots in self.manifest['children'].values() for names in roots.values()), 61)

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
        self.git.assert_any_call(['git', 'rev-parse', 'HEAD'], cwd=self.repo, text=True)
        self.git.assert_any_call(['git', 'rev-parse', 'HEAD^{tree}'], cwd=self.repo, text=True)
        self.git.assert_any_call(['git', 'ls-files', '-z'], cwd=self.repo)
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
                             ('source_sha', 'b' * 40), ('source_tree', 'b' * 40),
                             ('source_contents_sha256', '0' * 64), ('inventory_sha256', '0' * 64),
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
        for path in (self.manifest_path, self.plan_path, self.repo / 'oaksolver.go'):
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

    def test_every_native_prerequisite_file_is_mandatory(self):
        for name in sorted(prerequisite.required_files()):
            self.seed_artifacts()
            (self.artifact('support') / name).unlink()
            with self.subTest(name=name):
                self.reject()

    def test_native_stages_require_exact_commands_success_and_one_total_budget(self):
        for stage in prerequisite.STAGES:
            for key, value in (('returncode', 1), ('returncode', False), ('returncode', -9),
                               ('timed_out', True), ('timed_out', 0), ('elapsed_seconds', -1),
                               ('elapsed_seconds', 5401), ('timeout_seconds', 5401),
                               ('timeout_seconds', 0), ('timeout_seconds', True),
                               ('command', ['go', 'test', '-short'])):
                self.seed_artifacts()
                path = self.artifact('support') / (stage + '-status.json')
                status = json.loads(path.read_text())
                status[key] = value
                self.write_json(path, status)
                with self.subTest(stage=stage, key=key, value=value):
                    self.reject()
        for key, value in (('budget_seconds', 5401), ('budget_seconds', 5400.0),
                           ('elapsed_seconds', 0.2), ('elapsed_seconds', 5401),
                           ('success', False), ('harness_sha256', '0'*64),
                           ('success_sha256', '0'*64), ('directory', '../other')):
            self.seed_artifacts()
            path = self.artifact('support') / 'prerequisite-status.json'
            receipt = json.loads(path.read_text())
            receipt[key] = value
            self.write_json(path, receipt)
            with self.subTest(key=key, value=value):
                self.reject()

    def test_root_executes_same_persisted_race_harness_and_native_artifact(self):
        for key, value in (('harness_sha256', '0'*64), ('success_sha256', '0'*64),
                           ('environment', {}), ('environment', {'OAK_NATIVE_PREREQUISITE': '/other'}),
                           ('timeout_seconds', 2701), ('elapsed_seconds', 2701), ('timed_out', True)):
            self.seed_artifacts()
            path = self.artifact('support') / 'root-status.json'
            status = json.loads(path.read_text())
            status[key] = value
            self.write_json(path, status)
            with self.subTest(key=key):
                self.reject()
        self.seed_artifacts()
        path = self.artifact('support') / 'root-status.json'
        original = json.loads(path.read_text())
        for index in range(len(original['command'])):
            status = copy.deepcopy(original)
            status['command'][index] = 'changed'
            self.write_json(path, status)
            with self.subTest(index=index):
                self.reject()

    def test_native_recipe_changes_fail_even_if_all_receipts_are_rehashed(self):
        mutations = [
            ('recipe_version', 'unverified'), ('target', 'linux/amd64'), ('asm_mode', 'c'),
            ('object_format', 'MachO'), ('cpu', 'native'), ('c_opt_level', 2),
            ('harness_sha256', '0'*64), ('sources.bdd.oak', '0'*64),
            ('support_sources.stdlib/std.oak', '0'*64), ('support_sources.stdlib/host.oak', '0'*64),
            ('context.source_sha', 'b'*40), ('context.source_tree', 'b'*40),
            ('context.source_contents_sha256', '0'*64), ('context.run_id', '54321'),
            ('context.run_attempt', '1'), ('context.shard', 'compiler-a'),
            ('context.inventory_sha256', '0'*64), ('context.plan_sha256', '0'*64),
            ('cc.path', '/usr/bin/other'), ('cc.sha256', '0'*64), ('cc.version', 'Clang'),
            ('cc.args', ['-O0']), ('toolchain_files', {}), ('link_inputs', [{'Kind': 'object', 'Path': '/unreviewed'}]),
            ('go_build.version', 'go1.26.0'), ('go_build.main', {'Path': 'other'}),
            ('go_build.dependencies', []), ('go_build.settings.-race', 'false'),
            ('go_build.settings.GOARCH', 'amd64'), ('go_build.settings.CGO_ENABLED', '0'),
            ('go_build.settings.-tags', 'reduced'), ('go_build.settings.vcs.modified', 'true'),
        ]
        for key, value in mutations:
            self.seed_artifacts()
            path = self.artifact('support') / 'native-prover/recipe.json'
            recipe = json.loads(path.read_text())
            parent = recipe
            parts = key.split('.', 2)
            # Source file names deliberately include a literal dot.
            if parts[0] in ('sources', 'support_sources'):
                parent[parts[0]][key.split('.', 1)[1]] = value
            else:
                for part in parts[:-1]:
                    parent = parent[part]
                parent[parts[-1]] = value
            self.write_json(path, recipe)
            self.reseal_prerequisite()
            with self.subTest(key=key):
                self.reject()

    def test_complete_hybrid_report_keeps_actual_verdicts_and_fallbacks(self):
        path = self.artifact('support') / 'native-prover/report.json'
        report = json.loads(path.read_text())
        for row, outcome in zip(report['functions'], ('trusted', 'witnessed')):
            row['status'] = outcome
            row['selected']['outcome'] = outcome
            row['validations'][0]['outcome'] = outcome
        fallback = report['functions'][2]
        fallback.update(status='c-fallback', reason='unsupported fixture lowering', selected=None, validations=[])
        self.write_json(path, report)
        self.reseal_prerequisite()
        self.assertEqual(self.aggregate()['roots'], 198)

    def test_missing_duplicate_unexpected_unfinished_and_false_report_records_fail(self):
        for mutation in ('missing', 'duplicate', 'extra', 'reordered', 'wrong-input', 'unfinished',
                         'error', 'wrong-verdict', 'no-validation', 'bad-body', 'bad-recipe',
                         'cached', 'bad-count', 'empty-reason', 'extern-native', 'c-only',
                         'duplicate-validation', 'unknown-callee', 'duplicate-callee', 'mismatched-fallback'):
            self.seed_artifacts()
            path = self.artifact('support') / 'native-prover/report.json'
            report = json.loads(path.read_text())
            row = report['functions'][0]
            if mutation == 'missing':
                report['functions'].pop()
            elif mutation == 'duplicate':
                report['functions'][1] = copy.deepcopy(row)
            elif mutation == 'extra':
                report['functions'].append(copy.deepcopy(row))
            elif mutation == 'reordered':
                report['functions'].reverse()
            elif mutation == 'wrong-input':
                row['input']['source_sha256'] = '0'*64
            elif mutation in ('unfinished', 'error'):
                row['status'] = mutation
            elif mutation == 'wrong-verdict':
                row['selected']['outcome'] = 'trusted'
            elif mutation == 'no-validation':
                row['validations'] = []
            elif mutation in ('bad-body', 'bad-recipe'):
                row['selected']['body_sha256' if mutation == 'bad-body' else 'recipe_sha256'] = ''
            elif mutation == 'cached':
                row['validations'][0]['cached'] = True
            elif mutation == 'duplicate-validation':
                row['validations'].append(copy.deepcopy(row['validations'][0]))
            elif mutation == 'unknown-callee':
                row['callees'] = ['missing']
            elif mutation == 'duplicate-callee':
                row['callees'] = [row['input']['name']] * 2
            elif mutation == 'mismatched-fallback':
                row['status'] = 'c-fallback'
                row['selected']['outcome'] = 'mismatch'
                row['validations'][0]['outcome'] = 'mismatch'
            elif mutation == 'bad-count':
                row['materialized'] = row['considered'] + 1
            elif mutation == 'empty-reason':
                row['reason'] = ''
            elif mutation == 'extern-native':
                report['inventory']['eligible'][0] = report['inventory']['externs'][0]
            else:
                for item in report['functions']:
                    item.update(status='c-fallback', selected=None, validations=[])
            self.write_json(path, report)
            self.reseal_prerequisite()
            with self.subTest(mutation=mutation):
                self.reject()

    def test_native_output_source_and_harness_bytes_are_independently_checked(self):
        artifact = self.artifact('support')
        for name in ('root-harness', 'native-prover/program.c', 'native-prover/asm.o',
                     'native-prover/solver', 'native-prover/source/bdd.oak'):
            self.seed_artifacts()
            path = artifact / name
            path.write_bytes(path.read_bytes() + b'changed')
            with self.subTest(name=name):
                self.reject()
        for name in ('program.c', 'asm.o', 'solver'):
            self.seed_artifacts()
            (artifact / 'native-prover' / name).write_bytes(b'')
            self.reseal_prerequisite()
            with self.subTest(empty=name):
                self.reject()

    def test_actual_link_command_and_runtime_identities_are_required(self):
        self.seed_artifacts()
        path = self.artifact('support') / 'native-prover/success.json'
        original = json.loads(path.read_text())
        for index in range(len(original['link_command'])):
            changed = copy.deepcopy(original)
            changed['link_command'][index] = 'wrong'
            self.write_json(path, changed)
            self.reseal_prerequisite()
            with self.subTest(index=index):
                self.reject()
        for value in ({}, {'/usr/lib/unexpected': 'a'*64}, {'relative.so': 'd'*64}):
            changed = copy.deepcopy(original)
            changed['runtime_files'] = value
            self.write_json(path, changed)
            self.reseal_prerequisite()
            with self.subTest(runtime=value):
                self.reject()

    def test_native_json_and_nested_artifacts_fail_closed(self):
        files = ('prerequisite-status.json', 'root-harness-build-status.json',
                 'root-harness-list-status.json', 'native-prover-build-status.json',
                 'native-prover/recipe.json', 'native-prover/report.json', 'native-prover/success.json')
        for name in files:
            for raw in ('{', '{}', 'null', '{"schema_version":1,"schema_version":1}'):
                self.seed_artifacts()
                (self.artifact('support') / name).write_text(raw)
                with self.subTest(name=name, raw=raw):
                    self.reject()
        for name in ('native-prover/source/extra.oak', 'native-prover/extra.json', 'unexpected/nested.txt'):
            self.seed_artifacts()
            path = self.artifact('support') / name
            path.parent.mkdir(exist_ok=True)
            path.write_text('extra')
            with self.subTest(name=name):
                self.reject()
        for name in ('root-harness', 'native-prover/solver', 'native-prover/source/bdd.oak'):
            self.seed_artifacts()
            path = self.artifact('support') / name
            path.unlink()
            path.symlink_to(self.repo / 'oaksolver.go')
            with self.subTest(symlink=name):
                self.reject()
        self.seed_artifacts()
        native = self.artifact('support') / 'native-prover'
        destination = self.root / 'native-outside'
        native.rename(destination)
        native.symlink_to(destination, target_is_directory=True)
        self.reject()


if __name__ == '__main__':
    unittest.main()
