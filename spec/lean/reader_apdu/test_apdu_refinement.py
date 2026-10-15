"""Finite APDU profile controls; source-only until an authorized control run.

Every subprocess entry point and os.system is refused during actual module
imports and tests. All process/audit/object fixtures are synthetic, not proof
evidence. No Lean, Go, shell, downloader, existing test or target is invoked.
"""
import argparse
import copy
from contextlib import ExitStack
import importlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

# Independent literal inventory copied from the accepted final-source authority,
# not derived from the contract or the adapter's module list under test.
EXPECTED_MODULES = ('APDUExtracted', 'BoundedReaderExtracted', 'BoundedReaderModel',
                    'APDULengthModel', 'BoundedReaderRefinement', 'APDUModelErrorContracts',
                    'APDUReaderBridge', 'APDUParserRefinement', 'APDUParserHelperProofs',
                    'APDUParserCorrectness', 'APDUParserControls')
EXPECTED_MODULE_SOURCES = {'spec/lean/Oak/Stdlib/APDUExtracted.lean': {'bytes': 15917,
                                             'sha256': '55d97ce34d1a3436156ab6d7df32538f5f3a0be530ab27238494a19dfaedecc6'},
 'spec/lean/Oak/Stdlib/APDULengthModel.lean': {'bytes': 20026,
                                               'sha256': '896b78507df003704c62c738660451275cfd0b53e0257abdac15e49e071223cf'},
 'spec/lean/Oak/Stdlib/APDUModelErrorContracts.lean': {'bytes': 6848,
                                                       'sha256': '9bab755e837993691fe42dfeec46a73e4c33f9b1844220d7fcffa6428e4dac96'},
 'spec/lean/Oak/Stdlib/APDUParserControls.lean': {'bytes': 3387,
                                                  'sha256': '2ec74a2b379c40484830fe5285c15fd2e476f3d68b9b68241043d46e9449e602'},
 'spec/lean/Oak/Stdlib/APDUParserCorrectness.lean': {'bytes': 11872,
                                                     'sha256': '71db4c91f229424362802d044db6a32dc46238a5883259056640aaab2ba8553f'},
 'spec/lean/Oak/Stdlib/APDUParserHelperProofs.lean': {'bytes': 22752,
                                                      'sha256': '86ec7c758ff3901fb90c4a1e9c468f8eb51f80a4a45cd66629e50350b6970d55'},
 'spec/lean/Oak/Stdlib/APDUParserRefinement.lean': {'bytes': 9058,
                                                    'sha256': '4c7ce29c02e1a2ac1dcee39bf6f3c7bf9ef4d0636c5c13af708e1bc517446bc0'},
 'spec/lean/Oak/Stdlib/APDUReaderBridge.lean': {'bytes': 23882,
                                                'sha256': '4c33b141cbfa7350a99f3f5d76c01bc861f81f179ba7bbbb756c809dae05d564'},
 'spec/lean/Oak/Stdlib/BoundedReaderExtracted.lean': {'bytes': 5624,
                                                      'sha256': '94f44f3e034bd421c1653304d5b8cb6558a2440f595854af962a2088fe08a335'},
 'spec/lean/Oak/Stdlib/BoundedReaderModel.lean': {'bytes': 10433,
                                                  'sha256': 'b7eaf77ba004107148989d476bc8818c482c5121abb4be2cc640f6d4ed4eecd7'},
 'spec/lean/Oak/Stdlib/BoundedReaderRefinement.lean': {'bytes': 48400,
                                                       'sha256': '21f8c9bf4956e21a192a31192d70bddf997baf0e5f325450315b99ca42ec50b8'}}

C = CONTRACT = SOURCE = EXTRACTION = None
NOW, END = 10.0, 20.0
VERBOSE_FAULTS = ('empty', 'stderr', 'truncated', 'skip', 'missing', 'duplicate',
                  'order', 'child', 'extra', 'nonascii')
RESULT_FAULTS = ('accepted', 'scope', 'contract', 'checkout', 'controls', 'emit',
                 'theorems', 'examples', 'imports', 'candidates', 'object-count',
                 'object-type', 'object-size', 'object-snapshot', 'phase-count')
PROCESS_FAULTS = ('exit', 'exit-bool', 'eof', 'overflow', 'joined', 'descendants', 'argv')
SOURCE_CASE_COUNTS = {
    'test_contract_and_drift': 2,
    'test_eleven_module_source_inventory': 12,
    'test_exact_seventy_plus_one': 2,
    'test_verbose_refusals': 10,
    'test_extraction_equal_and_expired': 2,
    'test_each_extraction_byte_drift': 3,
    'test_extraction_membership': 2,
    'test_five_current_source_pins': 5,
    'test_two_fixture_pins': 2,
    'test_receipt_span_and_origin': 4,
    'test_eleven_objects_and_identity': 4,
    'test_result_and_process_refusals': 15,
    'test_each_of_fourteen_processes': 98,
    'test_retention_exact_and_tamper': 8,
    'test_retention_missing_or_extra': 2,
    'test_sixty_four_entries_no_auxiliary_slack': 2,
    'test_resource_constants_and_deadline': 3,
    'test_exclusive_output_and_metadata_cap': 3,
    'test_main_success_and_late_failure': 3,
}


def verbose(names):
    return (''.join('=== RUN   ' + n + '\n--- PASS: ' + n + ' (0.00s)\n'
                    for n in names) + 'PASS\n').encode()


class APDUProfileControls(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='apdu-profile-controls-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.addCleanup(self.check_scratch)
        self.repo, self.work = self.root / 'source', self.root / 'work'
        self.work.mkdir(mode=0o700)
        self.contract, self.extraction = copy.deepcopy(CONTRACT), dict(EXTRACTION)
        for relative, data in SOURCE.items():
            self.write(self.repo / relative, data)
        self.clock = mock.patch.object(C.time, 'monotonic', return_value=NOW)
        self.clock.start()
        self.addCleanup(self.clock.stop)
        self.runner = mock.patch.object(C.host, 'run_lean', side_effect=AssertionError('target refused'))
        self.runner.start()
        self.addCleanup(self.runner.stop)
        self.lean, self.extractor = self.root / 'tool/bin/lean', self.root / 'extractor.test'
        self.driver = self.repo / 'spec/lean/reader_apdu/APDURefinementAuditDriver.lean'

    def write(self, path, data):
        path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
        C.host.write_new(path, data)

    def check_scratch(self):
        # Largest fixture is the three serial mocked main invocations plus the
        # 2.8-MiB source input set. No target output or toolchain is materialized.
        count = logical = allocated = 0
        for directory, directories, files in os.walk(self.root, followlinks=False):
            count += 1 + len(files)
            allocated += Path(directory).lstat().st_blocks * 512
            for name in files:
                info = (Path(directory) / name).lstat()
                logical += info.st_size
                allocated += info.st_blocks * 512
            self.assertLessEqual(count, 384)
            self.assertLessEqual(logical, 8 * 1024**2)
            self.assertLessEqual(allocated, 8 * 1024**2)

    def equality(self, leaves=None, contract=None):
        return C.extraction_equality(leaves or self.extraction, contract or self.contract, END, self.repo)

    def rejected(self, call):
        with self.assertRaises((RuntimeError, UnicodeError, KeyError, TypeError, ValueError, OSError)):
            call()

    def result_fixture(self):
        objects = {}
        for module in C.MODULES:
            target = self.work / 'objects/Oak/Stdlib' / (module + '.olean')
            self.write(target, ('synthetic ' + module).encode())
            objects[target.name] = C.host.object_identity(target)
        records = []
        arguments = [
            [str(self.extractor), '-test.v', '-test.count=1', '-test.timeout=10s',
             '-test.run=^TestAPDUParserControl'],
            [str(self.extractor), '-test.v', '-test.count=1', '-test.timeout=45s',
             '-test.run=^TestAPDUParserExtractionEmit$', '-apdu-source-root=' + str(self.repo),
             '-apdu-fixture=' + str(self.repo / self.contract['fixture']),
             '-apdu-output=' + str(self.work / 'extracted')],
        ]
        for module in C.MODULES:
            arguments.append([str(self.lean), *C.host.FLAGS, '--root=' + str(self.repo / 'spec/lean'),
                              '-o', str(self.work / 'objects/Oak/Stdlib' / (module + '.olean')),
                              str(self.repo / 'spec/lean/Oak/Stdlib' / (module + '.lean'))])
        arguments.append([str(self.lean), *C.host.FLAGS, '--root=' + str(self.driver.parent), str(self.driver)])
        for phase, argv in zip(C.PHASES, arguments):
            records.append({'phase': phase, 'argv': argv, 'returncode': 0,
                            'pipe_eof': ['stderr', 'stdout'], 'overflow': False,
                            'direct_child_joined': True, 'arbitrary_descendant_emptiness_established': False})
        audit = {'accepted': True, 'named_theorems': 280, 'named_controls': 41,
                 'candidate_declarations': 2226, 'actual_imports': 1058, 'source_examples': 15,
                 'anonymous_examples_persisted': False, 'generated_definition_refinement_established': True,
                 'oak_implementation_refinement_established': False, 'implementation_refinement_established': False,
                 'imported_distribution_normal_trust': True, 'allowed_axioms': sorted(self.contract['allowed_axioms']),
                 'dependency_nodes': 4817, 'dependency_edges': 99722,
                 'independent_processed_nodes': 347056, 'independent_edge_occurrences': 5145957}
        return {'accepted': True, 'generated_definition_refinement': True, 'oak_implementation_refinement': False,
                'source_contract_sha256': C.CONTRACT_SHA256, 'checkout_commit': '1' * 40,
                'historical_extraction_tree': self.contract['historical_extraction_tree'],
                'extraction': self.contract['extraction']['files'], 'controls': {'roots': 70, 'children': 0, 'skips': 0},
                'emit': {'roots': 1, 'children': 0, 'skips': 0}, 'audit': audit, 'objects': objects,
                'direct_processes': records}

    def retention_fixture(self):
        result = self.result_fixture()
        for directory in ('home', 'tmp', 'extracted'):
            (self.work / directory).mkdir(mode=0o700)
        for phase in C.PHASES:
            for suffix in ('-stdout.log', '-stderr.log', '-execution.json'):
                self.write(self.work / (phase + suffix), b'fixture\n' if phase == 'audit' and suffix == '-stdout.log' else b'')
        for name, data in self.extraction.items():
            self.write(self.work / 'extracted' / name, data)
        leaves = {'audit-stdout.log': b'fixture\n', 'audit-stderr.log': b'',
                  **{'extracted/' + n: b for n, b in self.extraction.items()}}
        self.write(self.work / 'result.json', C.host.retained_json(result))
        self.write(self.work / 'object-hashes.json', C.retention_manifest(result, leaves, self.contract))
        return result

    def test_contract_and_drift(self):
        with self.subTest(case='valid'):
            self.assertEqual(C.load_contract(), CONTRACT)
        with self.subTest(case='drift'):
            path = self.root / 'contract/apdu_refinement_contract.json'
            self.write(path, json.dumps(CONTRACT).encode() + b' ')
            self.rejected(lambda: C.load_contract(path.parent))

    def test_eleven_module_source_inventory(self):
        with self.subTest(case='valid-independent-inventory'):
            self.assertEqual(C.MODULES, EXPECTED_MODULES)
            self.assertEqual(C.module_source_pins(self.contract), EXPECTED_MODULE_SOURCES)
            for path, expected in EXPECTED_MODULE_SOURCES.items():
                self.assertEqual(C.bytes_identity(SOURCE[path]), expected)
        for path in EXPECTED_MODULE_SOURCES:
            with self.subTest(missing=path):
                contract = copy.deepcopy(self.contract)
                contract['inputs'].pop(path)
                self.rejected(lambda: C.module_source_pins(contract))

    def test_exact_seventy_plus_one(self):
        for names in (self.contract['control_roots'], ['TestAPDUParserExtractionEmit']):
            with self.subTest(count=len(names)):
                self.assertEqual(C.test_output(verbose(names), b'', names), {'roots': len(names), 'children': 0, 'skips': 0})

    def test_verbose_refusals(self):
        names = self.contract['control_roots']
        raw = verbose(names)
        for fault in VERBOSE_FAULTS:
            with self.subTest(fault=fault):
                data, err = raw, b''
                if fault == 'empty': data = b''
                elif fault == 'stderr': err = b'warning\n'
                elif fault == 'truncated': data = raw[:-1]
                elif fault == 'skip': data = raw.replace(b'--- PASS:', b'--- SKIP:', 1)
                elif fault == 'missing': data = verbose(names[1:])
                elif fault == 'duplicate': data = verbose(names + [names[0]])
                elif fault == 'order': data = verbose(list(reversed(names)))
                elif fault == 'child': data = raw.replace(names[0].encode(), (names[0] + '/child').encode())
                elif fault == 'extra': data = raw + b'PASS\n'
                else: data = raw.replace(b'PASS', b'\xffASS', 1)
                self.rejected(lambda: C.test_output(data, err, names))

    def test_extraction_equal_and_expired(self):
        with self.subTest(case='valid'):
            self.assertEqual(self.equality(), self.contract['extraction']['files'])
        with self.subTest(case='expired'):
            with mock.patch.object(C.time, 'monotonic', return_value=END): self.rejected(self.equality)

    def test_each_extraction_byte_drift(self):
        for name in self.extraction:
            with self.subTest(name=name):
                leaves = dict(self.extraction); leaves[name] += b' '
                self.rejected(lambda: self.equality(leaves))

    def test_extraction_membership(self):
        for fault in ('missing', 'extra'):
            with self.subTest(fault=fault):
                leaves = dict(self.extraction)
                if fault == 'missing': leaves.pop('raw.lean')
                else: leaves['extra'] = b''
                self.rejected(lambda: self.equality(leaves))

    def test_five_current_source_pins(self):
        for pin in self.contract['extraction']['receipt']['source_pins']:
            with self.subTest(path=pin['Path']):
                path = self.repo / pin['Path']; original = path.read_bytes(); path.write_bytes(b'X' + original[1:])
                self.rejected(self.equality); path.write_bytes(original)

    def test_two_fixture_pins(self):
        for pin in self.contract['extraction']['receipt']['fixture_pins']:
            with self.subTest(path=pin['Path']):
                path = self.repo / self.contract['fixture'] / pin['Path']; original = path.read_bytes()
                path.write_bytes(b'X' + original[1:]); self.rejected(self.equality); path.write_bytes(original)

    def test_receipt_span_and_origin(self):
        for field in ('raw_start_byte', 'raw_span_sha256', 'source-origin', 'historical-tree'):
            with self.subTest(field=field):
                contract = copy.deepcopy(self.contract); receipt = contract['extraction']['receipt']
                row = receipt['declarations'][0]
                if field == 'source-origin': row['generic_source_span']['FirstLine'] = 0
                elif field == 'historical-tree': receipt['tree_requires_outer_authentication'] = '0' * 40
                elif field == 'raw_start_byte': row[field] = -1
                else: row[field] = '0' * 64
                leaves = dict(self.extraction); leaves['extraction.json'] = json.dumps(receipt).encode()
                contract['extraction']['files']['extraction.json'] = C.bytes_identity(leaves['extraction.json'])
                self.rejected(lambda: self.equality(leaves, contract))

    def test_eleven_objects_and_identity(self):
        result = self.result_fixture(); objects = result['objects']; root = self.work / 'objects'
        with self.subTest(case='valid'):
            C.inspect_objects(root, objects, END)
        with self.subTest(case='extra'):
            self.rejected(lambda: C.inspect_objects(root, dict(objects, **{'extra.olean': next(iter(objects.values()))}), END))
        with self.subTest(case='missing'):
            self.rejected(lambda: C.inspect_objects(root, dict(list(objects.items())[:-1]), END))
        with self.subTest(case='replaced-identity'):
            changed = copy.deepcopy(objects); next(iter(changed.values()))['snapshot'][1] += 1
            self.rejected(lambda: C.inspect_objects(root, changed, END))

    def test_result_and_process_refusals(self):
        result = self.result_fixture()
        for fault in RESULT_FAULTS:
            with self.subTest(fault=fault):
                value = copy.deepcopy(result)
                if fault == 'accepted': value['accepted'] = False
                elif fault == 'scope': value['oak_implementation_refinement'] = True
                elif fault == 'contract': value['source_contract_sha256'] = '0' * 64
                elif fault == 'checkout': value['checkout_commit'] = 'unknown'
                elif fault == 'controls': value['controls']['roots'] = 69
                elif fault == 'emit': value['emit']['skips'] = 1
                elif fault in ('theorems', 'examples', 'imports', 'candidates'):
                    key = {'theorems': 'named_theorems', 'examples': 'source_examples', 'imports': 'actual_imports', 'candidates': 'candidate_declarations'}[fault]
                    value['audit'][key] -= 1
                elif fault == 'object-count': value['objects'].pop(next(iter(value['objects'])))
                elif fault == 'object-type': next(iter(value['objects'].values()))['bytes'] = True
                elif fault == 'object-size': next(iter(value['objects'].values()))['bytes'] = 8 * 1024**2 + 1
                elif fault == 'object-snapshot': next(iter(value['objects'].values()))['snapshot'][4] = 2
                else: value['direct_processes'].pop()
                self.rejected(lambda: C.validate_retained_result(value, self.contract))

    def test_each_of_fourteen_processes(self):
        result = self.result_fixture()
        changes = {'exit': ('returncode', 1), 'exit-bool': ('returncode', False), 'eof': ('pipe_eof', ['stdout']),
                   'overflow': ('overflow', True), 'joined': ('direct_child_joined', False),
                   'descendants': ('arbitrary_descendant_emptiness_established', True), 'argv': ('argv', ['wrong'])}
        for index in range(14):
            for fault in PROCESS_FAULTS:
                with self.subTest(index=index, fault=fault):
                    value = copy.deepcopy(result); key, replacement = changes[fault]
                    value['direct_processes'][index][key] = replacement
                    self.rejected(lambda: C.validate_retained_result(value, self.contract))

    def test_retention_exact_and_tamper(self):
        self.retention_fixture()
        with mock.patch.object(C, 'load_contract', return_value=self.contract):
            with self.subTest(case='valid'):
                C.verify_retention(self.work, END)
            for name in C.ARTIFACT_CAPS:
                with self.subTest(name=name):
                    path = self.work / name; original = path.read_bytes(); path.write_bytes(original + b' ')
                    self.rejected(lambda: C.verify_retention(self.work, END)); path.write_bytes(original)

    def test_retention_missing_or_extra(self):
        self.retention_fixture()
        with mock.patch.object(C, 'load_contract', return_value=self.contract):
            with self.subTest(case='missing'):
                path = self.work / 'audit-stdout.log'; data = path.read_bytes(); path.unlink()
                self.rejected(lambda: C.verify_retention(self.work, END)); self.write(path, data)
            with self.subTest(case='extra'):
                self.write(self.work / 'result.json.tmp', b'')
                self.rejected(lambda: C.verify_retention(self.work, END))

    def test_sixty_four_entries_no_auxiliary_slack(self):
        self.retention_fixture()
        with self.subTest(case='exact64'):
            self.assertEqual(sum(len(dirs) + len(files) for _, dirs, files in os.walk(self.work)), 64)
            C.host.storage_usage(self.work)
        with self.subTest(case='extra'):
            self.write(self.work / 'temporary-output', b'')
            self.rejected(lambda: C.host.storage_usage(self.work))

    def test_resource_constants_and_deadline(self):
        with self.subTest(case='constants'):
            self.assertEqual((C.WHOLE_SECONDS, C.host.FRESH_BYTES, sum(C.ARTIFACT_CAPS.values())),
                             (1560, 64 * 1024**2, 12845056))
        with self.subTest(case='clipped'):
            self.assertEqual(C.host.phase_deadline(100, 120, NOW), 70)
        with self.subTest(case='expired'):
            self.rejected(lambda: C.host.phase_deadline(40, 120, NOW))

    def test_exclusive_output_and_metadata_cap(self):
        path = self.work / 'once'; self.write(path, b'first')
        with self.subTest(case='existing'):
            self.rejected(lambda: self.write(path, b'second'))
        with self.subTest(case='alias'):
            alias = self.work / 'alias'; alias.symlink_to(path)
            self.rejected(lambda: self.write(alias, b'second'))
        with self.subTest(case='metadata-cap'):
            self.rejected(lambda: C.host.retained_json({'value': 'x' * 32768}))

    def test_main_success_and_late_failure(self):
        # Three serial, isolated main calls; actual process runner is replaced.
        for fault in ('none', 'audit', 'final-membership'):
            with self.subTest(fault=fault):
                work = self.root / ('main-' + fault)
                self.lean.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
                if not self.lean.exists(): self.write(self.lean, b'fixture'); self.lean.chmod(0o700)
                if not self.extractor.exists(): self.write(self.extractor, b'fixture'); self.extractor.chmod(0o700)
                summary = {'accepted': True, 'named_theorems': 280, 'named_controls': 41,
                           'candidate_declarations': 2226, 'actual_imports': 1058, 'source_examples': 15,
                           'anonymous_examples_persisted': False, 'generated_definition_refinement_established': True,
                           'oak_implementation_refinement_established': False, 'implementation_refinement_established': False,
                           'imported_distribution_normal_trust': True, 'allowed_axioms': sorted(self.contract['allowed_axioms']),
                           'dependency_nodes': 4817, 'dependency_edges': 99722,
                           'independent_processed_nodes': 347056, 'independent_edge_occurrences': 5145957}
                calls = []
                def run(argv, env, actual_work, phase, deadline, stdout_cap):
                    calls.append(phase)
                    if phase == 'audit' and fault == 'audit': raise RuntimeError('synthetic audit fault')
                    out = verbose(self.contract['control_roots']) if phase == 'controls' else verbose(['TestAPDUParserExtractionEmit']) if phase == 'extract' else b'audit\n' if phase == 'audit' else b''
                    if phase == 'extract':
                        for name, data in self.extraction.items(): self.write(actual_work / 'extracted' / name, data)
                    if phase in C.MODULES: self.write(Path(argv[argv.index('-o') + 1]), b'synthetic object')
                    record = {'phase': phase, 'argv': argv, 'returncode': 0, 'pipe_eof': ['stderr', 'stdout'],
                              'overflow': False, 'direct_child_joined': True, 'arbitrary_descendant_emptiness_established': False}
                    for suffix, data in (('-stdout.log', out), ('-stderr.log', b''), ('-execution.json', json.dumps(record).encode())):
                        self.write(actual_work / (phase + suffix), data)
                    return out, b'', record
                real_write = C.host.write_new
                def publish(path, data):
                    real_write(path, data)
                    if fault == 'final-membership' and Path(path).name == 'result.json':
                        real_write(work / 'unexpected.tmp', b'')
                with ExitStack() as stack:
                    stack.enter_context(mock.patch.object(C, 'REPO', self.repo))
                    stack.enter_context(mock.patch.object(C, 'HERE', self.repo / 'spec/lean/reader_apdu'))
                    stack.enter_context(mock.patch.object(C, 'load_contract', return_value=self.contract))
                    stack.enter_context(mock.patch.object(C, 'verify_file', side_effect=lambda path, expected, deadline: C.host.object_identity(path)))
                    stack.enter_context(mock.patch.object(C.host, 'verify_distribution', return_value=None))
                    stack.enter_context(mock.patch.object(C.host, 'physical_guards', side_effect=lambda path, *args: C.host.storage_usage(path)))
                    stack.enter_context(mock.patch.object(C.host, 'run_lean', side_effect=run))
                    stack.enter_context(mock.patch.object(C.host, 'write_new', side_effect=publish))
                    stack.enter_context(mock.patch.object(C, 'load_extraction', return_value=(self.extraction, self.contract['extraction']['files'])))
                    stack.enter_context(mock.patch.object(C, 'diagnostics', side_effect=lambda out, err, phase, *args: summary if phase == 'audit' else None))
                    stack.enter_context(mock.patch.object(C.signal, 'signal'))
                    stack.enter_context(mock.patch.object(C.os, 'statvfs', return_value=type('FS', (), {'f_bavail': 2**30, 'f_frsize': 1})()))
                    stack.enter_context(mock.patch.object(sys, 'argv', ['check', '--lean', str(self.lean), '--extractor', str(self.extractor), '--checkout-commit', '1' * 40, '--work', str(work)]))
                    if fault == 'none': C.main(); self.assertEqual(calls, list(C.PHASES))
                    else: self.rejected(C.main)


def main():
    global C, CONTRACT, SOURCE, EXTRACTION
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--adapter', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--repo-root', type=Path)
    options, remaining = parser.parse_known_args()
    adapter = options.adapter.resolve()
    if (set(unittest.defaultTestLoader.getTestCaseNames(APDUProfileControls)) != set(SOURCE_CASE_COUNTS)
            or len(SOURCE_CASE_COUNTS) != 19 or sum(SOURCE_CASE_COUNTS.values()) != 182):
        raise RuntimeError('fixed APDU profile control inventory')
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(adapter))
    with ExitStack() as stack:
        refusal = AssertionError('subprocess execution is outside APDU synthetic controls')
        for name in ('Popen', 'run', 'call', 'check_call', 'check_output', 'getoutput', 'getstatusoutput'):
            stack.enter_context(mock.patch.object(subprocess, name, side_effect=refusal))
        stack.enter_context(mock.patch.object(os, 'system', side_effect=refusal))
        stack.enter_context(mock.patch.object(os, 'popen', side_effect=refusal))
        C = importlib.import_module('check_apdu_refinement')
        if Path(C.__file__).resolve() != adapter / 'check_apdu_refinement.py':
            raise RuntimeError('actual selected APDU profile required')
        CONTRACT = C.load_contract(adapter)
        repo = options.repo_root.resolve() if options.repo_root else C.REPO
        # Source-shaped fixtures only. Include all locked inputs for the mocked
        # main path; no toolchain data, objects, executables or caches are copied.
        SOURCE = {name: C.read_regular(repo / name, expected['bytes']) for name, expected in CONTRACT['inputs'].items()}
        SOURCE['spec/lean/reader_apdu/apdu_refinement_contract.json'] = C.read_regular(adapter / 'apdu_refinement_contract.json', 1024**2)
        EXTRACTION = {'raw.lean': SOURCE[CONTRACT['extraction']['raw_reference']],
                      'APDUExtracted.lean': SOURCE[CONTRACT['extraction']['profiled_reference']],
                      'extraction.json': SOURCE[CONTRACT['extraction']['receipt_reference']]}
        unittest.main(argv=[sys.argv[0], *remaining])


if __name__ == '__main__':
    main()
