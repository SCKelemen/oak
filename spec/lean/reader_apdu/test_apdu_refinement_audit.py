"""Finite controls for the actual imported APDU consumer; no compiler invocation.

Run only when separately authorized:
  python3 test_apdu_refinement_audit.py --contract PATH [-v] [--adapter DIRECTORY]
The 11 methods and 141 subcases below are explicit, checked inventories. Complete
fixtures contain all 280 theorems and 2226 candidates; they are synthetic audit
messages, not evidence of compilation or implementation refinement.
"""
import argparse
from contextlib import ExitStack, contextmanager
from copy import deepcopy
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import unittest
from unittest import mock


ORACLES = ('sorryAx', 'Lean.trustCompiler', 'Lean.ofReduceBool',
           'Lean.ofReduceNat', 'Lean.reduceBool', 'Lean.reduceNat')
CONTROL_INVENTORY = {
    'test_positive_graphs': ('complete', 'private', 'cycle', 'shared', 'repeated', 'allowed_axioms'),
    'test_contract_inventory': (
        'expected_schema', 'theorem_count', 'duplicate_theorem', 'theorem_schema',
        'theorem_private_type', 'theorem_module', 'anonymous_count', 'anonymous_schema',
        'anonymous_line_boolean', 'anonymous_duplicate', 'named_count', 'named_duplicate',
        'named_missing_theorem', 'distribution_count', 'distribution_duplicate',
        'distribution_overlap', 'distribution_nonlist'),
    'test_record_schema_order': (
        'empty_records', 'nonlist_records', 'over_record_bound', 'unknown_record',
        'missing_field', 'extra_field', 'wrong_record_type', 'missing_imports',
        'duplicate_imports', 'wrong_import_set', 'duplicate_theorem', 'reordered_theorem',
        'early_candidate', 'duplicate_candidate', 'late_theorem', 'early_dependency',
        'duplicate_dependency', 'post_complete'),
    'test_names_private': (
        'empty_name', 'nul_name', 'oversized_name', 'dependency_name_type',
        'dependencies_nonlist', 'invalid_public_actual', 'invalid_private_actual',
        'private_boolean', 'owner_mismatch', 'candidate_user_mismatch'),
    'test_oracles_and_axioms': tuple(
        oracle + ':' + location for oracle in ORACLES
        for location in ('candidate', 'dependency', 'axioms')) + (
            'unapproved_axiom', 'candidate_owned_axiom', 'invalid_kind',
            'incomplete_axioms', 'overstated_axioms', 'duplicate_axioms'),
    'test_graph_coverage': (
        'missing_node', 'missing_reference', 'extra_node', 'candidate_kind',
        'candidate_edges', 'theorem_edges', 'theorem_axioms', 'missing_theorem_candidate',
        'candidate_owner', 'theorem_kind'),
    'test_completion': (
        'missing', 'duplicate', 'early', 'expected_count', 'candidate_count', 'node_count',
        'edge_count', 'example_count', 'persisted', 'boolean_counter', 'extra_field'),
    'test_diagnostics': (
        'valid', 'compile_empty', 'wrong_file', 'severity', 'silent', 'full_range',
        'caption', 'kind', 'prefix', 'position_negative', 'position_boolean',
        'position_line_boolean', 'end_position_line_boolean', 'end_position_column_boolean',
        'end_position', 'missing_field', 'extra_field', 'duplicate_outer_key',
        'duplicate_record_key', 'invalid_utf8', 'nonfinite', 'nonjson', 'empty_line',
        'unterminated', 'empty_stdout', 'stderr', 'compile_stdout', 'stdout_exact_cap',
        'stdout_over_cap', 'message_over_cap', 'unknown_record'),
    'test_bounds': (
        'edges_at_cap', 'edges_over_cap', 'pending_at_cap', 'pending_over_cap',
        'array_over_cap', 'nodes_at_cap', 'nodes_over_cap', 'candidates_short',
        'candidates_extra', 'candidates_over_cap'),
    'test_deadlines': ('audit_expired', 'diagnostic_parse_expired', 'graph_expired'),
    'test_process_guard': ('import_and_calls_guarded',),
}
CONTROL_COUNTS = {
    'test_positive_graphs': 6, 'test_contract_inventory': 17,
    'test_record_schema_order': 18, 'test_names_private': 10,
    'test_oracles_and_axioms': 24, 'test_graph_coverage': 10,
    'test_completion': 11, 'test_diagnostics': 31, 'test_bounds': 10,
    'test_deadlines': 3, 'test_process_guard': 1,
}
EXPECTED_METHOD_COUNT = 11
EXPECTED_SUBCASE_COUNT = 141
DRIVER_PATH = Path('/synthetic/APDURefinementAuditDriver.lean')
ADAPTER = None
CONTRACT = None
TEMPLATE = None
PROCESS_ATTEMPTS = []


def blocked_process(*args, **kwargs):
    PROCESS_ATTEMPTS.append((args, kwargs))
    raise RuntimeError('process execution forbidden in APDU consumer controls')


def select(records, kind):
    return [record for record in records if record.get('record') == kind]


def reconcile(records):
    nodes = select(records, 'dependency')
    records[-1] = {
        'record': 'complete', 'expected_theorems': len(select(records, 'expected_theorem')),
        'candidate_declarations': len(select(records, 'candidate_declaration')),
        'dependency_nodes': len(nodes),
        'dependency_edges': sum(len(node['direct_dependencies']) for node in nodes),
        'anonymous_examples_persisted': False,
        'anonymous_examples_accounted_by_exact_source_compile': 15,
    }


def make_fixture(candidate_count=2226):
    records = [{'record': 'imports',
                'modules': sorted(set(CONTRACT['distribution_modules']) | ADAPTER.MODULES)}]
    candidates = []
    for index, row in enumerate(CONTRACT['expected']['theorems']):
        user_name = row['qualified_name']
        name = ('_private.synthetic.' + str(index) + '.' + user_name
                if row['private'] else user_name)
        records.append({'record': 'expected_theorem', 'owner': row['module'],
                        'user_name': user_name, 'actual_name': name, 'private': row['private'],
                        'axioms': [], 'direct_dependencies': []})
        candidates.append({'record': 'candidate_declaration', 'actual_name': name,
                           'user_name': user_name, 'owner': row['module'], 'kind': 'theorem',
                           'axioms': [], 'direct_dependencies': []})
    owner = sorted(ADAPTER.MODULES)[0]
    for index in range(candidate_count - len(candidates)):
        name = 'Synthetic.candidate_' + str(index)
        candidates.append({'record': 'candidate_declaration', 'actual_name': name,
                           'user_name': name, 'owner': owner, 'kind': 'definition',
                           'axioms': [], 'direct_dependencies': []})
    records.extend(candidates)
    records.extend({'record': 'dependency', 'actual_name': row['actual_name'],
                    'kind': row['kind'], 'direct_dependencies': []} for row in candidates)
    records.append({})
    reconcile(records)
    return records


def link(records, name, dependencies, axioms=None):
    for record in records:
        if record.get('actual_name') == name:
            record['direct_dependencies'] = list(dependencies)
            if axioms is not None and 'axioms' in record:
                record['axioms'] = list(axioms)


def add_node(records, name='Synthetic.shared', kind='definition', dependencies=()):
    records.insert(-1, {'record': 'dependency', 'actual_name': name, 'kind': kind,
                        'direct_dependencies': list(dependencies)})


def message(record):
    return {'fileName': str(DRIVER_PATH), 'pos': {'line': 1, 'column': 0},
            'endPos': {'line': 1, 'column': 1}, 'keepFullRange': False,
            'severity': 'information', 'isSilent': False, 'caption': '',
            'data': ADAPTER.PREFIX + json.dumps(record, separators=(',', ':')),
            'kind': '[anonymous]'}


def encode_message(value):
    return json.dumps(value, separators=(',', ':'), ensure_ascii=True).encode() + b'\n'


def stdout_for(records):
    return b''.join(encode_message(message(record)) for record in records)


class AuditControls(unittest.TestCase):
    seen = set()

    @contextmanager
    def case(self, label):
        key = (self._testMethodName, label)
        self.assertIn(label, CONTROL_INVENTORY[self._testMethodName])
        self.assertNotIn(key, self.seen)
        self.seen.add(key)
        with self.subTest(control=label):
            yield

    @classmethod
    def tearDownClass(cls):
        expected = {(method, label) for method, labels in CONTROL_INVENTORY.items()
                    for label in labels}
        if cls.seen != expected:
            raise AssertionError('subcase inventory not completely exercised: ' +
                                 repr(sorted(expected - cls.seen)))

    def fixture(self):
        return deepcopy(TEMPLATE)

    def audit(self, records, contract=None):
        return ADAPTER.audit_records(records, time.monotonic() + 60,
                                     CONTRACT if contract is None else contract)

    def reject(self, records, contract=None):
        with self.assertRaises(RuntimeError):
            self.audit(records, contract)

    def assert_acceptance(self, result):
        for key, value in {
            'accepted': True, 'actual_imports': 1058, 'named_theorems': 280,
            'source_examples': 15, 'named_controls': 41, 'candidate_declarations': 2226,
            'anonymous_examples_persisted': False, 'imported_distribution_normal_trust': True,
            'generated_definition_refinement_established': True,
            'oak_implementation_refinement_established': False,
            'implementation_refinement_established': False,
        }.items():
            self.assertEqual(result[key], value, key)
            self.assertIs(type(result[key]), type(value), key)
        self.assertEqual(result['allowed_axioms'], ['Classical.choice', 'Quot.sound', 'propext'])

    def test_positive_graphs(self):
        for label in CONTROL_INVENTORY[self._testMethodName]:
            with self.case(label):
                records = self.fixture()
                contract = deepcopy(CONTRACT)
                roots = select(records, 'expected_theorem')
                first, second = roots[0]['actual_name'], roots[1]['actual_name']
                if label == 'private':
                    contract['expected']['theorems'][0]['private'] = True
                    roots[0]['private'] = True
                    for row in records:
                        if row.get('actual_name') == first:
                            row['actual_name'] = '_private.fixture.0.' + first
                elif label == 'cycle':
                    link(records, first, [second])
                    link(records, second, [first])
                elif label in ('shared', 'repeated'):
                    add_node(records)
                    link(records, first, ['Synthetic.shared'] * (3 if label == 'repeated' else 1))
                    link(records, second, ['Synthetic.shared'])
                elif label == 'allowed_axioms':
                    for name in ('propext', 'Quot.sound', 'Classical.choice'):
                        add_node(records, name, 'axiom')
                    link(records, first, ['propext', 'Quot.sound', 'Classical.choice'],
                         ['propext', 'Quot.sound', 'Classical.choice'])
                reconcile(records)
                result = self.audit(records, contract)
                self.assert_acceptance(result)
                self.assertEqual(result['dependency_edges'], records[-1]['dependency_edges'])
                if label == 'repeated':
                    self.assertEqual(result['dependency_edges'], 4)
                    self.assertEqual(result['independent_edge_occurrences'], 8)

    def test_contract_inventory(self):
        for label in CONTROL_INVENTORY[self._testMethodName]:
            with self.case(label):
                contract = deepcopy(CONTRACT)
                expected = contract['expected']
                theorems, examples = expected['theorems'], expected['anonymous_controls']
                controls, distribution = expected['named_controls'], contract['distribution_modules']
                if label == 'expected_schema': expected['unexpected'] = 0
                elif label == 'theorem_count': theorems.pop()
                elif label == 'duplicate_theorem': theorems[1] = deepcopy(theorems[0])
                elif label == 'theorem_schema': theorems[0]['unexpected'] = 0
                elif label == 'theorem_private_type': theorems[0]['private'] = 0
                elif label == 'theorem_module': theorems[0]['module'] = 'Foreign.Module'
                elif label == 'anonymous_count': examples.pop()
                elif label == 'anonymous_schema': examples[0]['unexpected'] = 0
                elif label == 'anonymous_line_boolean': examples[0]['line'] = True
                elif label == 'anonymous_duplicate': examples[1] = deepcopy(examples[0])
                elif label == 'named_count': controls.pop()
                elif label == 'named_duplicate': controls[1] = controls[0]
                elif label == 'named_missing_theorem': controls[0] = 'Synthetic.missing_control'
                elif label == 'distribution_count': distribution.pop()
                elif label == 'distribution_duplicate': distribution[1] = distribution[0]
                elif label == 'distribution_overlap': distribution[0] = sorted(ADAPTER.MODULES)[0]
                elif label == 'distribution_nonlist': contract['distribution_modules'] = tuple(distribution)
                self.reject(self.fixture(), contract)

    def test_record_schema_order(self):
        for label in CONTROL_INVENTORY[self._testMethodName]:
            with self.case(label):
                records = self.fixture()
                candidates, nodes = select(records, 'candidate_declaration'), select(records, 'dependency')
                if label == 'empty_records': records = []
                elif label == 'nonlist_records': records = tuple(records)
                elif label == 'over_record_bound': records = [{}] * 14283
                elif label == 'unknown_record': records[1]['record'] = 'unsupported'
                elif label == 'missing_field': del records[1]['axioms']
                elif label == 'extra_field': records[1]['unexpected'] = 0
                elif label == 'wrong_record_type': records[1] = []
                elif label == 'missing_imports': records.pop(0)
                elif label == 'duplicate_imports': records.insert(1, deepcopy(records[0]))
                elif label == 'wrong_import_set': records[0]['modules'][0] = 'Foreign.Module'
                elif label == 'duplicate_theorem': records[2] = deepcopy(records[1])
                elif label == 'reordered_theorem': records[1], records[2] = records[2], records[1]
                elif label == 'early_candidate': records.insert(1, deepcopy(candidates[0]))
                elif label == 'duplicate_candidate': records.insert(281, deepcopy(candidates[0]))
                elif label == 'late_theorem': records.insert(282, deepcopy(records[1]))
                elif label == 'early_dependency': records.insert(281, deepcopy(nodes[0]))
                elif label == 'duplicate_dependency': records.insert(-1, deepcopy(nodes[0]))
                elif label == 'post_complete': records.append(deepcopy(nodes[0]))
                self.reject(records)

    def test_names_private(self):
        for label in CONTROL_INVENTORY[self._testMethodName]:
            with self.case(label):
                records = self.fixture()
                theorem = records[1]
                candidate = select(records, 'candidate_declaration')[0]
                if label == 'empty_name': theorem['actual_name'] = ''
                elif label == 'nul_name': theorem['actual_name'] = 'bad\x00name'
                elif label == 'oversized_name': theorem['actual_name'] = 'x' * 65537
                elif label == 'dependency_name_type': theorem['direct_dependencies'] = [1]
                elif label == 'dependencies_nonlist': theorem['direct_dependencies'] = ()
                elif label == 'invalid_public_actual':
                    theorem = next(row for row in select(records, 'expected_theorem') if not row['private'])
                    theorem['actual_name'] = 'Synthetic.wrong_public'
                elif label == 'invalid_private_actual':
                    theorem = next(row for row in select(records, 'expected_theorem') if row['private'])
                    theorem['actual_name'] = 'Synthetic.wrong_private'
                elif label == 'private_boolean': theorem['private'] = int(theorem['private'])
                elif label == 'owner_mismatch': theorem['owner'] = 'Foreign.Module'
                elif label == 'candidate_user_mismatch': candidate['user_name'] = 'Synthetic.wrong_user'
                self.reject(records)

    def test_oracles_and_axioms(self):
        for label in CONTROL_INVENTORY[self._testMethodName]:
            with self.case(label):
                records = self.fixture()
                candidates, nodes = select(records, 'candidate_declaration'), select(records, 'dependency')
                root = records[1]['actual_name']
                if ':' in label:
                    oracle, location = label.split(':')
                    if location == 'candidate': candidates[-1]['actual_name'] = oracle
                    elif location == 'dependency': nodes[-1]['actual_name'] = oracle
                    else: records[1]['axioms'] = [oracle]
                elif label == 'unapproved_axiom':
                    add_node(records, 'Synthetic.oracle', 'axiom')
                    link(records, root, ['Synthetic.oracle'])
                elif label == 'candidate_owned_axiom': candidates[-1]['kind'] = 'axiom'
                elif label == 'invalid_kind': candidates[-1]['kind'] = 'unknown'
                elif label == 'incomplete_axioms':
                    add_node(records, 'propext', 'axiom')
                    link(records, root, ['propext'])
                elif label == 'overstated_axioms': link(records, root, [], ['propext'])
                elif label == 'duplicate_axioms': records[1]['axioms'] = ['propext', 'propext']
                reconcile(records)
                self.reject(records)

    def test_graph_coverage(self):
        for label in CONTROL_INVENTORY[self._testMethodName]:
            with self.case(label):
                records = self.fixture()
                candidates, nodes = select(records, 'candidate_declaration'), select(records, 'dependency')
                root = records[1]['actual_name']
                if label == 'missing_node': records.remove(nodes[-1])
                elif label == 'missing_reference': link(records, root, ['Synthetic.missing'])
                elif label == 'extra_node': add_node(records)
                elif label == 'candidate_kind': candidates[-1]['kind'] = 'opaque'
                elif label == 'candidate_edges': candidates[-1]['direct_dependencies'] = [root]
                elif label == 'theorem_edges': records[1]['direct_dependencies'] = [root]
                elif label == 'theorem_axioms': records[1]['axioms'] = ['propext']
                elif label == 'missing_theorem_candidate':
                    candidates[0]['actual_name'] = candidates[0]['user_name'] = 'Synthetic.replacement'
                    nodes[0]['actual_name'] = 'Synthetic.replacement'
                elif label == 'candidate_owner':
                    candidates[0]['owner'] = next(owner for owner in ADAPTER.MODULES
                                                   if owner != records[1]['owner'])
                elif label == 'theorem_kind': candidates[0]['kind'] = nodes[0]['kind'] = 'definition'
                reconcile(records)
                self.reject(records)

    def test_completion(self):
        fields = {'expected_count': 'expected_theorems', 'candidate_count': 'candidate_declarations',
                  'node_count': 'dependency_nodes', 'edge_count': 'dependency_edges',
                  'example_count': 'anonymous_examples_accounted_by_exact_source_compile'}
        for label in CONTROL_INVENTORY[self._testMethodName]:
            with self.case(label):
                records = self.fixture()
                if label == 'missing': records.pop()
                elif label == 'duplicate': records.append(deepcopy(records[-1]))
                elif label == 'early': records.insert(-2, records.pop())
                elif label in fields: records[-1][fields[label]] += 1
                elif label == 'persisted': records[-1]['anonymous_examples_persisted'] = True
                elif label == 'boolean_counter': records[-1]['dependency_edges'] = False
                elif label == 'extra_field': records[-1]['unexpected'] = 0
                self.reject(records)

    def test_diagnostics(self):
        complete = stdout_for(TEMPLATE)
        boolean_positions = {
            'position_boolean': ('pos', 'column', False, b'"pos":{"line":1,"column":false}'),
            'position_line_boolean': ('pos', 'line', True, b'"pos":{"line":true,"column":0}'),
            'end_position_line_boolean': ('endPos', 'line', True, b'"endPos":{"line":true,"column":1}'),
            'end_position_column_boolean': ('endPos', 'column', True, b'"endPos":{"line":1,"column":true}'),
        }
        for label in CONTROL_INVENTORY[self._testMethodName]:
            with self.case(label):
                first = message(TEMPLATE[0])
                stdout, stderr, phase = complete, b'', 'audit'
                changes = {'wrong_file': ('fileName', '/wrong/APDURefinementAuditDriver.lean'),
                           'severity': ('severity', 'warning'), 'silent': ('isSilent', True),
                           'full_range': ('keepFullRange', True), 'caption': ('caption', 'unexpected'),
                           'kind': ('kind', 'unsupported'), 'prefix': ('data', 'wrong prefix')}
                if label in changes:
                    key, value = changes[label]
                    first[key] = value
                elif label == 'position_negative': first['pos']['line'] = -1
                elif label in boolean_positions:
                    location, coordinate, value, token = boolean_positions[label]
                    first[location][coordinate] = value
                elif label == 'end_position': first['endPos']['line'] = 2**32
                elif label == 'missing_field': del first['caption']
                elif label == 'extra_field': first['unexpected'] = 0
                elif label == 'duplicate_record_key': first['data'] = ADAPTER.PREFIX + '{"record":"imports","record":"imports","modules":[]}'
                elif label == 'nonfinite': first['data'] = ADAPTER.PREFIX + '{"record":NaN}'
                elif label == 'unknown_record': first['data'] = ADAPTER.PREFIX + '{"record":"unknown"}'
                # Always serialize the mutation: bool and int compare equal in Python.
                stdout = encode_message(first) + complete.split(b'\n', 1)[1]
                if label == 'compile_empty': stdout, phase = b'', 'compile'
                elif label == 'duplicate_outer_key': stdout = b'{"fileName":"x","fileName":"y"}\n'
                elif label == 'invalid_utf8': stdout = b'\xff\n'
                elif label == 'nonjson': stdout = b'not-json\n'
                elif label == 'empty_line': stdout = b'\n' + complete
                elif label == 'unterminated': stdout = complete[:-1]
                elif label == 'empty_stdout': stdout = b''
                elif label == 'stderr': stderr = b'warning\n'
                elif label == 'compile_stdout': phase = 'compile'
                elif label == 'stdout_exact_cap':
                    self.assertLess(len(complete), 12582912)
                    stdout = b' ' * (12582912 - len(complete)) + complete
                elif label == 'stdout_over_cap': stdout = b' ' * 12582912 + b'\n'
                elif label == 'message_over_cap': stdout = b'{}\n' * 14283
                if label in boolean_positions:
                    first_line = stdout.split(b'\n', 1)[0]
                    self.assertEqual(first_line, encode_message(first)[:-1])
                    self.assertNotEqual(first_line, complete.split(b'\n', 1)[0])
                    self.assertIn(token, first_line)
                    self.assertIs(json.loads(first_line)[location][coordinate], value)
                if label in ('valid', 'compile_empty', 'stdout_exact_cap'):
                    result = ADAPTER.diagnostics(stdout, stderr, phase, time.monotonic() + 60,
                                                 DRIVER_PATH, CONTRACT)
                    if label == 'compile_empty': self.assertIsNone(result)
                    else: self.assert_acceptance(result)
                else:
                    with self.assertRaises((RuntimeError, ValueError, UnicodeError)):
                        ADAPTER.diagnostics(stdout, stderr, phase, time.monotonic() + 60,
                                            DRIVER_PATH, CONTRACT)

    def test_bounds(self):
        for label in CONTROL_INVENTORY[self._testMethodName]:
            with self.case(label):
                records = self.fixture()
                roots, candidates = select(records, 'expected_theorem'), select(records, 'candidate_declaration')
                first = roots[0]['actual_name']
                if label.startswith('edges_') or label == 'array_over_cap':
                    add_node(records)
                    link(records, first, ['Synthetic.shared'] * (100001 if label == 'array_over_cap' else 100000))
                    if label == 'edges_over_cap': link(records, roots[1]['actual_name'], ['Synthetic.shared'])
                elif label.startswith('pending_'):
                    add_node(records)
                    # This is the first combined-walk root: 2225 roots remain pending.
                    count = 97775 if label == 'pending_at_cap' else 97776
                    link(records, candidates[-1]['actual_name'], ['Synthetic.shared'] * count)
                elif label.startswith('nodes_'):
                    count = (10000 if label == 'nodes_at_cap' else 10001) - 2226
                    extras = ['Synthetic.node_' + str(index) for index in range(count)]
                    for name in extras: add_node(records, name)
                    link(records, first, extras)
                else:
                    count = {'candidates_short': 2225, 'candidates_extra': 2227,
                             'candidates_over_cap': 4001}[label]
                    records = make_fixture(count)
                reconcile(records)
                if label in ('edges_at_cap', 'pending_at_cap', 'nodes_at_cap'):
                    result = self.audit(records)
                    self.assert_acceptance(result)
                    if label == 'edges_at_cap':
                        self.assertEqual(result['dependency_edges'], 100000)
                        self.assertEqual(result['independent_edge_occurrences'], 200000)
                    elif label == 'pending_at_cap': self.assertEqual(result['dependency_edges'], 97775)
                    else: self.assertEqual(result['dependency_nodes'], 10000)
                else:
                    self.reject(records)

    def test_deadlines(self):
        with self.case('audit_expired'):
            with self.assertRaises(RuntimeError):
                ADAPTER.audit_records(self.fixture(), time.monotonic() - 1, CONTRACT)
        with self.case('diagnostic_parse_expired'):
            stdout = stdout_for(TEMPLATE)
            with mock.patch.object(ADAPTER.time, 'monotonic', side_effect=[0.0, 1.0]):
                with self.assertRaisesRegex(RuntimeError, 'audit parsing original deadline'):
                    ADAPTER.diagnostics(stdout, b'', 'audit', 0.5, DRIVER_PATH, CONTRACT)
        with self.case('graph_expired'):
            records = self.fixture()
            with mock.patch.object(ADAPTER.time, 'monotonic', side_effect=[0.0] * len(records) + [1.0]):
                with self.assertRaisesRegex(RuntimeError, 'graph reconstruction original deadline'):
                    ADAPTER.audit_records(records, 0.5, CONTRACT)

    def test_process_guard(self):
        with self.case('import_and_calls_guarded'):
            self.assertEqual(PROCESS_ATTEMPTS, [])
            for name in ('Popen', 'run', 'call', 'check_call', 'check_output', 'getoutput', 'getstatusoutput'):
                self.assertIs(getattr(subprocess, name), blocked_process)
            self.assertIs(os.system, blocked_process)
            self.assertIs(os.popen, blocked_process)


def main():
    global ADAPTER, CONTRACT, TEMPLATE
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--adapter', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--contract', type=Path, required=True)
    parser.add_argument('-v', '--verbose', action='store_true')
    args = parser.parse_args()
    if ({name: len(labels) for name, labels in CONTROL_INVENTORY.items()} != CONTROL_COUNTS or
            len(CONTROL_INVENTORY) != EXPECTED_METHOD_COUNT or
            sum(CONTROL_COUNTS.values()) != EXPECTED_SUBCASE_COUNT):
        raise RuntimeError('declared control inventory/count mismatch')
    discovered = unittest.defaultTestLoader.getTestCaseNames(AuditControls)
    if set(discovered) != set(CONTROL_INVENTORY):
        raise RuntimeError('test method inventory mismatch')
    sys.dont_write_bytecode = True
    adapter_path = (args.adapter / 'apdu_refinement_audit_consumer.py').resolve(strict=True)
    sys.path.insert(0, str(adapter_path.parent))
    with ExitStack() as guards:
        for name in ('Popen', 'run', 'call', 'check_call', 'check_output', 'getoutput', 'getstatusoutput'):
            guards.enter_context(mock.patch.object(subprocess, name, blocked_process))
        guards.enter_context(mock.patch.object(os, 'system', blocked_process))
        guards.enter_context(mock.patch.object(os, 'popen', blocked_process))
        spec = importlib.util.spec_from_file_location('apdu_consumer_under_control', adapter_path)
        if spec is None or spec.loader is None:
            raise RuntimeError('adapter import specification unavailable')
        ADAPTER = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(ADAPTER)
        CONTRACT = ADAPTER.decode(args.contract.read_bytes())
        TEMPLATE = make_fixture()
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(AuditControls)
        result = unittest.TextTestRunner(verbosity=2 if args.verbose else 1).run(suite)
        success = result.wasSuccessful() and not PROCESS_ATTEMPTS
        print(json.dumps({'schema': 'oak-apdu-refinement-control-result-v1', 'passed': success,
                          'methods': result.testsRun, 'subcases': len(AuditControls.seen),
                          'expected_methods': EXPECTED_METHOD_COUNT,
                          'expected_subcases': EXPECTED_SUBCASE_COUNT,
                          'process_attempts': len(PROCESS_ATTEMPTS),
                          'synthetic_fixtures_only': True}, sort_keys=True))
    return 0 if success else 1


if __name__ == '__main__':
    raise SystemExit(main())
