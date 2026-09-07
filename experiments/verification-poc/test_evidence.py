import copy
import itertools
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from evidence import Rejected, check_tree, read_json, truth, verify
from produce import produce, tree
from project import evaluate

ROOT = Path(__file__).parent
GOOD = ROOT / 'examples/borrow.json'
BAD = ROOT / 'examples/broken.json'


class EvidenceTests(unittest.TestCase):
    def test_all_three_valid_evidence_kinds(self):
        for project, kind in ((GOOD, 'inductive'), (GOOD, 'closed-set'), (BAD, 'trace')):
            self.assertTrue(verify(project, produce(project, kind))['accepted'])

    def test_checker_does_not_call_search_or_producer_evaluation(self):
        cert = produce(GOOD, 'inductive')
        with patch('project.finite_check', side_effect=AssertionError('search called')), patch('project.evaluate', side_effect=AssertionError('producer evaluator called')):
            self.assertTrue(verify(GOOD, cert)['accepted'])

    def test_wrong_model_rejected(self):
        with self.assertRaises(Rejected):
            verify(GOOD, produce(BAD, 'trace'))

    def test_trace_rejects_bad_edges_start_endpoint_and_types(self):
        original = produce(BAD, 'trace')
        mutations = []
        bad = copy.deepcopy(original); bad['states'] = [bad['states'][0], bad['states'][-1]]; mutations.append(bad)
        bad = copy.deepcopy(original); bad['states'] = bad['states'][1:]; mutations.append(bad)
        bad = copy.deepcopy(original); bad['states'] = bad['states'][:-1]; mutations.append(bad)
        bad = copy.deepcopy(original); bad['states'][0]['reader'] = 0; mutations.append(bad)
        bad = copy.deepcopy(original); bad['states'][0]['extra'] = False; mutations.append(bad)
        for cert in mutations:
            with self.subTest(cert=cert), self.assertRaises(Rejected):
                verify(BAD, cert)
        stutter = copy.deepcopy(original)
        stutter['states'].insert(1, stutter['states'][0])
        self.assertTrue(verify(BAD, stutter)['accepted'])

    def test_closed_set_rejects_omissions_and_unsafe_members(self):
        original = produce(GOOD, 'closed-set')
        for index in range(len(original['states'])):
            cert = copy.deepcopy(original)
            cert['states'].pop(index)
            with self.assertRaises(Rejected):
                verify(GOOD, cert)
        with self.assertRaises(Rejected):
            verify(BAD, produce(BAD, 'closed-set'))

    def test_proof_rejects_forged_leaf_missing_case_and_wrong_variable(self):
        original = produce(GOOD, 'inductive')
        alternatives = [{'false': True}, {'false': 1}, {'split': 's.reader', 'zero': {'false': True}},
                        {'split': 'x', 'zero': {'false': True}, 'one': {'false': True}}]
        for bad_tree in alternatives:
            cert = copy.deepcopy(original)
            cert['proofs']['step'] = bad_tree
            with self.assertRaises(Rejected):
                verify(GOOD, cert)
        cert = copy.deepcopy(original)
        cert['proofs'].pop('step')
        with self.assertRaises(Rejected):
            verify(GOOD, cert)
        cert = copy.deepcopy(original)
        cert['proofs']['base']['zero']['split'] = 's.reader'
        with self.assertRaises(Rejected):
            verify(GOOD, cert)

    def test_forged_success_flag_not_accepted(self):
        cert = produce(GOOD, 'inductive') | {'status': 'passed'}
        with self.assertRaises(Rejected):
            verify(GOOD, cert)

    def test_initial_witness_is_checked(self):
        cert = produce(GOOD, 'inductive')
        cert['initial_witness']['writer'] = True
        with self.assertRaises(Rejected):
            verify(GOOD, cert)

    def test_duplicate_json_keys_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'bad.json'
            path.write_text('{"kind":"trace","kind":"inductive"}')
            with self.assertRaises(Rejected):
                read_json(path)

    def test_small_formula_soundness_and_partial_evaluation(self):
        atoms = [('bool', False), ('bool', True), ('var', 's', 'x'), ('var', 's', 'y')]
        formulas = atoms + [('!', a) for a in atoms]
        formulas += [(op, a, b) for op in ('&&', '||', '==', '!=') for a in formulas[:] for b in atoms]
        for formula in formulas:
            outcomes = []
            for x, y in itertools.product((False, True), repeat=2):
                expected = evaluate(formula, {'s': {'x': x, 'y': y}})
                self.assertEqual(truth(formula, {'s.x': x, 's.y': y}), expected)
                outcomes.append(expected)
            try:
                proof = tree(formula, ['s.x', 's.y'])
            except ValueError:
                self.assertTrue(any(outcomes))
            else:
                self.assertFalse(any(outcomes))
                check_tree(proof, formula, {'s.x', 's.y'})
            # Any result established with a partial assignment must hold in all completions.
            for x in (None, False, True):
                env = {} if x is None else {'s.x': x}
                result = truth(formula, env)
                if result is not None:
                    for xx, yy in itertools.product((False, True), repeat=2):
                        if x is None or x == xx:
                            self.assertEqual(result, evaluate(formula, {'s': {'x': xx, 'y': yy}}))


if __name__ == '__main__':
    unittest.main()
