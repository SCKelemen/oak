#!/usr/bin/env python3
"""Independent evidence acceptance. Does not import or run the search engine."""
import argparse
import itertools
import json
from pathlib import Path
import sys
from project import load_project

FORMAT = 'oak-evidence-1'


class Rejected(ValueError):
    pass


def require(condition, reason):
    if not condition:
        raise Rejected(reason)


def exact(value, keys):
    require(type(value) is dict and set(value) == set(keys), 'unexpected or missing evidence fields')


def read_json(path):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    require(path.stat().st_size <= 2_000_000, 'evidence exceeds prototype size limit')
    return json.loads(path.read_text(), object_pairs_hook=pairs)


def state(value, fields):
    exact(value, fields)
    require(all(type(v) is bool for v in value.values()), 'state fields must be actual Booleans')
    return tuple(value[f] for f in fields)


def truth(expr, assignment):
    """Three-valued partial evaluation; None means not established."""
    op = expr[0]
    if op == 'bool':
        return expr[1]
    if op == 'var':
        return assignment.get(expr[1] + '.' + expr[2])
    a = truth(expr[1], assignment)
    if op == '!':
        return None if a is None else not a
    b = truth(expr[2], assignment)
    if op == '&&':
        if a is False or b is False:
            return False
        return True if a is True and b is True else None
    if op == '||':
        if a is True or b is True:
            return True
        return False if a is False and b is False else None
    require(op in ('==', '!='), 'unsupported logical operator')
    if a is None or b is None:
        return None
    return (a == b) if op == '==' else (a != b)


def assignment(**states):
    return {p + '.' + f: v for p, s in states.items() for f, v in s.items()}


def instantiate(expr, old, new):
    if expr[0] == 'var':
        return ('var', new if expr[1] == old else expr[1], expr[2])
    if expr[0] == 'bool':
        return expr
    return (expr[0], *(instantiate(x, old, new) for x in expr[1:]))


def obligations(terms):
    return {
        'base': ('&&', terms['initial'], ('!', terms['invariant'])),
        'step': ('&&', ('&&', terms['invariant'], terms['step']),
                 ('!', instantiate(terms['invariant'], 's', 't'))),
    }


def check_tree(tree, formula, allowed, env=None):
    """Rules: false leaf; or both Boolean cases of a fresh variable."""
    env = {} if env is None else env
    require(type(tree) is dict, 'proof node must be an object')
    if set(tree) == {'false'}:
        require(tree['false'] is True, 'false leaf must have literal true marker')
        require(truth(formula, env) is False, 'leaf does not establish falsity')
        return 1
    exact(tree, ('split', 'zero', 'one'))
    variable = tree['split']
    require(type(variable) is str and variable in allowed, 'unknown split variable')
    require(variable not in env, 'repeated split variable')
    # Both branches mandatory, and their assignments cannot be supplied by evidence.
    return 1 + check_tree(tree['zero'], formula, allowed, env | {variable: False}) + check_tree(tree['one'], formula, allowed, env | {variable: True})


def verify(project, evidence):
    model, terms, digest = load_project(project)
    require(type(evidence) is dict, 'evidence must be an object')
    require(evidence.get('format') == FORMAT, 'unsupported format')
    require(evidence.get('semantic_digest') == digest, 'evidence belongs to a different source/project/version')
    kind = evidence.get('kind')
    common = ('format', 'semantic_digest', 'kind')
    fields = model.fields
    if kind == 'trace':
        exact(evidence, (*common, 'states'))
        states = evidence['states']
        require(type(states) is list and 1 <= len(states) <= 4096, 'invalid trace length')
        for s in states:
            state(s, fields)
        require(truth(terms['initial'], assignment(s=states[0])) is True, 'trace does not start in an initial state')
        for s, t in zip(states, states[1:]):
            require(s == t or truth(terms['step'], assignment(s=s, t=t)) is True, 'trace contains an illegal transition')
        require(truth(terms['invariant'], assignment(s=states[-1])) is False, 'trace does not end in a safety violation')
        return {'accepted': True, 'claim': 'reachable safety counterexample', 'states': len(states)}
    if kind == 'inductive':
        exact(evidence, (*common, 'initial_witness', 'proofs'))
        state(evidence['initial_witness'], fields)
        require(truth(terms['initial'], assignment(s=evidence['initial_witness'])) is True, 'invalid initial witness')
        exact(evidence['proofs'], ('base', 'step'))
        counts = {}
        for name, formula in obligations(terms).items():
            allowed = {p + '.' + f for p in (('s',) if name == 'base' else ('s', 't')) for f in fields}
            counts[name] = check_tree(evidence['proofs'][name], formula, allowed)
        return {'accepted': True, 'claim': 'nonvacuous inductive safety', 'proof_nodes': counts}
    require(kind == 'closed-set', 'unsupported evidence kind')
    exact(evidence, (*common, 'states'))
    supplied = evidence['states']
    require(type(supplied) is list and 1 <= len(supplied) <= 2 ** len(fields), 'invalid closed-set size')
    keys = [state(s, fields) for s in supplied]
    require(len(set(keys)) == len(keys), 'duplicate states')
    universe = [dict(zip(fields, bits)) for bits in itertools.product((False, True), repeat=len(fields))]
    initial = [s for s in universe if truth(terms['initial'], assignment(s=s)) is True]
    require(bool(initial), 'empty initial set')
    require(all(state(s, fields) in keys for s in initial), 'certificate omits an initial state')
    for s in supplied:
        require(truth(terms['invariant'], assignment(s=s)) is True, 'certificate includes unsafe state')
        for t in universe:
            if truth(terms['step'], assignment(s=s, t=t)) is True:
                require(state(t, fields) in keys, 'certificate is not closed under transitions')
    return {'accepted': True, 'claim': 'finite-state safety via closed invariant set', 'states': len(keys)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('project', type=Path)
    parser.add_argument('evidence', type=Path)
    args = parser.parse_args()
    try:
        result = verify(args.project, read_json(args.evidence))
        print(json.dumps(result, indent=2))
        return 0
    except (ValueError, OSError, RecursionError, TypeError) as error:
        print(json.dumps({'accepted': False, 'reason': str(error)}))
        return 1


if __name__ == '__main__':
    sys.exit(main())
