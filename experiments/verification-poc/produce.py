#!/usr/bin/env python3
"""Untrusted example evidence producer. The checker does not call this module."""
import argparse
import itertools
import json
from pathlib import Path
import sys
from project import load_project, finite_check, evaluate, rename_state


def tree(formula, variables, env=None):
    env = {} if env is None else env
    if not variables:
        states = {}
        for key, value in env.items():
            p, f = key.split('.')
            states.setdefault(p, {})[f] = value
        if evaluate(formula, states):
            raise ValueError('obligation has a satisfying assignment; no refutation produced')
        return {'false': True}
    v, *rest = variables
    return {'split': v, 'zero': tree(formula, rest, env | {v: False}),
            'one': tree(formula, rest, env | {v: True})}


def produce(path, kind):
    model, terms, digest = load_project(path)
    result = {'format': 'oak-evidence-1', 'semantic_digest': digest, 'kind': kind}
    states = [dict(zip(model.fields, bits)) for bits in itertools.product((False, True), repeat=len(model.fields))]
    initials = [s for s in states if evaluate(terms['initial'], {'s': s})]
    if not initials:
        raise ValueError('empty initial set')
    if kind == 'trace':
        report = finite_check(model, terms)
        if report['status'] != 'counterexample':
            raise ValueError('no counterexample found')
        return result | {'states': report['trace']}
    if kind == 'closed-set':
        reached = list(initials)
        for s in reached:
            for t in states:
                if evaluate(terms['step'], {'s': s, 't': t}) and t not in reached:
                    reached.append(t)
        # Deliberately leaves acceptance to the checker, even for an unsafe set.
        return result | {'states': reached}
    base = ('&&', terms['initial'], ('!', terms['invariant']))
    step = ('&&', ('&&', terms['invariant'], terms['step']), ('!', rename_state(terms['invariant'], 's', 't')))
    return result | {'initial_witness': initials[0], 'proofs': {
        'base': tree(base, ['s.' + f for f in model.fields]),
        'step': tree(step, [p + '.' + f for p in ('s', 't') for f in model.fields])}}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('project', type=Path)
    p.add_argument('--kind', choices=('trace', 'inductive', 'closed-set'), required=True)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    try:
        cert = produce(args.project, args.kind)
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(cert, indent=2) + '\n')
        print(f'Wrote candidate evidence: {args.out}; run evidence.py to check it.')
        return 0
    except (ValueError, OSError, RecursionError) as error:
        # A failed run must not leave an older successful artifact at this path.
        args.out.unlink(missing_ok=True)
        print(str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
