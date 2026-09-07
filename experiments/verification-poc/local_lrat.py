"""Untrusted, intentionally small DPLL/RUP proof producer for local tests.
Use CaDiCaL for real search. Acceptance is exclusively in lrat.py.
"""
from lrat import dimacs


def prove(text, node_limit=4096, priority=()):
    count, clauses = dimacs(text)
    db = {i + 1: c for i, c in enumerate(clauses)}
    lines = []
    nodes = 0

    def propagate(decisions):
        assigned = set(decisions)
        hints = []
        while True:
            changed = False
            for ident, clause in db.items():
                if any(x in assigned for x in clause):
                    continue
                remaining = clause - {-x for x in assigned}
                if not remaining:
                    return True, hints + [ident], assigned
                if len(remaining) == 1:
                    assigned.add(next(iter(remaining)))
                    hints.append(ident)
                    changed = True
            if not changed:
                return False, hints, assigned

    def search(decisions):
        nonlocal nodes
        nodes += 1
        if nodes > node_limit:
            raise ValueError('local proof search resource limit')
        conflict, hints, assigned = propagate(decisions)
        if not conflict:
            unresolved = {abs(x) for clause in db.values() if not clause.intersection(assigned) for x in clause if -x not in assigned}
            order = dict.fromkeys([*priority, *sorted(unresolved)])
            variable = next((v for v in order if v in unresolved and v not in assigned and -v not in assigned), None)
            if variable is None:
                raise ValueError('SAT: no refutation exists')
            search(decisions + [variable])
            search(decisions + [-variable])
            conflict, hints, _ = propagate(decisions)
            if not conflict:
                raise ValueError('producer failed to derive a parent clause')
        ident = max(db, default=0) + 1
        clause = [-x for x in decisions]
        db[ident] = frozenset(clause)
        lines.append(' '.join(map(str, [ident, *clause, 0, *hints, 0])))
    search([])
    return '\n'.join(lines) + '\n'
