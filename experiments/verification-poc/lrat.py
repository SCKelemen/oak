#!/usr/bin/env python3
"""Independent ASCII LRAT RUP/deletion checker (CaDiCaL 2.1.3 subset).

Negative RAT hints and binary LRAT are explicitly unsupported. This module has
no dependency on Oak, the CNF encoder, or the proof producer.
"""
import argparse
import json
from pathlib import Path
import sys


class InvalidProof(ValueError):
    pass


def need(ok, why):
    if not ok:
        raise InvalidProof(why)


def dimacs(text):
    header = None
    data = []
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith('c'):
            continue
        if line.startswith('p'):
            need(header is None and not data, 'duplicate or misplaced DIMACS header')
            words = line.split()
            need(len(words) == 4 and words[:2] == ['p', 'cnf'], 'invalid DIMACS header')
            header = tuple(map(int, words[2:]))
            need(all(x >= 0 for x in header), 'negative DIMACS counts')
        else:
            need(header is not None, 'missing DIMACS header')
            data.extend(map(int, line.split()))
    need(header is not None, 'missing DIMACS header')
    clauses, clause = [], []
    for lit in data:
        if lit == 0:
            clauses.append(frozenset(clause)); clause = []
        else:
            need(abs(lit) <= header[0], 'literal exceeds declared variable domain')
            clause.append(lit)
    need(not clause and (not data or data[-1] == 0), 'unterminated clause')
    need(len(clauses) == header[1], 'clause count mismatch')
    return header[0], clauses


def rup(database, clause, hints):
    # Assumed TRUE literals are precisely the negated proposed clause.
    assigned = {-lit for lit in clause}
    for hint in hints:
        need(hint > 0, 'RAT/negative hints unsupported; use ASCII RUP LRAT')
        need(hint in database, 'hint refers to absent/deleted/future clause')
    if any(-lit in assigned for lit in assigned):
        return  # tautological proposed clause
    for position, hint in enumerate(hints):
        premise = database[hint]
        need(not any(lit in assigned for lit in premise), 'hint clause is already satisfied')
        remaining = premise - {-lit for lit in assigned}
        if not remaining:
            need(position == len(hints) - 1, 'unused hints after conflict')
            return
        need(len(remaining) == 1, 'hint is neither unit nor conflicting')
        assigned.add(next(iter(remaining)))
    raise InvalidProof('RUP chain did not derive a conflict')


def check(cnf_text, proof_text):
    variables, clauses = dimacs(cnf_text)
    database = {i + 1: c for i, c in enumerate(clauses)}
    last_added = len(database)
    has_empty = any(not c for c in clauses)
    additions = deletions = 0
    for number, line in enumerate(proof_text.splitlines(), 1):
        words = line.split()
        if not words or words[0] == 'c':
            continue
        try:
            need(len(words) >= 3, 'short LRAT line')
            identifier = int(words[0])
            if words[1] == 'd':
                ids = list(map(int, words[2:]))
                need(identifier >= last_added and ids[-1] == 0 and all(x > 0 for x in ids[:-1]), 'invalid deletion line')
                need(len(ids[:-1]) == len(set(ids[:-1])), 'duplicate deletion')
                for removed in ids[:-1]:
                    need(removed in database, 'deletion refers to absent clause')
                    del database[removed]
                    deletions += 1
                continue
            need(identifier > last_added, 'addition ids must strictly increase')
            values = list(map(int, words[1:]))
            need(values.count(0) == 2 and values[-1] == 0, 'expected clause and hints terminated by zero')
            split = values.index(0)
            clause, hints = frozenset(values[:split]), values[split + 1:-1]
            need(all(abs(x) <= variables for x in clause), 'proof uses an undeclared variable')
            rup(database, clause, hints)
            database[identifier] = clause
            last_added = identifier
            additions += 1
            has_empty |= not clause
        except (ValueError, IndexError) as error:
            raise InvalidProof(f'LRAT line {number}: {error}') from error
    need(has_empty, 'proof never establishes the empty clause')
    return {'accepted': True, 'claim': 'CNF unsatisfiable', 'format': 'ASCII LRAT RUP/deletion', 'additions': additions, 'deletions': deletions}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('cnf', type=Path); p.add_argument('proof', type=Path)
    a = p.parse_args()
    try:
        need(a.cnf.stat().st_size < 20_000_000 and a.proof.stat().st_size < 50_000_000, 'prototype input size limit')
        print(json.dumps(check(a.cnf.read_text(), a.proof.read_text()), indent=2))
        return 0
    except (ValueError, OSError) as error:
        print(json.dumps({'accepted': False, 'reason': str(error)})); return 1


if __name__ == '__main__':
    sys.exit(main())
