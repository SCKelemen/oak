#!/usr/bin/env python3
"""Isolated typed-model CLI. Native Oak is default; offline mode is explicit."""
import argparse
from collections import deque
import json
from pathlib import Path
import subprocess
import sys
from circuit import digest
from finite_model import load, encode, value
from projections import emit
from local_lrat import prove
from verify import FORMAT, verify


def trace(model):
    states=model.states();queue=deque();seen=set()
    def key(s): return tuple(s.values())
    for s in states:
        if value(model.terms['initial'],{'s':s}): queue.append([s]);seen.add(key(s))
    while queue:
        path=queue.popleft();s=path[-1]
        if not value(model.terms['invariant'],{'s':s}):
            return {'format':FORMAT,'semantic_digest':model.digest,'kind':'trace','states':path}
        for t in states:
            if key(t) not in seen and value(model.terms['step'],{'s':s,'t':t}):
                seen.add(key(t));queue.append(path+[t])
    raise ValueError('no counterexample in the exhaustively explored finite model')


def local_proof(model):
    witness=next((s for s in model.states() if value(model.terms['initial'],{'s':s})),None)
    if witness is None: raise ValueError('empty initial set')
    proofs={}
    for role in ('base','step'):
        c,root=encode(model,role);cnf=c.dimacs(root)
        proofs[role]={'cnf_sha256':digest(cnf),'lrat':prove(cnf,priority=c.inputs.values())}
    return {'format':FORMAT,'semantic_digest':model.digest,'kind':'lrat','initial_witness':witness,'proofs':proofs}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('action',choices=('emit','prove-local','trace'))
    p.add_argument('project',type=Path);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--frontend',choices=('oak','experimental'),default='oak');a=p.parse_args()
    try:
        model=load(a.project,a.frontend)
        if a.action=='emit': result=emit(model,a.out)
        else:
            cert=local_proof(model) if a.action=='prove-local' else trace(model)
            result=verify(model,cert)
            a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(cert,indent=2)+'\n')
        print(json.dumps(result,indent=2));return 0
    except (ValueError,OSError,TypeError,RecursionError,subprocess.TimeoutExpired) as e:
        print(json.dumps({'accepted':False,'reason':str(e)}));return 1


if __name__=='__main__': sys.exit(main())
