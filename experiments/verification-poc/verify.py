#!/usr/bin/env python3
"""Check finite-model evidence by reconstructing the source obligation."""
import argparse
import json
from pathlib import Path
import sys
import subprocess
from circuit import digest
from evidence import read_json, exact
from finite_model import load, encode, value, need
import lrat

FORMAT='oak-evidence-2'


def verify(model, cert):
    need(type(cert) is dict and cert.get('format')==FORMAT,'unsupported evidence format')
    need(cert.get('semantic_digest')==model.digest,'evidence belongs to a different source/frontend/project')
    kind=cert.get('kind')
    if kind=='trace':
        exact(cert,('format','semantic_digest','kind','states'))
        states=cert['states'];need(type(states) is list and 0<len(states)<=4096,'invalid trace')
        for s in states: model.valid_state(s)
        need(value(model.terms['initial'],{'s':states[0]}),'invalid initial state')
        for s,t in zip(states,states[1:]): need(s==t or value(model.terms['step'],{'s':s,'t':t}),'illegal transition')
        need(not value(model.terms['invariant'],{'s':states[-1]}),'trace does not end in a safety violation')
        return {'accepted':True,'claim':'reachable safety counterexample','states':len(states)}
    need(kind=='lrat','unsupported evidence kind')
    exact(cert,('format','semantic_digest','kind','initial_witness','proofs'))
    model.valid_state(cert['initial_witness']);need(value(model.terms['initial'],{'s':cert['initial_witness']}),'invalid initial witness')
    exact(cert['proofs'],('base','step'))
    results={}
    for role,proof in cert['proofs'].items():
        exact(proof,('cnf_sha256','lrat'))
        need(type(proof['lrat']) is str and len(proof['lrat'])<=50_000_000,'invalid proof text')
        c,root=encode(model,role);text=c.dimacs(root)
        need(proof['cnf_sha256']==digest(text),'proof CNF does not match reconstructed obligation')
        results[role]=lrat.check(text,proof['lrat'])
    return {'accepted':True,'claim':'nonvacuous inductive safety','evidence':'independently checked LRAT','frontend':model.frontend,'translation_trusted':True,'obligations':results}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('project',type=Path);p.add_argument('certificate',type=Path)
    p.add_argument('--frontend',choices=('oak','experimental'),default='oak')
    a=p.parse_args()
    try:
        print(json.dumps(verify(load(a.project,a.frontend),read_json(a.certificate)),indent=2));return 0
    except (ValueError,OSError,TypeError,RecursionError,subprocess.TimeoutExpired) as error:
        print(json.dumps({'accepted':False,'reason':str(error)}));return 1


if __name__=='__main__': sys.exit(main())
