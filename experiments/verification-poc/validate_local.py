#!/usr/bin/env python3
"""Reproduce available validation and record unavailable integration gates."""
import argparse
import datetime
import json
from pathlib import Path
import subprocess
import sys
import unittest
from finite_model import ROOT,load
from finite import local_proof,trace


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out',type=Path,default=ROOT/'build/validation-v3.json');a=p.parse_args()
    suite=unittest.defaultTestLoader.discover(str(ROOT));result=unittest.TextTestRunner(verbosity=1).run(suite)
    folder=ROOT/'examples/evidence-v3';folder.mkdir(exist_ok=True)
    checks=[]
    for name,safe in [('enum',True),('counter',True),('wrap',True),('enum-broken',False),('counter-broken',False)]:
        m=load(ROOT/f'examples/native/{name}.json','experimental');cert=local_proof(m) if safe else trace(m)
        path=folder/(name+'.json');path.write_text(json.dumps(cert,indent=2)+'\n')
        command=[sys.executable,'verify.py',f'examples/native/{name}.json',str(path.relative_to(ROOT)),'--frontend','experimental']
        r=subprocess.run(command,cwd=ROOT,capture_output=True,text=True)
        checks.append({'command':command[1:],'exit_code':r.returncode,'result':json.loads(r.stdout)})
    # Run the real gate: unavailable tools must result in a non-passing report.
    r=subprocess.run([sys.executable,'backend_suite.py','--out','build/native-integration'],cwd=ROOT,capture_output=True,text=True)
    integration=json.loads(r.stdout);integration.pop('attempt',None)
    report={'format':'oak-validation-3','recorded_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'tests':{'run':result.testsRun,'passed':result.testsRun-len(result.errors)-len(result.failures)-len(result.skipped),'failures':len(result.failures),'errors':len(result.errors),'skipped':[reason for _,reason in result.skipped]},
            'local_evidence':checks,'external_integration_exit_code':r.returncode,'external_integration':integration,
            'scope':'Tests use the explicit experimental frontend unless stated. Synthetic importer fixtures are not external tool execution. No self-verification or compiler-refinement claim.'}
    a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    # Local command success is separate from the external gate's result.
    return 0 if result.wasSuccessful() and all(c['exit_code']==0 for c in checks) else 1


if __name__=='__main__':sys.exit(main())
