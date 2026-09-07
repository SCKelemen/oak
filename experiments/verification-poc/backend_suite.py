#!/usr/bin/env python3
"""Pinned integration gate. Missing tools, unknown answers and timeouts fail.
This runner never installs tools and never treats Z3 unsat as an LRAT proof.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from finite_model import ROOT, load, value, need
from projections import emit, bmc
from circuit import digest
from import_trace import receipt, import_trace
from verify import FORMAT, verify

LOCK=json.loads((ROOT/'tools.lock.json').read_text())
SUITE=(('enum',True,3),('enum-broken',False,3),('counter',True,5),('counter-broken',False,5),('wrap',True,3))


def run(command,folder,timeout):
    try:
        p=subprocess.run(command,cwd=folder,capture_output=True,text=True,timeout=timeout)
        return {'command':command,'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
    except (OSError,subprocess.TimeoutExpired) as e:
        return {'command':command,'error':str(e),'exit_code':None,'stdout':'','stderr':''}


def probe(name,folder,timeout,jar=None):
    if name=='tlc':
        need(jar is not None and jar.is_file(),'TLC jar unavailable; pass --tla-jar')
        sha=hashlib.sha256(jar.read_bytes()).hexdigest()
        need(sha==LOCK['tlc']['sha256'],'TLC jar does not match pinned artifact')
        result=run(['java','-version'],folder,timeout)
        need(result['exit_code']==0,'Java unavailable')
        match=re.search(r'version "(\d+)',result['stderr']+result['stdout'])
        need(match and int(match[1])>=17,'Java 17+ required')
        return {'available':True,'sha256':sha,'probe':result}
    executable=shutil.which(name);need(executable is not None,f'{name} unavailable')
    result=run([executable,'version' if name=='go' else '-version' if name=='z3' else '--version'],folder,timeout)
    need(result['exit_code']==0,'version probe failed')
    banner=result['stdout']+'\n'+result['stderr']
    need(re.search(r'(?<![\d.])'+re.escape(LOCK[name]['version'])+r'(?![\d.])',banner),'tool version does not match tools.lock.json')
    return {'available':True,'probe':result}


def backend(model,name,out,safe,bound,timeout,jar):
    logs=[]
    def call(command):
        r=run(command,out,timeout);logs.append(r)
        need(r['exit_code'] is not None,r.get('error','execution failed'));return r
    try:
        if name=='z3':
            for role,expected in (('initial','sat'),('base','unsat'),('step','unsat' if safe else 'sat')):
                r=call(['z3','-smt2',str(out/f'{role}.smt2')]);need(r['exit_code']==0 and r['stdout'].strip()==expected,f'unexpected Z3 {role} result')
            query=bmc(model,bound);(out/'bmc.smt2').write_text(query)
            r=call(['z3','-smt2',str(out/'bmc.smt2')]);need(r['exit_code']==0 and r['stdout'].strip()==('unsat' if safe else 'sat'),'unexpected Z3 BMC result')
            if not safe:
                query=bmc(model,bound,True);(out/'bmc-values.smt2').write_text(query)
                r=call(['z3','-smt2',str(out/'bmc-values.smt2')]);need(r['exit_code']==0,'get-value failed')
                raw=r['stdout'];record=receipt(model,'z3',query,raw,bound)
                cert=import_trace(model,'z3',query,raw,record,bound)
                (out/'z3-output.txt').write_text(raw);(out/'z3-receipt.json').write_text(json.dumps(record,indent=2)+'\n')
                (out/'z3-trace.json').write_text(json.dumps(cert,indent=2)+'\n')
        elif name=='tlc':
            rawpath=out/'tlc-trace.json'
            r=call(['java','-cp',str(jar),'tlc2.TLC','-workers','1','-dumpTrace','json',str(rawpath),'-metadir',str(out/'states'),'-config','Model.cfg','Model.tla'])
            log=r['stdout']+r['stderr']
            if safe:
                need(r['exit_code']==0 and 'Model checking completed. No error has been found.' in log,'TLC did not report completed safety check')
            else:
                need(r['exit_code']!=0 and 'Invariant Safe is violated' in log and rawpath.is_file(),'TLC did not produce the expected safety violation')
                raw=rawpath.read_text();query=(out/'Model.tla').read_text()+'\n'+(out/'Model.cfg').read_text()
                record=receipt(model,'tlc',query,raw);cert=import_trace(model,'tlc',query,raw,record)
                (out/'tlc-receipt.json').write_text(json.dumps(record,indent=2)+'\n');(out/'tlc-evidence.json').write_text(json.dumps(cert,indent=2)+'\n')
        elif name=='lean':
            # Expected rejection of a broken theorem cannot distinguish a false
            # claim from malformed code. First compile exactly its definitions.
            code=(out/'Model.lean').read_text()
            defs=code.split('theorem base (',1)[0]+'end OakFinite\n'
            (out/'Definitions.lean').write_text(defs)
            r=call(['lean',str(out/'Definitions.lean')]);need(r['exit_code']==0,'Lean definition projection failed')
            r=call(['lean',str(out/'Model.lean')])
            need(r['exit_code']==0 if safe else r['exit_code']!=0,'unexpected Lean theorem outcome')
        elif name=='cadical':
            proofs={}
            for role,expected in (('initial',10),('base',20),('step',20 if safe else 10)):
                proof=out/f'{role}.cadical.lrat'
                r=call(['cadical','--lrat','--no-binary',str(out/f'{role}.cnf'),str(proof)])
                need(r['exit_code']==expected,f'unexpected CaDiCaL {role} outcome')
                if expected==20:
                    import lrat
                    cnf=(out/f'{role}.cnf').read_text();text=proof.read_text();lrat.check(cnf,text)
                    proofs[role]={'cnf_sha256':digest(cnf),'lrat':text}
            if safe:
                witness=next((s for s in model.states() if value(model.terms['initial'],{'s':s})),None)
                cert={'format':FORMAT,'semantic_digest':model.digest,'kind':'lrat','initial_witness':witness,'proofs':proofs}
                verify(model,cert);(out/'cadical-evidence.json').write_text(json.dumps(cert,indent=2)+'\n')
        return {'passed':True,'expected_safety':safe,'logs':logs}
    except (ValueError,OSError,TypeError,KeyError,RecursionError) as e:
        return {'passed':False,'reason':str(e),'logs':logs}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--frontend',choices=('oak','experimental'),default='oak')
    p.add_argument('--tla-jar',type=Path);p.add_argument('--out',type=Path,default=ROOT/'build/integration')
    p.add_argument('--timeout',type=float,default=60);a=p.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    # Unique attempt directories prevent stale trace/certificate reuse.
    attempt=Path(tempfile.mkdtemp(prefix='attempt-',dir=a.out.resolve()))
    report={'format':'oak-integration-1','passed':False,'frontend':a.frontend,'attempt':str(attempt),'tools':{},'models':{}}
    jar=a.tla_jar.resolve() if a.tla_jar else None
    for name in ('go','lean','z3','cadical','tlc'):
        try: report['tools'][name]=probe(name,attempt,a.timeout,jar)
        except (ValueError,OSError) as e: report['tools'][name]={'available':False,'reason':str(e)}
    for name,safe,bound in SUITE:
        results={};report['models'][name]=results
        try:
            if a.frontend=='oak': need(report['tools']['go']['available'],'pinned Oak/Go frontend unavailable')
            model=load(ROOT/f'examples/native/{name}.json',a.frontend,a.timeout)
            if a.frontend=='oak':
                reference=load(ROOT/f'examples/native/{name}.json','experimental')
                need(model.doc==reference.doc,'native/reference frontend disagreement')
            out=attempt/name;emit(model,out)
            results['semantic_digest']=model.digest
            for tool in ('lean','z3','cadical','tlc'):
                results[tool]=backend(model,tool,out,safe,bound,a.timeout,jar) if report['tools'][tool]['available'] else {'passed':False,'unavailable':True}
        except (ValueError,OSError,TypeError,subprocess.TimeoutExpired) as e: results['error']=str(e)
    required=('go','lean','z3','cadical','tlc') if a.frontend=='oak' else ('lean','z3','cadical','tlc')
    report['passed']=all(report['tools'][t]['available'] for t in required) and all(all(v.get(t,{}).get('passed',False) for t in ('lean','z3','cadical','tlc')) for v in report['models'].values())
    (a.out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2));return 0 if report['passed'] else 2


if __name__=='__main__': sys.exit(main())
