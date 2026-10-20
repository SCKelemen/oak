#!/usr/bin/env python3
"""Serial, resource-bounded kernel validation. Never accepts native/custom axioms."""
import argparse
import hashlib
import json
import os
import pathlib
import re
import signal
import subprocess
import sys
import time

HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parent.parent
SOURCES=ROOT/'spec/lean/Oak/ArmDecoderClassification'
ALLOWED={'propext','Classical.choice','Quot.sound'}

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def run(args, build, label, library=None):
    started=time.monotonic();peak=0;reason='exited'
    env=dict(os.environ);env['LEAN_PATH']=str(library or build)
    log=build/(label+'.log')
    with log.open('w') as output:
        process=subprocess.Popen(args,cwd=ROOT/'spec/lean',env=env,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
        while process.poll() is None:
            try:
                status=pathlib.Path('/proc/'+str(process.pid)+'/status').read_text()
                rss=int(next(x.split()[1] for x in status.splitlines() if x.startswith('VmRSS:')))
                available=int(next(x.split()[1] for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))
                peak=max(peak,rss)
                if rss>1024*1024 or available<1536*1024 or time.monotonic()-started>30:
                    reason='resource ceiling';os.killpg(process.pid,signal.SIGTERM);break
            except (FileNotFoundError,StopIteration):pass
            time.sleep(.1)
        try:code=process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid,signal.SIGKILL);code=process.wait()
    result={'label':label,'exit':code,'reason':reason,'seconds':round(time.monotonic()-started,2),'peak_rss_kib':peak,'command':args}
    (build/(label+'.json')).write_text(json.dumps(result,indent=2)+'\n')
    if code!=0 or reason!='exited':
        raise RuntimeError(f'{label}: {result}; see {log}')
    return result

def main():
    p=argparse.ArgumentParser();p.add_argument('--build-dir',type=pathlib.Path,required=True);p.add_argument('--source',type=pathlib.Path);args=p.parse_args()
    check=[sys.executable,str(HERE/'decoder_classification.py')]
    if args.source:check+=['--source',str(args.source)]
    subprocess.run(check,check=True)
    version=subprocess.check_output(['lean','--version'],cwd=ROOT/'spec/lean',text=True).strip()
    if not version.startswith('Lean (version 4.33.1,'):raise RuntimeError('unexpected Lean version: '+version)
    build=args.build_dir.resolve();build.mkdir(parents=True,exist_ok=True)
    out=build/'Oak/ArmDecoderClassification';out.mkdir(parents=True,exist_ok=True)
    paths=[SOURCES/'Checker.lean']+sorted(SOURCES.glob('Batch*.lean'))+[SOURCES/'Selection.lean',SOURCES/'Controls.lean']
    checker=sha(paths[0]);receipts={};total=0
    def dependencies(source):
        result={}
        for dep in re.findall(r'^import Oak\.ArmDecoderClassification\.([A-Za-z_0-9]+)$',source.read_text(),re.M):
            target=SOURCES/(dep+'.lean');result[dep]=sha(target);result.update(dependencies(target))
        return result
    for n,source in enumerate(paths):
        name=source.stem;olean=out/(name+'.olean');receipt=build/(name+'.receipt.json')
        deps=dependencies(source)
        identity={'source_sha256':sha(source),'checker_sha256':checker,'lean':version,'dependencies':deps,
                  'dependency_oleans':{dep:sha(out/(dep+'.olean')) for dep in deps}}
        # Cache is local build acceleration only; source/olean hashes must match.
        if receipt.exists() and olean.exists():
            old=json.loads(receipt.read_text())
            if old.get('identity')==identity and old.get('olean_sha256')==sha(olean):
                receipts[name]=old;continue
        result=run(['lean','-j1','-o',str(olean),str(source)],build,name)
        total+=result['seconds'];entry={'identity':identity,'olean_sha256':sha(olean),'measurement':result}
        receipt.write_text(json.dumps(entry,indent=2)+'\n');receipts[name]=entry
        print(f'{n+1}/{len(paths)} {name}: {result["seconds"]}s, {result["peak_rss_kib"]}KiB',flush=True)
    names=[]
    for path in paths:
        suffix='Data.' if path.stem.startswith('Batch') else ''
        for name in re.findall(r'^theorem ([A-Za-z_][A-Za-z_0-9.]*)\b',path.read_text(),re.M):names.append('Oak.ArmDecoderClassification.'+suffix+name)
    audit=build/'Audit.lean';audit.write_text('import Oak.ArmDecoderClassification.Selection\nimport Oak.ArmDecoderClassification.Controls\n'+''.join('#print axioms '+n+'\n' for n in names))
    run(['lean','-j1',str(audit)],build,'Audit')
    text=(build/'Audit.log').read_text();found={}
    for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text):
        if name in found:raise RuntimeError('duplicate audit declaration: '+name)
        axioms={a.strip() for a in raw.split(',') if a.strip()}
        if not axioms<=ALLOWED:raise RuntimeError('unapproved axioms: '+name+' '+str(axioms))
        found[name]=axioms
    for name in re.findall(r"'([^']+)' does not depend on any axioms",text):
        if name in found:raise RuntimeError('duplicate audit declaration: '+name)
        found[name]=set()
    if set(found)!=set(names):raise RuntimeError('missing/extra audited closures')
    (build/'validated.json').write_text(json.dumps({'lean':version,'closures':len(names),'sources':{p.name:sha(p) for p in paths},'receipts':receipts},indent=2)+'\n')
    print(f'Validated {len(names)} closures with standard-only axioms; newly built modules took {total:.2f}s.',flush=True)

if __name__=='__main__':main()
