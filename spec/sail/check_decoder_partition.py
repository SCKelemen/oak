#!/usr/bin/env python3
"""Bounded two-worker kernel replay; receipts are local acceleration, not authority."""
import argparse
import concurrent.futures
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
LEAN=ROOT/'spec/lean'
SRC=LEAN/'Oak/ArmDecoderPartition'
ALLOWED={'propext','Classical.choice','Quot.sound'}
FLOOR_KIB=2*1024*1024

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def available():
    return int(next(x.split()[1] for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))

def run(cmd,build,name):
    # Wait at the launch boundary, never signal another worker's process.
    while available()<FLOOR_KIB:
        print('Launch paused below shared 2 GiB available-memory floor.',flush=True)
        time.sleep(5)
    env=dict(os.environ);env['LEAN_PATH']=str(build)
    start=time.monotonic();peak=0;reason='exited'
    with (build/(name+'.log')).open('w') as out:
        p=subprocess.Popen(cmd,cwd=LEAN,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
        while p.poll() is None:
            try:
                text=pathlib.Path(f'/proc/{p.pid}/status').read_text()
                rss=int(next(x.split()[1] for x in text.splitlines() if x.startswith('VmRSS:')));peak=max(peak,rss)
                if rss>1024*1024 or time.monotonic()-start>30 or available()<FLOOR_KIB:
                    reason='resource ceiling';os.killpg(p.pid,signal.SIGTERM);break
            except (FileNotFoundError,StopIteration):pass
            time.sleep(.1)
        try:code=p.wait(timeout=5)
        except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);code=p.wait()
    result={'exit':code,'reason':reason,'seconds':round(time.monotonic()-start,2),'peak_rss_kib':peak,'command':cmd}
    (build/(name+'.json')).write_text(json.dumps(result,indent=2)+'\n')
    if code or reason!='exited':raise RuntimeError(f'{name}: {result}; see {build/(name+".log")}')
    return result

def dependencies(source):
    result={}
    for name in re.findall(r'^import (Oak\.[A-Za-z_0-9.]+)$',source.read_text(),re.M):
        if name in result:continue
        path=LEAN/pathlib.Path(*name.split('.')).with_suffix('.lean')
        result[name]=path;result.update(dependencies(path))
    return result

def validate_classifier(old,version):
    """Require the complete prior graph, not a caller-selected subset of hashes."""
    base=LEAN/'Oak/ArmDecoderClassification'
    paths=[base/'Checker.lean']+sorted(base.glob('Batch*.lean'))+[base/'Selection.lean',base/'Controls.lean']
    summary=json.loads((old/'validated.json').read_text())
    if summary['lean']!=version:raise RuntimeError('classifier Lean identity')
    if set(summary['sources'])!={p.name for p in paths} or set(summary['receipts'])!={p.stem for p in paths}:raise RuntimeError('classifier graph inventory')
    for source in paths:
        name=source.stem;r=summary['receipts'][name];ident=r['identity'];m=r.get('measurement',{})
        if sha(source)!=summary['sources'][source.name] or ident['source_sha256']!=sha(source) or ident['lean']!=version:raise RuntimeError('classifier source/identity drift '+name)
        if m.get('exit')!=0 or m.get('reason')!='exited':raise RuntimeError('incomplete classifier module '+name)
        if sha(old/'Oak/ArmDecoderClassification'/(name+'.olean'))!=r['olean_sha256']:raise RuntimeError('classifier object drift '+name)
        deps=dependencies(source)
        expected={n.rsplit('.',1)[1]:sha(path) for n,path in deps.items()}
        if ident['dependencies']!=expected:raise RuntimeError('classifier dependency graph '+name)
        if 'dependency_oleans' in ident:
            objects={n.rsplit('.',1)[1]:sha(old/pathlib.Path(*n.split('.')).with_suffix('.olean')) for n in deps}
            if ident['dependency_oleans']!=objects:raise RuntimeError('classifier dependency objects '+name)
    byte=json.loads((old/'byte-binding.json').read_text())
    bridge=base/'ByteBinding.lean'
    if sha(bridge)!=byte['source_sha256'] or sha(old/'Oak/ArmDecoderClassification/ByteBinding.olean')!=byte['olean_sha256']:raise RuntimeError('byte bridge drift')
    core={n:p for n,p in dependencies(bridge).items() if not n.startswith('Oak.ArmDecoderClassification.')}
    if set(byte['core'])!=set(core):raise RuntimeError('core dependency inventory')
    for name,source in core.items():
        pins=byte['core'][name];rel=pathlib.Path(*name.split('.'))
        if sha(source)!=pins['source'] or sha(old/rel.with_suffix('.olean'))!=pins['olean']:raise RuntimeError('core drift '+name)
    return summary,byte

def module_identity(source,build,version):
    return {'source':sha(source),'lean':version,'dependencies':{n:{'source':sha(s),'olean':sha(build/pathlib.Path(*n.split('.')).with_suffix('.olean'))} for n,s in dependencies(source).items()}}

def verify_receipt(source,build,version,receipt):
    m=receipt.get('measurement',{})
    output=build/'Oak/ArmDecoderPartition'/(source.stem+'.olean')
    if receipt.get('identity')!=module_identity(source,build,version) or receipt.get('olean')!=sha(output) or m.get('exit')!=0 or m.get('reason')!='exited':raise RuntimeError('partition receipt drift '+source.stem)

def audit(paths,build):
    names=[]
    for p in paths:
        namespace=re.search(r'^namespace (\S+)',p.read_text(),re.M)[1]
        names += [namespace+'.'+n for n in re.findall(r'^theorem ([A-Za-z_][A-Za-z_0-9.]*)\b',p.read_text(),re.M)]
    source=build/'Audit.lean'
    source.write_text('import Oak.ArmDecoderPartition.Complete\nimport Oak.ArmDecoderPartition.Controls\n'+''.join('#print axioms '+n+'\n' for n in names))
    run(['lean','-j1',str(source)],build,'Audit')
    text=(build/'Audit.log').read_text();found={}
    for n,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text):
        axioms={x.strip() for x in raw.split(',') if x.strip()}
        if n in found or not axioms<=ALLOWED:raise RuntimeError('unapproved/duplicate closure '+n)
        found[n]=sorted(axioms)
    for n in re.findall(r"'([^']+)' does not depend on any axioms",text):
        if n in found:raise RuntimeError('duplicate closure '+n)
        found[n]=[]
    if set(found)!=set(names):raise RuntimeError('incomplete or extra closure audit')
    return found

def main():
    p=argparse.ArgumentParser();p.add_argument('--source',type=pathlib.Path,required=True)
    p.add_argument('--build-dir',type=pathlib.Path,required=True)
    p.add_argument('--classification-dir',type=pathlib.Path,required=True)
    p.add_argument('--jobs',type=int,choices=[1,2],default=2);a=p.parse_args()
    for script in ['copy_decoder_source_pages.py','decoder_partition.py']:
        subprocess.run([sys.executable,str(HERE/script),'--source',str(a.source)],check=True)
    version=subprocess.check_output(['lean','--version'],cwd=LEAN,text=True).strip()
    if not version.startswith('Lean (version 4.33.1,'):raise RuntimeError('Lean identity')
    build=a.build_dir.resolve();build.mkdir(parents=True,exist_ok=True)
    old=a.classification_dir.resolve()
    validate_classifier(old,version)
    (build/'Oak/ArmDecoderPartition').mkdir(parents=True,exist_ok=True)
    for path in (old/'Oak').iterdir():
        if path.name=='ArmDecoderPartition':continue
        link=build/'Oak'/path.name
        if link.is_symlink():
            if link.resolve()!=path.resolve():raise RuntimeError('dependency link drift')
        elif link.exists():raise RuntimeError('unexpected dependency path')
        else:link.symlink_to(path)
    validated=build/'validated.json'
    if validated.exists():validated.unlink()
    receipts={}
    def compile_one(source):
        name=source.stem;output=build/'Oak/ArmDecoderPartition'/(name+'.olean');receipt=build/(name+'.receipt.json')
        identity=module_identity(source,build,version)
        if receipt.exists() and output.exists():
            old_receipt=json.loads(receipt.read_text())
            m=old_receipt.get('measurement',{})
            if old_receipt.get('identity')==identity and old_receipt.get('olean')==sha(output) and m.get('exit')==0 and m.get('reason')=='exited':return name,old_receipt
        measurement=run(['lean','-j1','-o',str(output),str(source)],build,name)
        entry={'identity':identity,'olean':sha(output),'measurement':measurement}
        receipt.write_text(json.dumps(entry,indent=2)+'\n')
        print(f'{name}: {measurement["seconds"]}s/{measurement["peak_rss_kib"]}KiB',flush=True)
        return name,entry
    stages=[[SRC/'Bytes.lean'],[SRC/'Checker.lean',SRC/'Prefix.lean'],sorted(SRC.glob('SourceBatch*.lean')),sorted(SRC.glob('PageBatch*.lean')),sorted(SRC.glob('PartBatch*.lean'))+sorted(SRC.glob('PrefixBatch*.lean')),[SRC/'Declaration.lean',SRC/'Controls.lean'],[SRC/'Complete.lean']]
    paths=[s for stage in stages for s in stage]
    if set(SRC.glob('*.lean'))!=set(paths):raise RuntimeError('unexpected proof module inventory')
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
        for stage in stages:
            futures=[pool.submit(compile_one,s) for s in stage]
            try:
                for f in concurrent.futures.as_completed(futures):
                    name,r=f.result();receipts[name]=r
            except BaseException:
                for f in futures:f.cancel()
                raise
    closures=audit(paths,build)
    validate_classifier(old,version)
    for source in paths:verify_receipt(source,build,version,receipts[source.stem])
    result={'lean':version,'runner':sha(pathlib.Path(__file__)),'helpers':{name:sha(HERE/name) for name in ['copy_decoder_source_pages.py','decoder_partition.py']},'source':sha(a.source),'sources':{s.name:sha(s) for s in paths},'receipts':receipts,'closures':closures}
    validated.write_text(json.dumps(result,indent=2)+'\n')
    print(f'Validated {len(paths)} modules and {len(closures)} standard-only closures; full-source partition retained.',flush=True)

if __name__=='__main__':main()
