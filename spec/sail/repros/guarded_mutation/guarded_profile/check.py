#!/usr/bin/env python3
"""Regression gate for the separately pinned bounded generator experiment.
The official generator remains the source-evaluator oracle; raw output is never
edited. No universal source/export equivalence is inferred from these fixtures.
"""
import argparse, hashlib, json, os, pathlib, re, shutil, subprocess
HERE=pathlib.Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--output-dir',type=pathlib.Path,required=True);a=p.parse_args()
OUT=a.output_dir.resolve();OUT.mkdir(parents=True,exist_ok=True)
profile=json.loads((HERE/'profile.json').read_text())
from verify_build import verified_generator
compiler=verified_generator()
def require(ok,msg):
 if not ok: raise RuntimeError(msg)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
require(sha(HERE/'no-shadow.patch')==profile['patch_sha256'],'wrong experimental patch')
sourceenv=os.environ.copy();sourceenv.pop('SAIL_DIR',None);sourceenv.pop('SAIL_PLUGIN_DIR',None)
official=os.environ.get('SAIL','sail')
def run(args,cwd,log,env=None):
 r=subprocess.run(args,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
 (OUT/log).write_text(r.stdout);return r
v=run([official,'--version'],OUT,'official-version.log',sourceenv)
require(v.returncode==0 and v.stdout.strip()=='Sail 0.20.2 (sail2 @ 3b7af38d66466ecadad563158b07ce2f82fe05da)','wrong official source oracle')
(OUT/'run.isail').write_text('initialize_registers()\n:run\nmain()\n:run\n:quit\n')
def audit_axioms(output,evidence):
 expected=set(re.findall(r'^theorem\s+(\w+)',evidence.read_text(),re.M))
 require(bool(expected),'no fixture theorem declarations')
 rows=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",output,re.S)
 actual={name:{x.strip() for x in axioms.split(',') if x.strip()} for name,axioms in rows}
 require(len(rows)==len(actual) and set(actual)==expected,'missing/extra/duplicate fixture axiom report')
 allowed={'propext','Classical.choice','Quot.sound'}
 for name,axioms in actual.items():require(not (axioms-allowed),'unexpected axioms in '+name+': '+str(axioms-allowed))
support=pathlib.Path(os.environ['OAK_LEAN_SAIL_SUPPORT']).resolve()
expect={'effects':['normal=10','state=2','early=31','state=1','fallback=5','state=3'],
        'nonunit':['normal=1007','fallback=2009','early=31'],
        'typed_assignment':['probe(false,0)=100']}
negatives=['immutable','nested','pattern','loop','parameter','outer_before_shadow']
for name in list(expect)+negatives+['mutable']:
 shutil.copyfile(HERE/'fixtures'/f'{name}.sail',OUT/f'{name}.sail')
 oracle=run([official,f'{name}.sail','--is','run.isail'],OUT,name+'-source.log',sourceenv)
 if name=='mutable':
  require('var expression can only be used to declare new variables' in oracle.stdout,'mutable declaration semantics changed')
 else:
  require('Result = ()' in oracle.stdout and 'Error:' not in oracle.stdout,'source evaluator failed: '+name)
  for expected in expect.get(name,[]):require(expected in oracle.stdout,'source value mismatch: '+name)
 target=OUT/name;target.mkdir()
 exported=run([str(compiler),f'{name}.sail','--lean','--lean-single-file','--lean-output-dir',str(target),'--lean-lib-path',str(support)],OUT,name+'-export.log')
 if name in negatives:
  require(exported.returncode!=0 and 'Oak experimental no-shadow profile: shadowed binder x' in exported.stdout,'shadow accepted: '+name)
  require(not (target/'out').exists(),'rejected input created output: '+name)
 elif name=='mutable':require(exported.returncode!=0,'invalid mutable redeclaration accepted')
 else:
  require(exported.returncode==0,'admitted export failed: '+name)
  if name in ['effects','nonunit']:
   project=target/'out';raw_hash=sha(project/'Out.lean')
   (project/'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
   shutil.copyfile(HERE/'fixtures'/f'{name}_evidence.lean',project/'Evidence.lean')
   for command,label in [(['lake','update'],'update'),(['lake','build'],'build'),(['lake','env','lean','Evidence.lean'],'kernel')]:
    result=run(command,project,name+'-'+label+'.log')
    require(result.returncode==0 and 'sorryAx' not in result.stdout,'kernel regression failed: '+name)
    if label=='kernel':audit_axioms(result.stdout,project/'Evidence.lean')
   require(sha(project/'Out.lean')==raw_hash,'raw generated body was edited')
# The direct registered rewrite entry is guarded, not just the Lean pipeline.
shutil.copyfile(HERE/'before_remove_e_assign.isail',OUT/'direct.isail')
direct=run([str(compiler),'immutable.sail','--is','direct.isail'],OUT,'direct-shared-entry.log')
require('Oak experimental no-shadow profile: shadowed binder x' in direct.stdout,'direct rewrite did not reject shadow')
print('Six lexical-capture rejections; source-checked positive fixtures; kernel effect/failure/early-return/nonunit checks; direct shared-entry rejection passed.')
