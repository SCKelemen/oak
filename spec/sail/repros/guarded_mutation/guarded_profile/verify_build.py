"""Verify either the frozen local artifact or a fresh same-job source build.
A receipt is a build/provenance record, not a semantic correctness certificate.
CI creates it itself from the checked build script; it never consumes an
untrusted uploaded receipt as authority to select a different generator.
"""
import hashlib,json,os,pathlib,subprocess
from build import tree_hash, source_diff
HERE=pathlib.Path(__file__).resolve().parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def git(source,*args):return subprocess.check_output(['git','-C',str(source),*args])
def verified_generator():
 profile=json.loads((HERE/'profile.json').read_text())
 require(sha(HERE/'no-shadow.patch')==profile['patch_sha256'],'guarded patch drift')
 receipt_name=os.environ.get('OAK_RETURN_BUILD_RECEIPT')
 if not receipt_name:
  compiler=pathlib.Path(os.environ['OAK_RETURN_SAIL']).resolve()
  plugin=pathlib.Path(os.environ['SAIL_PLUGIN_DIR'])/'sail_plugin_lean.cmxs'
  require(sha(compiler)==profile['executable_sha256'],'wrong frozen local executable')
  require(sha(plugin)==profile['plugin_sha256'],'wrong frozen local plugin')
  return compiler
 receipt_path=pathlib.Path(receipt_name).resolve();receipt=json.loads(receipt_path.read_text())
 work=receipt_path.parent;source=work/'sources/sail'
 require(receipt['format']=='oak-guarded-source-build-v1','unknown build receipt format')
 require(receipt['official_base']==profile['official_base'],'wrong build source pin')
 require(receipt['patch_sha256']==profile['patch_sha256'],'wrong build patch')
 require(receipt['toolchain_lock_sha256']==sha(HERE/'toolchain-lock.json'),'dependency lock drift')
 require(receipt['build_script_sha256']==sha(HERE/'build.py'),'builder script drift')
 require(receipt['workdir']==str(work) and receipt['source_dir']==str(source),'unexpected build paths')
 require(receipt['ocaml_version']=='5.3.0' and receipt['dune_version']=='3.21.1','toolchain version drift')
 require(git(source,'rev-parse','HEAD').decode().strip()==profile['official_base'],'source checkout drift')
 require(git(source,'rev-parse','HEAD^{tree}').decode().strip()==receipt['source_tree'],'source tree drift')
 require(source_diff(source)==(HERE/'no-shadow.patch').read_bytes(),'source changes beyond exact patch')
 require(not git(source,'ls-files','--others','--exclude-standard').decode().strip(),'untracked source files')
 lock=json.loads((HERE/'toolchain-lock.json').read_text())
 for item in lock['packages']+lock['archives']:
  require(sha(work/'downloads'/item['file'])==item['sha256'],'build dependency drift: '+item['file'])
 require(tree_hash(work/'prefix')==receipt['prefix_tree_sha256'],'extracted toolchain drift')
 compiler=source/'_build/default/src/bin/sail.exe';plugin=source/'_build/default/src/sail_lean_backend/sail_plugin_lean.cmxs'
 require(sha(compiler)==receipt['executable_sha256'],'rebuilt executable changed')
 require(sha(plugin)==receipt['plugin_sha256'],'rebuilt plugin changed')
 expected={'OAK_RETURN_SAIL':compiler,'SAIL_DIR':source,'SAIL_PLUGIN_DIR':plugin.parent}
 for name,path in expected.items():
  if name in os.environ:require(pathlib.Path(os.environ[name]).resolve()==path,'wrong environment path: '+name)
  os.environ[name]=str(path)
 return compiler
