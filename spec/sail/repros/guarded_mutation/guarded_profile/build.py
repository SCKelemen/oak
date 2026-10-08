#!/usr/bin/env python3
"""Rebuild the bounded generator from pinned official artifacts in a prefix.
No opam installation, system configuration, or sandbox/security change is used.
The receipt binds source+patch+dependencies to this build's binary hashes; it
never relabels a new build as the older local binary artifact profile.
"""
import argparse, hashlib, json, os, pathlib, platform, shlex, shutil, subprocess, tarfile, urllib.request
HERE=pathlib.Path(__file__).resolve().parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def tree_hash(root):
 h=hashlib.sha256()
 for p in sorted(root.rglob('*')):
  if p.is_symlink(): value='link:'+os.readlink(p)
  elif p.is_file():value=sha(p)
  else:continue
  h.update((str(p.relative_to(root))+'\0'+value+'\n').encode())
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--workdir',type=pathlib.Path,required=True)
 p.add_argument('--download-cache',type=pathlib.Path);p.add_argument('--source-cache',type=pathlib.Path)
 a=p.parse_args();work=a.workdir.resolve()
 require(platform.system()=='Linux' and platform.machine()=='x86_64','this dependency lock supports Linux x86_64')
 require(not work.exists() or not any(work.iterdir()),'build directory must be empty')
 work.mkdir(parents=True,exist_ok=True)
 lock=json.loads((HERE/'toolchain-lock.json').read_text());profile=json.loads((HERE/'profile.json').read_text())
 require(sha(HERE/'no-shadow.patch')==profile['patch_sha256'],'patch drift')
 downloads=work/'downloads';prefix=work/'prefix';sources=work/'sources';bindir=work/'bin'
 for d in [downloads,prefix,sources,bindir]:d.mkdir()
 cache=a.download_cache.resolve() if a.download_cache else None
 def command(args,cwd=work,env=None,timeout=1800):
  print('+',shlex.join(map(str,args)),flush=True)
  subprocess.run(list(map(str,args)),cwd=cwd,env=env,check=True,timeout=timeout)
 def artifact(item):
  dest=downloads/item['file'];cached=None
  if cache:
   cached=next((p for p in [cache/item['file'],cache/'debs'/item['file']] if p.is_file()),None)
  if cached:shutil.copyfile(cached,dest)
  else:
   require(item['url'].startswith(('https://snapshot.debian.org/','https://github.com/')),'unexpected artifact authority')
   with urllib.request.urlopen(item['url'],timeout=180) as response, dest.open('wb') as output:shutil.copyfileobj(response,output)
  require(sha(dest)==item['sha256'],'artifact checksum mismatch: '+item['file'])
  if cache and not cached:
   cache.mkdir(parents=True,exist_ok=True);shutil.copyfile(dest,cache/item['file'])
  return dest
 for item in lock['packages']:command(['dpkg-deb','-x',artifact(item),prefix])
 for item in lock['archives']:
  archive=artifact(item)
  with tarfile.open(archive) as tf:
   for member in tf.getmembers():
    path=pathlib.PurePosixPath(member.name)
    require(not path.is_absolute() and '..' not in path.parts,'unsafe archive member')
   tf.extractall(sources,filter='data')
 ocamllib=prefix/'usr/lib/x86_64-linux-gnu/ocaml/5.3.0'
 (work/'ld.conf').write_text(str(ocamllib/'stublibs')+'\n')
 (work/'findlib.conf').write_text(f'destdir="{ocamllib}"\npath="{ocamllib}:{ocamllib}/METAS"\nldconf="{work}/ld.conf"\n')
 wrappers={'ocaml':f'exec {shlex.quote(str(prefix/"usr/bin/ocamlrun"))} {shlex.quote(str(prefix/"usr/bin/ocaml"))} "$@"',
           'ocamlfind':f'exec {shlex.quote(str(prefix/"usr/bin/ocamlfind"))} "$@"',
           'dune':f'exec {shlex.quote(str(sources/"dune-3.21.1/_boot/dune.exe"))} "$@"'}
 for name,body in wrappers.items():
  f=bindir/name;f.write_text('#!/bin/sh\n'+body+'\n');f.chmod(0o755)
 env=os.environ.copy();env.update(OCAMLLIB=str(ocamllib),OCAMLPATH=str(ocamllib),CAML_LD_LIBRARY_PATH=str(ocamllib/'stublibs'),OCAMLFIND_CONF=str(work/'findlib.conf'),LEMLIB=str(prefix/'usr/share/lem/library'))
 env['PATH']=str(bindir)+':'+str(prefix/'usr/bin')+':'+str(sources/'ott-0.34/bin')+':'+env['PATH']
 command(['ocaml','boot/bootstrap.ml'],sources/'dune-3.21.1',env)
 command(['make','-j1','world'],sources/'ott-0.34',env)
 require(subprocess.check_output(['ocamlc','-version'],env=env,text=True).strip()=='5.3.0','OCaml version drift')
 require(subprocess.check_output(['dune','--version'],env=env,text=True).strip()=='3.21.1','Dune version drift')
 src=sources/'sail';base=profile['official_base']
 if a.source_cache:
  command(['git','clone','--shared','--no-checkout',a.source_cache.resolve(),src])
 else:
  command(['git','init','-q',src]);command(['git','-C',src,'remote','add','origin','https://github.com/rems-project/sail.git'])
  command(['git','-C',src,'fetch','--depth','1','origin',base])
 command(['git','-C',src,'checkout','--detach',base])
 require(subprocess.check_output(['git','-C',src,'rev-parse','HEAD'],text=True).strip()==base,'wrong source revision')
 command(['git','-C',src,'apply','--check',HERE/'no-shadow.patch'])
 command(['git','-C',src,'apply',HERE/'no-shadow.patch'])
 expected=(HERE/'no-shadow.patch').read_bytes()
 require(subprocess.check_output(['git','-C',src,'diff','--binary','HEAD'])==expected,'source patch mismatch')
 command(['dune','build','--profile','release','-j','1','src/bin/sail.exe','src/sail_lean_backend/sail_plugin_lean.cmxs'],src,env)
 require(subprocess.check_output(['git','-C',src,'diff','--binary','HEAD'])==expected,'build changed tracked source')
 require(not subprocess.check_output(['git','-C',src,'ls-files','--others','--exclude-standard'],text=True).strip(),'untracked source files in build')
 exe=src/'_build/default/src/bin/sail.exe';plugin=src/'_build/default/src/sail_lean_backend/sail_plugin_lean.cmxs'
 receipt={'format':'oak-guarded-source-build-v1','official_base':base,'patch_sha256':sha(HERE/'no-shadow.patch'),
  'toolchain_lock_sha256':sha(HERE/'toolchain-lock.json'),'build_script_sha256':sha(pathlib.Path(__file__)),
  'workdir':str(work),'source_dir':str(src),'source_tree':subprocess.check_output(['git','-C',src,'rev-parse','HEAD^{tree}'],text=True).strip(),
  'executable_sha256':sha(exe),'plugin_sha256':sha(plugin),'prefix_tree_sha256':tree_hash(prefix),
  'ocaml_version':'5.3.0','dune_version':'3.21.1','version':subprocess.check_output([str(exe),'--version'],env=env,text=True).strip()}
 (work/'build-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 exports={k:env[k] for k in ['OCAMLLIB','OCAMLPATH','CAML_LD_LIBRARY_PATH','OCAMLFIND_CONF','LEMLIB','PATH']}
 exports.update(OAK_RETURN_BUILD_RECEIPT=str(work/'build-receipt.json'),OAK_RETURN_SAIL=str(exe),SAIL_DIR=str(src),SAIL_PLUGIN_DIR=str(plugin.parent))
 (work/'env.sh').write_text('\n'.join('export '+k+'='+shlex.quote(v) for k,v in exports.items())+'\n')
 print('Built separate experimental source+patch profile; receipt:',work/'build-receipt.json')
if __name__=='__main__':main()
