#!/usr/bin/env python3
"""Exercise the hosted shallow-fetch failure and fail-closed diff identity.
Uses only pinned objects in an existing local source checkout, no downloads.
"""
import argparse,json,pathlib,subprocess,tempfile
from build import HERE, source_diff, sha, require

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-cache',type=pathlib.Path,required=True);a=p.parse_args()
 profile=json.loads((HERE/'profile.json').read_text());patch=HERE/'no-shadow.patch'
 require(sha(patch)==profile['patch_sha256'],'regression patch drift')
 expected=patch.read_bytes()
 def git(src,*args):return subprocess.check_output(['git','-C',str(src),*args],stderr=subprocess.STDOUT)
 with tempfile.TemporaryDirectory(prefix='oak-source-diff-') as td:
  src=pathlib.Path(td)/'shallow';src.mkdir();git(src,'init','-q')
  git(src,'fetch','--depth','1',str(a.source_cache.resolve()),profile['official_base'])
  git(src,'checkout','--detach',profile['official_base'])
  require(git(src,'rev-parse','--is-shallow-repository').strip()==b'true','regression must use shallow source')
  git(src,'apply','--check',str(patch));git(src,'apply',str(patch))
  require(source_diff(src)==expected,'canonical shallow source mismatch')
  legacy=git(src,'-c','core.abbrev=7','diff','--binary','HEAD')
  require(legacy!=expected,'did not exercise old abbreviation failure')
  require(legacy.replace(b'index ca362cd..e44c716 ',b'index ca362cd3a..e44c716d9 ')==expected,
          'unexpected shallow regression difference')
  for name,value in [('core.abbrev','12'),('color.ui','always'),('diff.noprefix','true'),('diff.relative','true'),
                     ('diff.mnemonicPrefix','true'),('diff.context','12'),
                     ('diff.interHunkContext','20'),('diff.algorithm','histogram'),
                     ('diff.indentHeuristic','false'),('diff.external','/bin/false')]:
   git(src,'config',name,value)
  require(source_diff(src)==expected,'presentation configuration changed canonical identity')
  path=src/'src/lib/rewrites.ml';original=path.read_bytes()
  path.write_bytes(original+b'\n(* source mutation *)\n')
  require(source_diff(src)!=expected,'accepted content mutation');path.write_bytes(original)
  path.chmod(0o755)
  require(source_diff(src)!=expected,'accepted executable-mode mutation');path.chmod(0o644)
  other=src/'README.md';saved=other.read_bytes();other.write_bytes(saved+b'\nsource mutation\n')
  require(source_diff(src)!=expected,'accepted unrelated tracked mutation');other.write_bytes(saved)
  require(source_diff(src)==expected,'regression restoration failed')
  git(src,'add','src/lib/rewrites.ml')
  require(source_diff(src)==expected,'staging exact patch changed identity')
  path.write_bytes(original+b'\n(* staged source mutation *)\n');git(src,'add','src/lib/rewrites.ml')
  require(source_diff(src)!=expected,'accepted staged mutation')
  path.write_bytes(original);git(src,'add','src/lib/rewrites.ml')
  extra=src/'unexpected-tracked.txt';extra.write_text('unexpected input\n');git(src,'add',extra.name)
  require(source_diff(src)!=expected,'accepted extra tracked file')
 print('PASS: shallow abbreviation/config invariance; content/mode/unrelated tracked mutations rejected.')
if __name__=='__main__':main()
