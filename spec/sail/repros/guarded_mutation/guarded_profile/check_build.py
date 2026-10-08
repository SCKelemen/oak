#!/usr/bin/env python3
"""Reject provenance-record mutations before CI uses its freshly built tool."""
import json,os,pathlib,tempfile
from verify_build import verified_generator

receipt=pathlib.Path(os.environ['OAK_RETURN_BUILD_RECEIPT']).resolve()
data=json.loads(receipt.read_text());verified_generator()
with tempfile.NamedTemporaryFile(prefix='receipt-mutant-',suffix='.json',dir=receipt.parent,delete=False) as handle:
 mutant=pathlib.Path(handle.name)
try:
 for field in ['official_base','patch_sha256','toolchain_lock_sha256','build_script_sha256','source_tree','executable_sha256','plugin_sha256']:
  changed=dict(data);changed[field]='invalid-mutant';mutant.write_text(json.dumps(changed))
  os.environ['OAK_RETURN_BUILD_RECEIPT']=str(mutant)
  try:verified_generator()
  except RuntimeError:print('Rejected record mutation:',field)
  else:raise RuntimeError('accepted record mutation: '+field)
finally:
 os.environ['OAK_RETURN_BUILD_RECEIPT']=str(receipt);mutant.unlink()
with tempfile.NamedTemporaryFile(prefix='oak-unexpected-source-',suffix='.txt',dir=data['source_dir'],delete=False) as handle:
 probe=pathlib.Path(handle.name)
try:
 try:verified_generator()
 except RuntimeError as error:
  if 'untracked source' not in str(error):raise
  print('Rejected an unexpected source input')
 else:raise RuntimeError('accepted unexpected source input')
finally:probe.unlink()
verified_generator()
print('PASS: source-build receipt and source-input mutations rejected.')
