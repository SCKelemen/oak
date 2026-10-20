#!/usr/bin/env python3
"""Check the small downstream byte binding against the existing core closure."""
import argparse
import json
import os
import pathlib
import re
import subprocess
import check_decoder_classification as gate

HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parent.parent
CORE=ROOT/'spec/lean'

def main():
    p=argparse.ArgumentParser();p.add_argument('--build-dir',type=pathlib.Path,required=True);p.add_argument('--core-source',type=pathlib.Path);args=p.parse_args()
    build=args.build_dir.resolve();core=(args.core_source or CORE).resolve();library=core/'.lake/build/lib/lean'
    closure=[]
    def visit(name):
        if name in closure:return
        rel=pathlib.Path(*name.split('.')).with_suffix('.lean');source=(CORE/rel).read_bytes()
        if (core/rel).read_bytes()!=source:raise RuntimeError('core source/cache mismatch: '+name)
        for dep in re.findall(r'^import (Oak\.[A-Za-z_0-9.]+)',source.decode(),re.M):visit(dep)
        if not (library/rel.with_suffix('.olean')).is_file():raise RuntimeError('missing core olean: '+name)
        closure.append(name)
    visit('Oak.AArch64BitwiseFunction')
    summary=json.loads((build/'validated.json').read_text())
    for name,expected in summary['sources'].items():
        if gate.sha(gate.SOURCES/name)!=expected:raise RuntimeError('classification changed since full gate: '+name)
    for name,receipt in summary['receipts'].items():
        if gate.sha(build/'Oak/ArmDecoderClassification'/(name+'.olean'))!=receipt['olean_sha256']:raise RuntimeError('classification olean drift: '+name)
    # Lean resolves a package root once; both closures use the Oak root.
    # Link only the byte-matched, recursively inventoried core artifacts into
    # this build root, retaining exact source/olean hashes in the receipt.
    for name in closure:
        rel=pathlib.Path(*name.split('.')).with_suffix('.olean')
        target=library/rel;link=build/rel
        link.parent.mkdir(parents=True,exist_ok=True)
        if link.is_symlink():
            if link.resolve()!=target.resolve():raise RuntimeError('core link drift: '+name)
        elif link.exists():raise RuntimeError('unexpected core artifact: '+name)
        else:link.symlink_to(target)
    envpath=str(build)
    source=gate.SOURCES/'ByteBinding.lean';output=build/'Oak/ArmDecoderClassification/ByteBinding.olean'
    gate.run(['lean','-j1','-o',str(output),str(source)],build,'ByteBinding',envpath)
    audit=build/'ByteAudit.lean';names=re.findall(r'^theorem ([A-Za-z_][A-Za-z_0-9.]*)\b',source.read_text(),re.M)
    audit.write_text('import Oak.ArmDecoderClassification.ByteBinding\n'+''.join('#print axioms Oak.ArmDecoderClassification.'+n+'\n' for n in names))
    gate.run(['lean','-j1',str(audit)],build,'ByteAudit',envpath)
    found={}
    for name,raw in re.findall(r"'Oak.ArmDecoderClassification.([^']+)' depends on axioms: \[([^]]*)\]",(build/'ByteAudit.log').read_text()):
        axioms={x.strip() for x in raw.split(',') if x.strip()}
        if name in found or not axioms<=gate.ALLOWED:raise RuntimeError('invalid byte-binding audit: '+name)
        found[name]=axioms
    for name in re.findall(r"'Oak.ArmDecoderClassification.([^']+)' does not depend on any axioms",(build/'ByteAudit.log').read_text()):
        if name in found:raise RuntimeError('duplicate audit: '+name)
        found[name]=set()
    if set(found)!=set(names):raise RuntimeError('missing byte-binding closure')
    (build/'byte-binding.json').write_text(json.dumps({'source_sha256':gate.sha(source),'olean_sha256':gate.sha(output),'core':{name:{'source':gate.sha(CORE/pathlib.Path(*name.split('.')).with_suffix('.lean')),'olean':gate.sha(library/pathlib.Path(*name.split('.')).with_suffix('.olean'))} for name in closure},'closures':names},indent=2)+'\n')
    print(f'Byte binding validated against {len(closure)} byte-matched core modules; no full-decoder execution claim.')

if __name__=='__main__':main()
