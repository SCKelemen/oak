#!/usr/bin/env python3
"""Check or regenerate the separate experimental guarded return profile.
No generated body is replaced with an intended operation. The original scalar
raw export remains an independently pinned dependency, framed over larger state.
"""
import argparse, hashlib, json, os, pathlib, re, subprocess, sys, tempfile
HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
LEAN = HERE / 'lean'
PROFILE = HERE / 'repros/guarded_mutation/guarded_profile'
PINS = {'aarch64.sail':'9cdcf786f76223fb4bb0ca1fc52dbef3b62d7b2f3a4e22ab118935e03d4dd6bc', 'aarch_types.sail':'f87f0dda7183442c253cd3e3cd4073999911c858702e099151bf313df428769a', 'aarch_mem.sail':'5764f0a9282825f63edf30b5fd50811ae5c85ab2a3f6104334e00d26cf6d5592', 'prelude.sail':'c372a54eb3a4cb43da6f09d989690048f6778db79783a0a13ae2884538cb03fc', 'aarch_decode.sail':'61a57876f4ac9b10849bf90bcd9bb74f6336737015cb3a5b1e1ebd85f11e6ae7'}
def require(ok, message):
    if not ok: raise RuntimeError(message)
def sha(data): return hashlib.sha256(data).hexdigest()
def checked(path, digest):
    data = path.read_bytes(); require(sha(data) == digest, 'pin mismatch: ' + str(path)); return data

def source_fragment():
    model = ROOT / 'external/sail-arm/arm-v8.5-a/model'
    raw = {name: checked(model/name, digest).decode() for name,digest in PINS.items()}
    def decl(file, kind, name):
        matches = list(re.finditer(r'^'+kind+' '+re.escape(name)+r'(?=[\s:(=])', raw[file], re.M))
        require(len(matches)==1, 'nonunique declaration: '+name)
        tail = raw[file][matches[0].start():]
        end = re.search(r'\n(?:val|function|register|type|enum|struct|overload|let|union) ', tail[1:])
        require(end is not None, 'unterminated declaration: '+name)
        return tail[:end.start()+1].strip()+'\n\n'
    def both(file,name): return decl(file,'val',name)+decl(file,'function',name)
    def cut(file,name):
        d=decl(file,'val',name); require('val '+name+' :' in d,'unexpected signature: '+name)
        return d.replace('val '+name+' :','val '+name+' = impure { lean: "boundaries.'+name+'" } :')
    prelude=(HERE/'str_execution_regen.go').read_text().split('const fragmentPrelude = `',1)[1].rsplit('`',1)[0]
    prelude=prelude[prelude.index('default Order'):].replace('str_execution_vector.sail','return_vector.sail')
    source=raw['aarch_mem.sail'].split('\nval ',1)[0]+'\n'+prelude
    for name in ['LogicalOp','ShiftType','BranchType','ArchVersion']: source+=decl('aarch_types.sail','enum',name)
    source+=decl('aarch_types.sail','struct','ProcState')+decl('prelude.sail','union','exception')
    for name in ['_PC','__PC_changed','PSTATE','TCR_EL1','TCR_EL2','TCR_EL3']: source+=decl('aarch_mem.sail','register',name)
    for file,name in [('aarch_mem.sail','_R'),('aarch_mem.sail','InGuardedPage'),('aarch64.sail','BTypeNext'),('aarch64.sail','__unconditional'),('aarch_decode.sail','SEE')]: source+=decl(file,'register',name)
    for name in ['CFG_ID_AA64PFR0_EL1_EL2','CFG_ID_AA64PFR0_EL1_EL3','__v81_implemented','__v82_implemented','__v83_implemented','__v84_implemented','__v85_implemented']: source+=decl('aarch_mem.sail','register configuration',name)
    for name in ['EL0','EL1','EL2','EL3']: source+=decl('aarch_mem.sail','let',name)
    for name in ['ZeroExtend__0','ZeroExtend__1']: source+=both('aarch_mem.sail',name)
    source+='overload ZeroExtend = {ZeroExtend__0, ZeroExtend__1}\n'
    for name in ['UsingAArch32','IsInHost','SignExtend__1','ELUsingAArch32','HaveVirtHostExt','ELIsInHost','get_SCR']: source+=cut('aarch_mem.sail',name)
    source+='overload SignExtend = {SignExtend__1}\n'
    queries={}
    for name in ['HaveEL','S1TranslationRegime__0','HasArchVersion','HavePACExt']:
        signature=decl('aarch_mem.sail','val',name);body=decl('aarch_mem.sail','function',name)
        source+=signature+body
        queries[name]={'signature_sha256':sha(signature.encode()),'unchanged_body_sha256':sha(body.encode())}
    source+='overload S1TranslationRegime = {S1TranslationRegime__0}\n'
    signature=decl('aarch_mem.sail','val','AddrTop')
    require(signature.count('-> int effect')==1,'AddrTop signature drift')
    strengthened=signature.replace('-> int effect',"-> {'top, 'top in {31, 55, 63}. int('top)} effect")
    body=decl('aarch_mem.sail','function','AddrTop')
    source+=strengthened+body
    for name in ['Hint_Branch','AArch64_BranchAddr','BranchTo']: source+=both('aarch_mem.sail',name)
    provenance={'original_signature':signature,'strengthened_signature':strengthened,'original_signature_sha256':sha(signature.encode()),'strengthened_signature_sha256':sha(strengthened.encode()),'unchanged_body_sha256':sha(body.encode())}
    return source.encode(), provenance, queries

def frame(raw, namespace, interface, functions, boundary_type):
    text=raw.decode().replace('import Out.Defs\nimport Out.Specialization\nimport Out.FakeReal\n', 'import ReturnExecution.Defs\nimport ReturnExecution.'+interface+'\n')
    text=text.replace('namespace Out.Functions','namespace '+namespace+'\nopen PreSail').replace('end Out.Functions','end '+namespace)
    for name in functions:
        text=re.sub(r'\b'+name+r'\b',name+' boundaries',text)
        text=text.replace('def '+name+' boundaries ', 'def '+name+' (boundaries : '+boundary_type+') ')
    return text.encode()

def framed_outputs(raw, defs, scalar):
    out={}
    out['lean/ReturnExecution/Defs.lean']=(defs.decode().replace('import Sail\n','import Sail\nnamespace ReturnExecution\n')+'\nend ReturnExecution\n').encode()
    out['lean/ReturnExecution/Generated.lean']=frame(raw,'ReturnExecution.Functions','Interface',['S1TranslationRegime__0','AddrTop','AArch64_BranchAddr','BranchTo'],'Boundaries')
    out['lean/ReturnExecution/ScalarGenerated.lean']=frame(scalar,'ReturnExecution.ScalarFunctions','ScalarInterface',['LSL','ShiftReg','__PostDecode','integer_logical_shiftedreg','integer_logical_shiftedreg_decode','branch_unconditional_register','branch_unconditional_register_decode','decode64'],'ScalarBoundaries')
    out['lean/ReturnExecution/ScalarInterface.lean']=(LEAN/'ScalarExecution/Interface.lean').read_text().replace('ScalarExecution','ReturnExecution').replace('Boundaries','ScalarBoundaries').encode()
    text=(LEAN/'ScalarExecutionBridge.lean').read_text().replace('import ScalarExecution\n','import ReturnScalar\n').replace('namespace Oak.SailBridge.Scalar','namespace Oak.SailBridge.ExtendedScalar').replace('end Oak.SailBridge.Scalar','end Oak.SailBridge.ExtendedScalar').replace('ScalarExecution.Functions','ReturnExecution.ScalarFunctions').replace('ScalarExecution','ReturnExecution').replace('Boundaries','ScalarBoundaries')
    out['lean/ReturnScalarBridge.lean']=text.encode()
    return out

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--check-source',action='store_true')
    parser.add_argument('--regenerate',action='store_true')
    args=parser.parse_args()
    manifest=json.loads((HERE/'return_execution_manifest.json').read_text())
    for relative,digest in manifest['files'].items(): checked(HERE/relative,digest)
    raw=(LEAN/'ReturnExecution/Raw.lean').read_bytes();defs=(LEAN/'ReturnExecution/RawDefs.lean').read_bytes()
    scalar=(LEAN/'ScalarExecution/Raw.lean').read_bytes()
    if args.check_source or args.regenerate:
        source,provenance,queries=source_fragment()
        require(source==(HERE/'return_execution.sail').read_bytes(),'source extraction drift')
        require(provenance==manifest['AddrTop_adapter'],'signature/body provenance drift')
        require(queries==manifest['query_bodies'],'query declaration provenance drift')
    if args.regenerate:
        profile=json.loads((PROFILE/'profile.json').read_text())
        sys.path.insert(0,str(PROFILE))
        from verify_build import verified_generator
        compiler=verified_generator()
        with tempfile.TemporaryDirectory() as td:
            temp=pathlib.Path(td);(temp/'return.sail').write_bytes(source)
            (temp/'return_vector.sail').write_bytes((HERE/'return_execution_vector.sail').read_bytes())
            subprocess.run([str(compiler),'return.sail','--lean','--lean-single-file','--lean-output-dir',td,'--lean-lib-path',str(ROOT.parent/'external/lean-sail')],cwd=temp,check=True)
            require((temp/'out/Out.lean').read_bytes()==raw,'guarded raw export drift')
            require((temp/'out/Out/Defs.lean').read_bytes()==defs,'guarded raw definitions drift')
            # Same input filename/line layout, original signature, identical body.
            # The standalone AddrTop export typechecks without the later consumer.
            original=temp/'original';original.mkdir()
            original_source=source.decode().replace(provenance['strengthened_signature'],provenance['original_signature'])
            original_source=original_source[:original_source.index('val AArch64_BranchAddr')]
            (original/'return.sail').write_text(original_source)
            (original/'return_vector.sail').write_bytes((HERE/'return_execution_vector.sail').read_bytes())
            subprocess.run([str(compiler),'return.sail','--lean','--lean-single-file','--lean-output-dir',str(original),'--lean-lib-path',str(ROOT.parent/'external/lean-sail')],cwd=original,check=True)
            def addr_body(data):
                match=re.search(r'^def AddrTop .*?(?=^def |^/--|^end )',data.decode(),re.M|re.S)
                require(match is not None,'missing generated AddrTop body');return match.group(0)
            require(addr_body((original/'out/Out.lean').read_bytes())==addr_body(raw),
                    'signature adapter changed generated AddrTop body')

    for relative,data in framed_outputs(raw,defs,scalar).items():
        require((HERE/relative).read_bytes()==data,'framing/proof replay drift: '+relative)
    print('Guarded return pins, source adapter (when requested), and exact body framing checked.')
if __name__=='__main__': main()
