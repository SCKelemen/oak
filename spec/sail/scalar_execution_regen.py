#!/usr/bin/env python3
"""Extract intact pinned Arm scalar bodies/selected decode clauses and invoke Sail.
Unimplemented callees remain arbitrary explicit Lean boundary parameters.
"""
import argparse, hashlib, pathlib, re, subprocess, tempfile, shutil, os
HERE = pathlib.Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--output-dir', type=pathlib.Path, default=HERE)
OUT = parser.parse_args().output_dir.resolve()
OUT.mkdir(parents=True, exist_ok=True)
MODEL = HERE.parent.parent / 'external/sail-arm/arm-v8.5-a/model'
SAIL = os.environ.get('SAIL', 'sail')
PINS = {'aarch64.sail':'9cdcf786f76223fb4bb0ca1fc52dbef3b62d7b2f3a4e22ab118935e03d4dd6bc', 'aarch_types.sail':'f87f0dda7183442c253cd3e3cd4073999911c858702e099151bf313df428769a', 'aarch_mem.sail':'5764f0a9282825f63edf30b5fd50811ae5c85ab2a3f6104334e00d26cf6d5592', 'prelude.sail':'c372a54eb3a4cb43da6f09d989690048f6778db79783a0a13ae2884538cb03fc', 'aarch_decode.sail':'61a57876f4ac9b10849bf90bcd9bb74f6336737015cb3a5b1e1ebd85f11e6ae7'}
def require(condition, message):
    if not condition:
        raise RuntimeError(message)

sources = {}
for name, digest in PINS.items():
    data = (MODEL/name).read_bytes()
    require(hashlib.sha256(data).hexdigest() == digest, "pinned source mismatch: " + name)
    sources[name] = data.decode()
def decl(file,kind,name):
    source=sources[file]
    starts=list(re.finditer(r'^'+kind+' '+re.escape(name)+r'(?:[ \t\r\n:(=]|$)',source,re.M))
    require(len(starts)==1, (file,kind,name,len(starts)))
    start=starts[0].start();after=starts[0].end()
    end=re.search(r'^(?:val|function|register|type|enum|struct|overload|let|union)\s',source[after:],re.M)
    return source[start:after+end.start() if end else len(source)].strip()+'\n\n'
def both(file,name):return decl(file,'val',name)+decl(file,'function',name)
def cut(file,name):
    d=decl(file,'val',name)
    require('val '+name+' :' in d, 'missing boundary declaration: '+name)
    return d.replace('val '+name+' :','val '+name+' = impure { lean: "boundaries.'+name+'" } :')
version=subprocess.check_output([SAIL,'--version'],text=True).strip()
require(version=='Sail 0.20.2 (sail2 @ 3b7af38d66466ecadad563158b07ce2f82fe05da)', version)
saildir=pathlib.Path(subprocess.check_output([SAIL,'--dir'],text=True).strip())
vector=(saildir/'lib/vector.sail').read_text()
require(hashlib.sha256(vector.encode()).hexdigest()=='73855de7cdfbef3cc5ba22b64478d1ae031ad56fdc80a4dedc8fdfbb4db1218b', 'Sail vector prelude mismatch')
vector=vector.replace('val signed = pure','val oak_signed_compat = pure')
prelude=(HERE/'str_execution_regen.go').read_text().split('const fragmentPrelude = `',1)[1].rsplit('`',1)[0]
prelude=prelude[prelude.index('default Order'):].replace('str_execution_vector.sail','scalar_execution_vector.sail')
prelude += "overload operator ^ = {xor_vec}\n"
license=sources['aarch64.sail'].split('\nval println',1)[0]
fragment=license+'\n\n/* Intact source extraction; explicit impure callee boundaries; selected decoder only. */\n'+prelude
for kind,name in [('enum','LogicalOp'),('enum','ShiftType'),('enum','BranchType'),('struct','ProcState')]:fragment+=decl('aarch_types.sail',kind,name)
fragment+=decl('prelude.sail','union','exception')
for file,name in [('aarch_mem.sail','_R'),('aarch_mem.sail','PSTATE'),('aarch_mem.sail','InGuardedPage'),('aarch64.sail','BTypeNext'),('aarch64.sail','__unconditional'),('aarch_decode.sail','SEE')]:fragment+=decl(file,'register',name)
fragment+=both('aarch_mem.sail','ZeroExtend__0')+'overload ZeroExtend = {ZeroExtend__0}\n\n'
fragment+=both('aarch64.sail','aget_X')+both('aarch64.sail','aset_X')+'overload X = {aget_X, aset_X}\n\n'
fragment+=cut('aarch64.sail','LSL_C')+both('aarch64.sail','LSL')
for file,name in [('aarch_mem.sail','LSR'),('aarch64.sail','ASR'),('aarch64.sail','ROR'),('aarch_mem.sail','HaveBTIExt'),('aarch_mem.sail','UsingAArch32'),('aarch64.sail','BranchTargetCheck'),('aarch_mem.sail','HavePACExt'),('aarch64.sail','aget_SP'),('aarch64.sail','AuthIA'),('aarch64.sail','AuthIB'),('aarch_mem.sail','aget_PC'),('aarch_mem.sail','BranchTo')]:fragment+=cut(file,name)
fragment+='overload SP = {aget_SP}\noverload PC = {aget_PC}\n\n'
for file,name in [('aarch_mem.sail','IsZero'),('aarch64.sail','IsZeroBit'),('aarch64.sail','DecodeShift'),('aarch64.sail','ShiftReg'),('aarch64.sail','__PostDecode'),('aarch64.sail','integer_logical_shiftedreg'),('aarch64.sail','integer_logical_shiftedreg_decode'),('aarch64.sail','branch_unconditional_register'),('aarch64.sail','branch_unconditional_register_decode')]:fragment+=both(file,name)
fragment+=decl('aarch_decode.sail','val','decode64')
clauses=re.findall(r'^function clause decode64 .*?(?=^function clause|\Z)',sources['aarch_decode.sail'],re.M|re.S)
selected=[]
for word in [0x0a010000,0x2a010000,0x4a010000,0xd65f03c0]:
    matches=[]
    for clause in clauses:
        header=clause.split(' = {',1)[0]
        if 'as op_code' not in header:continue
        tokens=re.findall(r'0b([01]+)|_\s*:\s*bits\((\d+)\)',header.split('as op_code')[0])
        n=0;mask=0;value=0
        for bits,width in tokens:
            k=len(bits) if bits else int(width);n+=k;mask=(mask<<k)|((1<<k)-1 if bits else 0);value=(value<<k)|(int(bits,2) if bits else 0)
        if n==32 and word&mask==value:matches.append(clause)
    require(len(matches)==1,(hex(word),len(matches)))
    selected+=matches
fragment+='\n'.join(selected)+'\nfunction clause decode64 _ = throw(Error_Undefined())\n'
(OUT/'scalar_execution.sail').write_text(fragment)
(OUT/'scalar_execution_vector.sail').write_text(vector)
with tempfile.TemporaryDirectory() as td:
    tmp=pathlib.Path(td)
    (tmp/'scalar_execution.sail').write_text(fragment);(tmp/'scalar_execution_vector.sail').write_text(vector)
    subprocess.run([SAIL,'scalar_execution.sail','--lean','--lean-single-file','--lean-output-dir',td,'--lean-lib-path',str(HERE.parent.parent.parent/'external/lean-sail')],cwd=tmp,check=True)
    out=OUT/'lean/ScalarExecution';out.mkdir(parents=True, exist_ok=True)
    for name,src in [('Raw.lean',tmp/'out/Out.lean'),('RawDefs.lean',tmp/'out/Out/Defs.lean')]:shutil.copy(src,out/name)
    print('Generated raw output. Boundary framing and audit still required.')

# Namespace and explicit callback-parameter framing only. No generated bodies
# are replaced with expected arithmetic or successful stubs.
out=OUT/'lean/ScalarExecution'
defs=(out/'RawDefs.lean').read_text()
require(hashlib.sha256(defs.encode()).hexdigest()=='4599759ae12f5aff5af70c4fcc35fb4fff1d56bbfa6ef94c8997426fedaeac01', 'raw definition output needs re-audit')
defs=defs.replace('import Sail\n','import Sail\nnamespace ScalarExecution\n')+'\nend ScalarExecution\n'
(out/'Defs.lean').write_text(defs)
generated=(out/'Raw.lean').read_text()
require(hashlib.sha256(generated.encode()).hexdigest()=='db0b8ed93db97925f152d508f3c2020230c13c09cf5ea29942a4666d3df24f83', 'raw generator output needs re-audit')
generated=generated.replace('import Out.Defs\nimport Out.Specialization\nimport Out.FakeReal\n','import ScalarExecution.Defs\nimport ScalarExecution.Interface\n')
generated=generated.replace('namespace Out.Functions','namespace ScalarExecution.Functions\nopen PreSail').replace('end Out.Functions','end ScalarExecution.Functions')
for name in ['LSL','ShiftReg','__PostDecode','integer_logical_shiftedreg','integer_logical_shiftedreg_decode','branch_unconditional_register','branch_unconditional_register_decode','decode64']:
    generated=re.sub(r'\b'+name+r'\b',name+' boundaries',generated)
    generated=generated.replace('def '+name+' boundaries ','def '+name+' (boundaries : Boundaries) ')
(out/'Generated.lean').write_text(generated)
print('Raw SHA256:',hashlib.sha256((out/'Raw.lean').read_bytes()).hexdigest())
