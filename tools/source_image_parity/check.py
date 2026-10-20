#!/usr/bin/env python3
"""Focused source-to-complete-image composition and fixed-root audit checks.
Render current production NativeBitwiseImage fixtures; never run their large
mutation matrix here. This is local diagnostic evidence, not a production authority API.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import re
import resource
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / 'spec/lean'
NATIVE = ROOT / 'tools/native_image_fixtures'
sys.path.insert(0, str(NATIVE))
from render_lean_fixtures import literal, expand_literal
spec = importlib.util.spec_from_file_location('native_fixture_check', NATIVE / 'check.py')
native = importlib.util.module_from_spec(spec)
spec.loader.exec_module(native)
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}
PREFIX = 'Oak.BitwiseSourceImageParity.'
PINNED_TOOLCHAIN = 'leanprover/lean4:v4.33.1'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def lean_environment(output):
    try:
        toolchain = (LEAN/'lean-toolchain').read_text().strip()
    except OSError as error:
        raise SystemExit('Cannot read pinned Lean toolchain: '+str(error)) from error
    if toolchain != PINNED_TOOLCHAIN:
        raise SystemExit('Requires pinned Lean toolchain '+PINNED_TOOLCHAIN)
    env = dict(os.environ)
    # Elan cannot discover spec/lean/lean-toolchain from an isolated evidence cwd.
    # Override inherited selection; do not change cwd or rely on a global default.
    env['ELAN_TOOLCHAIN'] = toolchain
    env['LEAN_PATH'] = str(output) + os.pathsep + str(LEAN/'.lake/build/lib/lean')
    return env


def case_inventory():
    return json.loads((ROOT/'tools/source_image_parity/expected-cases.json').read_text())


def require_cases(kind, actual):
    expected=case_inventory()[kind]
    if actual != expected:
        raise SystemExit('Changed, missing, duplicate or reordered '+kind+' case inventory')


def validate_report(report):
    pinned=case_inventory()
    roots=json.loads((ROOT/'tools/source_image_parity/expected-roots.json').read_text())
    if report.get('schema')!='oak.source-image-parity.tests.v1' or report.get('complete') is not True:
        raise SystemExit('Missing completed source-image gate report')
    expected_fields=set(pinned['counts']) | {'schema','complete','cases','seconds','max_child_rss_kib',
        'scope','inputs','model_sha256','audit_sha256'}
    if set(report)!=expected_fields:
        raise SystemExit('Changed gate report fields')
    for field,value in pinned['counts'].items():
        if type(report[field]) is not int or report[field]!=value:
            raise SystemExit('Missing, skipped or extra required checks: '+field)
    for field in ['model_sha256','audit_sha256']:
        if report[field]!=roots[field]:
            raise SystemExit('Gate report belongs to another '+field)
    expected_cases={k:pinned[k] for k in ['pairs','source_refusals','auditor_refusals','late_failures']}
    if report['cases']!=expected_cases:
        raise SystemExit('Gate report has changed case identities')
    native_pins=json.loads((NATIVE/'evidence.json').read_text())
    expected_inputs={arch+'_'+pair[0] for pair in pinned['pairs'] for arch in ['arm64','riscv64']}
    if set(report['inputs'])!=expected_inputs:
        raise SystemExit('Gate report is missing exact complete tuples')
    for ident,data in report['inputs'].items():
        required={'image_length','image_sha256','source_sha256'} | ({'wasm_sha256'} if ident.startswith('arm64_') else set())
        if set(data)!=required or type(data['image_length']) is not int or not 0<data['image_length']<=5120:
            raise SystemExit('Invalid complete input evidence: '+ident)
        for key in required-{'image_length'}:
            if not isinstance(data[key],str) or not re.fullmatch('[0-9a-f]{64}',data[key]):
                raise SystemExit('Invalid input hash: '+ident)
        expected=native_pins[ident]
        if data['image_length']!=expected['length'] or data['image_sha256']!=expected['sha256'] or data['source_sha256']!=expected['source_sha256']:
            raise SystemExit('Input report does not match retained production identity: '+ident)
    for pair in pinned['pairs']:
        if report['inputs']['arm64_'+pair[0]]['source_sha256']!=report['inputs']['riscv64_'+pair[0]]['source_sha256']:
            raise SystemExit('Architecture source snapshots differ')


def require_current_inputs(lines, directory, selected):
    selected=set(selected)
    decoded={}
    current=None
    for line in lines:
        opening=re.match(r'^namespace (\w+)$',line)
        if opening and opening[1] in selected:
            current=opening[1]
            if current in decoded:raise SystemExit('Duplicate fresh native fixture')
            decoded[current]={}
        if current:
            match=re.match(r'^def (source|header|suffix|image) : (?:List UInt8|Bytes) := (.*)$',line)
            if match:decoded[current][match[1]]=match[2]
        if line.startswith('end '):current=None
    if set(decoded)!=selected:raise SystemExit('Missing fresh native fixture')
    for ident,fields in decoded.items():
        if fields.get('image')!='header ++ (List.replicate 3976 0 ++ suffix)':
            raise SystemExit('Changed fresh complete-image representation')
        image=expand_literal(fields['header'])+bytes(3976)+expand_literal(fields['suffix'])
        source=expand_literal(fields['source'])
        if image!=(directory/(ident+'.elf')).read_bytes() or source!=(directory/(ident+'.oak')).read_bytes():
            raise SystemExit('Fresh Lean input is not the actual complete production output: '+ident)


def run(command, directory, log, env=None, failure=None):
    started = time.monotonic()
    with log.open('w') as handle:
        child = subprocess.Popen(command, cwd=directory, env=env, text=True,
                                 stdout=handle, stderr=subprocess.STDOUT, start_new_session=True)
        while True:
            pid, status, usage = os.wait4(child.pid, os.WNOHANG)
            if pid:
                child.returncode = os.waitstatus_to_exitcode(status)
                break
            if time.monotonic()-started > 240:
                os.killpg(child.pid, signal.SIGKILL)
                _, status, usage = os.wait4(child.pid, 0)
                child.returncode = os.waitstatus_to_exitcode(status)
                raise SystemExit('Timed out: '+str(command))
            time.sleep(0.1)
    output = log.read_text()
    metric = dict(log=log.name, command=command, seconds=time.monotonic()-started,
                  max_rss_kib=usage.ru_maxrss, returncode=child.returncode)
    with (log.parent/'process-metrics.jsonl').open('a') as handle:
        handle.write(json.dumps(metric)+'\n')
    print(f'{log.name}: exit {child.returncode}, {metric["seconds"]:.2f}s, {usage.ru_maxrss} KiB', flush=True)
    if failure is None:
        if child.returncode:
            raise SystemExit(output + f'\nFailed: {command}')
    elif not child.returncode or failure not in output:
        raise SystemExit(output + f'\nExpected nonzero exit containing {failure!r}')
    elif failure is not None:
        errors=re.findall(r'^.+: error(?:\([^)]*\))?: (.*)$', output, re.M)
        if len(errors)!=1 or failure not in errors[0]:
            raise SystemExit(output + '\nNegative control had an unrelated or multiple errors')
    return output


REFUSAL_HELPERS = r'''
private theorem other_body {m : Oak.MinimalELF.Machine}
    {name image body other : Oak.MinimalELF.Bytes}
    (h : NativeBitwiseImage.accepts m name image body = true) (neq : body ≠ other) :
    NativeBitwiseImage.accepts m name image other = false := by
  obtain ⟨loaded, extracted, _, _, _, eq, _⟩ := NativeBitwiseImage.accepted_named_load h
  simp only [NativeBitwiseImage.accepts, extracted, eq, decide_eq_false_iff_not]
  exact neq

private theorem other_name {m : Oak.MinimalELF.Machine}
    {name other image body otherBody : Oak.MinimalELF.Bytes}
    (h : NativeBitwiseImage.accepts m name image body = true) (neq : other ≠ name) :
    NativeBitwiseImage.accepts m other image otherBody = false := by
  obtain ⟨_, _, old, _⟩ := NativeBitwiseImage.accepted_named_load h
  cases bad : NativeBitwiseImage.accepts m other image otherBody with
  | false => rfl
  | true =>
    obtain ⟨_, _, current, _⟩ := NativeBitwiseImage.accepted_named_load bad
    have oldName := old.2.2.2.1.2.2.2.2.1
    have newName := current.2.2.2.1.2.2.2.2.1
    have equal := Option.some.inj (newName.symm.trans oldName)
    exact False.elim (neq (List.append_cancel_left equal))
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path, help='Raw pinned native fixture directory')
    parser.add_argument('--output', type=Path, required=True, help='Evidence and generated-proof directory')
    parser.add_argument('--reuse-fixtures', action='store_true', help='Reuse controlled compiled fixture modules with matching source/proof hashes')
    parser.add_argument('--reuse-build', action='store_true', help='Reuse already compiled composition/audit modules')
    args = parser.parse_args()
    out = args.output.resolve(); out.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    library = LEAN / '.lake/build/lib/lean'
    env = lean_environment(out)
    version = run(['lean', '--version'], LEAN, out/'lean-version.log', env)
    if 'version 4.33.1,' not in version:
        raise SystemExit('Requires pinned Lean 4.33.1')
    model = (LEAN/'Oak/BitwiseSourceImageParity.lean').read_text()
    roots = json.loads((ROOT/'tools/source_image_parity/expected-roots.json').read_text())
    if sha(model.encode()) != roots['model_sha256'] or sha((LEAN/'Oak/BitwiseSourceImageParityAudit.lean').read_bytes()) != roots['audit_sha256']:
        raise SystemExit('Changed pinned model/auditor source, including binding and contract definitions')
    statements = {}
    for match in re.finditer(r'^theorem (\w+)\b', model, re.M):
        end = model.index(' := by', match.start())
        statements[PREFIX+match[1]] = model[match.start():end]
    if list(statements) != roots['model'] or statements != roots['statements']:
        raise SystemExit('Changed pinned composition theorem inventory or exact statements')
    if not args.reuse_build:
        for module in ['BitwiseSourceImageParity', 'BitwiseSourceImageParityAudit']:
            target = library/'Oak'/f'{module}.olean'
            run(['lean', '-j1', '-M3000', '--trust=0', '-o', str(target), f'Oak/{module}.lean'],
                LEAN, out/f'{module}-compile.log', env)
    audit = out/'AuditComposition.lean'
    audit.write_text('import Oak.BitwiseSourceImageParity\nset_option format.width 100000\n'+
                     '\n'.join('#print axioms '+name for name in roots['model'])+'\n')
    native.audit_reports(run(['lean','-j1','-M3000','--trust=0',str(audit)], LEAN, out/'model-audit.log', env), roots['model'])
    fresh=out/'FreshCompositionNative.lean'
    run([sys.executable,str(NATIVE/'render_lean_fixtures.py'),str(args.directory.resolve()),
         '--output',str(fresh),'--fresh'],ROOT,out/'fresh-native-render.log')
    lines=fresh.read_text().splitlines()
    fixtures=native.inventory(lines)
    native.require_inventory('fresh',fixtures.values())
    native.require_statements(lines,fixtures,'fresh')
    native.verify_inputs(lines)
    pins = json.loads((NATIVE/'evidence.json').read_text())
    pairs = [('mix_and','And'), ('mix_or','Or'), ('mix_xor','Xor'), ('Mix9_and','Rename')]
    require_cases('pairs',[list(pair) for pair in pairs])
    require_current_inputs(lines,args.directory,{arch+'_'+pair[0] for pair in pairs for arch in ['arm64','riscv64']})
    inputs = {}
    for ident, tag in pairs:
        for arch in ['arm64','riscv64']:
            key = arch+'_'+ident
            source = (args.directory/(key+'.oak')).read_bytes()
            image = (args.directory/(key+'.elf')).read_bytes()
            if sha(source) != pins[key]['source_sha256'] or sha(image) != pins[key]['sha256']:
                raise SystemExit('Changed raw pinned input: '+key)
            inputs[key] = dict(source_sha256=sha(source), image_sha256=sha(image), image_length=len(image))
        if (args.directory/('arm64_'+ident+'.oak')).read_bytes() != (args.directory/('riscv64_'+ident+'.oak')).read_bytes():
            raise SystemExit('Architecture source mismatch: '+ident)
    # Current complete Wasm modules are compiled from these exact original bytes.
    run(['go','run','-p=2','./tools/source_image_parity',str(args.directory.resolve()),str(out)],
        ROOT,out/'wasm-production.log')
    parsed = {}
    records = {}
    native_sources = {}
    for ident, tag in pairs:
        chosen = {i for i,name in fixtures.items() if name in [
            f'Oak.NativeBitwiseImageFixtures.arm64_{ident}.admitted',
            f'Oak.NativeBitwiseImageFixtures.riscv64_{ident}.admitted']}
        if len(chosen) != 2: raise SystemExit('Missing native admitted roots')
        mod = 'SourceImageParityData'+tag
        namespace = 'Oak.'+mod
        source = native.fixture_source(lines, fixtures, chosen).replace('Oak.NativeBitwiseImageFixtures',namespace)
        names = [fixtures[i].replace('Oak.NativeBitwiseImageFixtures',namespace) for i in sorted(chosen)]
        source += '\nset_option format.width 100000\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
        path=out/(mod+'.lean'); path.write_text(source)
        receipt=out/(mod+'-receipt.json')
        key=dict(source_sha256=sha(source.encode()), native_model_sha256=sha((LEAN/'Oak/NativeBitwiseImage.lean').read_bytes()), roots=names)
        compiled=out/(mod+'.olean')
        cached=False
        if args.reuse_fixtures and receipt.exists() and compiled.exists():
            saved=json.loads(receipt.read_text())
            cached=all(saved.get(k)==v for k,v in key.items()) and saved.get('olean_sha256')==sha(compiled.read_bytes())
        if cached:
            native.audit_reports((out/(mod+'.log')).read_text(),names)
            print('Reused checked native fixture pair '+tag,flush=True)
        else:
            result=run(['lean','-j1','-M3000','--trust=0','-o',str(compiled),str(path)],out,out/(mod+'.log'),env)
            native.audit_reports(result,names)
            receipt.write_text(json.dumps(dict(key,olean_sha256=sha(compiled.read_bytes())),indent=2)+'\n')
        native_sources[ident]=source[:source.index('\nset_option format.width 100000\n')]
        raw=(args.directory/('arm64_'+ident+'.oak')).read_bytes()
        wasm=(out/(ident+'.wasm')).read_bytes()
        match=re.fullmatch(rb'(\w+): \((\w+): u32, (\w+): u32\): u32 = \2 ([&|^]) \3\n',raw)
        if not match: raise SystemExit('Unexpected canonical source bytes')
        name,first,second,operator=match.groups()
        op={b'&':'and',b'|':'or',b'^':'xor'}[operator]
        d='⟨'+', '.join([literal(name),literal(first),literal(second),'.'+op])+'⟩'
        p=f'{namespace}.arm64_{ident}'
        q=f'{namespace}.riscv64_{ident}'
        base=f'''import Oak.BitwiseSourceImageParityAudit
import {mod}
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Oak.SourceImageParityRequest
open Oak.BitwiseSourceImageParity
open Oak.NativeBitwiseObject (fromUInt8)
def source : List UInt8 := {p}.source
def wasm : List UInt8 := {literal(wasm)}
def arm : Oak.MinimalELF.Bytes := {p}.image
def rv : Oak.MinimalELF.Bytes := {q}.image
def declaration : Oak.BitwiseSource.Decl := (Oak.BitwiseSource.parse source).getD ⟨[], [], [], .and⟩
private theorem parsed : Oak.BitwiseSource.parse source = some ({d} : Oak.BitwiseSource.Decl) := by decide +kernel
private theorem wasm_good : Oak.BitwiseModule.acceptsModule .wasm .wasmLocals [32,32] 32 .{op} {literal(name)} wasm = true := by decide +kernel
'''
        admitted=f'''theorem admitted : check source wasm arm rv = some declaration := by
  have declared : declaration = ({d} : Oak.BitwiseSource.Decl) := by
    unfold declaration
    rw [parsed]
    rfl
  rw [declared]
  exact check_of_artifacts parsed wasm_good {p}.admitted {q}.admitted
'''
        binding='theorem binding : type_of% (accepted_source_image_binding admitted) := accepted_source_image_binding admitted\n'
        all_inputs='theorem all_inputs : type_of% (accepted_all_input_success admitted) := accepted_all_input_success admitted\n'
        suffix='end Oak.SourceImageParityRequest\n#oak_source_image_parity_audit\n'
        full=base+admitted+binding+all_inputs+suffix
        path=out/(tag+'Positive.lean');path.write_text(full)
        output=run(['lean','-j1','-M3000','--trust=0',str(path)],out,out/(tag+'Positive.log'),env)
        try: record=json.loads(output)
        except ValueError: raise SystemExit('Not one exact JSON audit record')
        expected_fields={'schema','profile','lean_version','source','wasm','arm','rv','declaration','roots'}
        if set(record)!=expected_fields or record['schema']!='oak.source-image-parity.audit.v1' or record['profile']!='bitwise-source-complete-images-local-invocation-v1' or record['lean_version']!='4.33.1':
            raise SystemExit('Wrong audit schema/profile/inventory')
        for field,data in [('source',raw),('wasm',wasm),('arm',(args.directory/('arm64_'+ident+'.elf')).read_bytes()),('rv',(args.directory/('riscv64_'+ident+'.elf')).read_bytes())]:
            if record[field]!=list(data):raise SystemExit('Wrong exact byte echo: '+field)
        expected_decl=dict(name=list(name),first=list(first),second=list(second),op=op)
        if record['declaration']!=expected_decl:raise SystemExit('Wrong declaration echo')
        if [r['name'] for r in record['roots']]!=['Oak.SourceImageParityRequest.'+n for n in ['admitted','binding','all_inputs']]:raise SystemExit('Wrong root inventory')
        if any(set(r['axioms'])-ALLOWED for r in record['roots']):raise SystemExit('Forbidden audited axiom')
        records[ident]=record
        inputs['arm64_'+ident]['wasm_sha256']=sha(wasm)
        parsed[ident]=(base,admitted,binding,all_inputs,suffix,d,p,q,op,name)
    # Orthogonal mismatches: all unaffected artifacts remain valid, and each
    # negative proof is audited. Reuse prior native admission proofs instead of
    # recomputing the full ELF recognizer for each source-level control.
    base,_,_,_,_,d,p,q,op,name=parsed['mix_and']
    source_or=(args.directory/'arm64_mix_or.oak').read_bytes()
    source_rename=(args.directory/'arm64_Mix9_and.oak').read_bytes()
    wasm_or=(out/'mix_or.wasm').read_bytes()
    wasm_rename=(out/'Mix9_and.wasm').read_bytes()
    _,_,_,_,_,d_or,p_or,q_or,_,_=parsed['mix_or']
    _,_,_,_,_,d_rename,p_rename,q_rename,_,name_rename=parsed['Mix9_and']
    cases=[]
    def refusal(label,source,wasm,arm,rv,decl,proof):
        cases.append(f'theorem {label} : check {source} {wasm} {arm} {rv} = none := by\n'
                     f'  apply refuses_failed_artifact (d := ({decl} : Oak.BitwiseSource.Decl)) (by decide +kernel)\n'
                     f'  exact {proof}\n')
    refusal('refuses_wrong_source_operation',literal(source_or),'wasm','arm','rv',d_or,'Or.inl (by decide +kernel)')
    refusal('refuses_wrong_source_name',literal(source_rename),'wasm','arm','rv',d_rename,'Or.inl (by decide +kernel)')
    refusal('refuses_wrong_wasm_operation','source',literal(wasm_or),'arm','rv',d,'Or.inl (by decide +kernel)')
    refusal('refuses_wrong_wasm_name','source',literal(wasm_rename),'arm','rv',d,'Or.inl (by decide +kernel)')
    refusal('refuses_extra_wasm_bytes','source','(wasm ++ [0])','arm','rv',d,'Or.inl (by decide +kernel)')
    refusal('refuses_wrong_arm_operation','source','wasm',p_or+'.image','rv',d,
            f'Or.inr (Or.inl (other_body {p_or}.admitted (by decide +kernel)))')
    refusal('refuses_wrong_rv_operation','source','wasm','arm',q_or+'.image',d,
            f'Or.inr (Or.inr (other_body {q_or}.admitted (by decide +kernel)))')
    refusal('refuses_wrong_arm_name',literal(source_rename),literal(wasm_rename),'arm',q_rename+'.image',d_rename,
            f'Or.inr (Or.inl (other_name {p}.admitted (by decide +kernel)))')
    refusal('refuses_wrong_rv_name',literal(source_rename),literal(wasm_rename),p_rename+'.image','rv',d_rename,
            f'Or.inr (Or.inr (other_name {q}.admitted (by decide +kernel)))')
    refusal('refuses_body_only_arm','source','wasm','(fromUInt8 (Oak.AArch64BitwiseFunction.functionBytes .and))','rv',d,
            'Or.inr (Or.inl (by decide +kernel))')
    refusal('refuses_body_only_rv','source','wasm','arm','(Oak.RiscVFramedBitwise.functionBytes .and)',d,
            'Or.inr (Or.inr (by decide +kernel))')
    raw=(args.directory/'arm64_mix_and.oak').read_bytes()
    for label,unsupported in [
        ('refuses_unsupported_type',raw.replace(b'u32',b'u64',1)),
        ('refuses_extra_declaration',raw+raw),
        ('refuses_extra_source_byte',raw+b'\n')]:
        cases.append(f'theorem {label} : check {literal(unsupported)} wasm arm rv = none :=\n'
                     f'  (refuses_unsupported (by decide +kernel)).1\n')
    refusals=base.replace('import SourceImageParityDataAnd','import SourceImageParityDataAnd\nimport SourceImageParityDataOr\nimport SourceImageParityDataRename')+REFUSAL_HELPERS+'\n'+''.join(cases)+'\nend Oak.SourceImageParityRequest\nset_option format.width 100000\n'
    refusal_names=['Oak.SourceImageParityRequest.'+re.search(r'theorem (\w+)',c)[1] for c in cases]
    require_cases('source_refusals',refusal_names)
    actual_statements={n:c.split(' :=',1)[0] for n,c in zip(refusal_names,cases)}
    if actual_statements!=case_inventory()['source_statements']:
        raise SystemExit('Changed exact source-refusal theorem statements')
    refusals+='\n'.join('#print axioms '+n for n in refusal_names)+'\n'
    path=out/'SourceRefusals.lean';path.write_text(refusals)
    result=run(['lean','-j1','-M3000','--trust=0',str(path)],out,out/'SourceRefusals.log',env)
    native.audit_reports(result,refusal_names)
    # Measure one full paired-image proof plus fixed auditor in a single
    # process, with complete native inputs/proofs present in that request file.
    base,admitted,binding,all_inputs,suffix,*_=parsed['mix_and']
    combined=native_sources['mix_and'].replace('import Oak.NativeBitwiseImage','import Oak.BitwiseSourceImageParityAudit')+'\n'+'\n'.join(line for line in (base+admitted+binding+all_inputs+suffix).splitlines() if not line.startswith('import '))+'\n'
    path=out/'CompletePairAndAudit.lean';path.write_text(combined)
    output=run(['lean','-j1','-M3000','--trust=0',str(path)],out,out/'CompletePairAndAudit.log',env)
    if json.loads(output)!=records['mix_and']:
        raise SystemExit('Single-process complete pair proof/audit changed exact record')
    # Independently reject valid weaker types, wrong roots/declarations,
    # imported roots, and disallowed proof mechanisms.
    controls={
        'WrongBinding':(base+admitted+'theorem binding : True := True.intro\n'+all_inputs+suffix,'has the wrong exact type or value'),
        'WrongAllInputs':(base+admitted+binding+'theorem all_inputs : True := True.intro\n'+suffix,'has the wrong exact type or value'),
        'FalseAntecedent':(base+admitted+binding+'theorem all_inputs : False → type_of% (accepted_all_input_success admitted) := by intro bad; cases bad\n'+suffix,'has the wrong exact type or value'),
        'WrongRootKind':(base+admitted+binding+all_inputs.replace('theorem all_inputs','def all_inputs')+suffix,'missing theorem root'),
        'WrongDeclaration':(base.replace('(Oak.BitwiseSource.parse source).getD ⟨[], [], [], .and⟩','⟨[], [], [], .or⟩')+'theorem admitted : True := True.intro\ntheorem binding : True := True.intro\ntheorem all_inputs : True := True.intro\n'+suffix,'has the wrong exact type or value'),
        'ForbiddenAxiom':(base+admitted+binding+'axiom forbidden : type_of% (accepted_all_input_success admitted)\ntheorem all_inputs : type_of% (accepted_all_input_success admitted) := forbidden\n'+suffix,'depends on forbidden axiom'),
        'NativeEvaluator':(base+'theorem admitted : check source wasm arm rv = some declaration := by native_decide\n'+binding+all_inputs+suffix,'depends on forbidden axiom'),
        'SkipKernelChecking':(base.replace('namespace Oak.SourceImageParityRequest','set_option debug.skipKernelTC true\nnamespace Oak.SourceImageParityRequest')+admitted+binding+all_inputs+suffix,'kernel checking is disabled')}
    # Regression for the previously observed current-helper validation gap.
    # This invalid proof body is test-only and must be refused by the auditor.
    invalid_helper = '''open Lean Elab Command
elab "invalidDependencyForRegression" : command => do
  liftCoreM <| Lean.addDecl (.thmDecl {
    name := `Oak.TransientUnchecked.falseHelper
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro })
set_option debug.skipKernelTC true in
invalidDependencyForRegression
'''
    controls['InvalidDependencyBody']=(
        base.replace('namespace Oak.SourceImageParityRequest',invalid_helper+'namespace Oak.SourceImageParityRequest')+
        'theorem admitted : check source wasm arm rv = some declaration := False.elim Oak.TransientUnchecked.falseHelper\n'+
        binding+all_inputs+suffix,'has the wrong exact type or value')
    original=roots['statements'][PREFIX+'accepted_all_input_success']
    for label,clause,conclusion in [
        ('DropArmContract','          ArmContract arm armLoaded d.op armState left right ∧\n','rvContract'),
        ('DropRvContract',' ∧\n          RvContract rv rvLoaded d.op left right caller memory mappedRW','armContract')]:
        weak=original.replace('theorem accepted_all_input_success','theorem weaker_contract').replace(clause,'')
        weak+=''' := by
  obtain ⟨al, rl, ab, rb, success⟩ := accepted_all_input_success h
  refine ⟨al, rl, ab, rb, ?_⟩
  intro left right fuel armState armLeft armRight caller memory mappedRW safe
  obtain ⟨hs, ht, hw, ha, hr, armContract, rvContract⟩ :=
    success left right fuel armState armLeft armRight caller memory mappedRW safe
  exact ⟨hs, ht, hw, ha, hr, '''+conclusion+'''⟩
'''
        source=base+admitted+binding+'open Oak.BitwiseFunction (eval)\nopen Oak.BitwiseSource (Bytes Decl Means)\n'+weak+'theorem all_inputs : type_of% (weaker_contract admitted) := weaker_contract admitted\n'+suffix
        controls[label]=(source,'has the wrong exact type or value')
    imported=out/'ImportedAllInputs.lean'
    imported.write_text('import Oak.BitwiseSourceImageParityAudit\nnamespace Oak.SourceImageParityRequest\ntheorem all_inputs : True := True.intro\nend Oak.SourceImageParityRequest\n')
    run(['lean','-j1','-M3000','--trust=0','-o',str(out/'ImportedAllInputs.olean'),str(imported)],out,out/'ImportedAllInputsCompile.log',env)
    controls['ImportedRoot']=('import ImportedAllInputs\n'+base+admitted+binding+suffix,'must be a current-request theorem')
    require_cases('auditor_refusals',list(controls)+['NonzeroTrust'])
    for name,(source,error) in controls.items():
        error=case_inventory()['errors'][name]
        path=out/(name+'.lean');path.write_text(source)
        run(['lean','-j1','-M3000','--trust=0',str(path)],out,out/(name+'.log'),env,failure=error)
    path=out/'NonzeroTrust.lean';path.write_text(base+admitted+binding+all_inputs+suffix)
    run(['lean','-j1','-M3000','--trust=1',str(path)],out,out/'NonzeroTrust.log',env,failure=case_inventory()['errors']['NonzeroTrust'])
    path=out/'LateFailure.lean';path.write_text(base+admitted+binding+all_inputs+suffix+'#check nonexistent_after_success\n')
    output=run(['lean','-j1','-M3000','--trust=0',str(path)],out,out/'LateFailure.log',env,failure=case_inventory()['errors']['LateFailure'])
    emitted=[]
    for line in output.splitlines():
        try: value=json.loads(line)
        except ValueError: continue
        emitted.append(value)
    if emitted != [records['mix_and']]:
        raise SystemExit('Late-failure control did not first emit the exact successful input record')
    require_cases('late_failures',['LateFailure'])
    report=dict(schema='oak.source-image-parity.tests.v1',complete=True,
                cases={k:case_inventory()[k] for k in ['pairs','source_refusals','auditor_refusals','late_failures']},
                complete_tuples=len(pairs),native_admissions_reused=8,model_roots=len(roots['model']),
                audited_tuple_roots=3*len(pairs),source_artifact_refusals=len(cases),auditor_refusals=len(controls)+1,late_process_failures=1,
                seconds=time.monotonic()-started,max_child_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                scope='local named-function invocation; no runtime authority, Linux startup, or hardware claim',
                model_sha256=roots['model_sha256'],audit_sha256=roots['audit_sha256'],inputs=inputs)
    validate_report(report)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,sort_keys=True))


if __name__=='__main__': main()
