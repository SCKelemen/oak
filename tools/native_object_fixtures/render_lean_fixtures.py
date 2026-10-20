#!/usr/bin/env python3
"""Prepare kernel-checkable complete-object fixtures; this does not run Lean."""
import argparse
import json
import pathlib


def literal(data):
    return '['+','.join(map(str,data))+']'


def setle(expr, off, width, value):
    return f'(setLE {expr} {off} {width} {value})'


def negative(out, name, machine, source_name, image, body, comment=''):
    if comment:
        out.append('-- '+comment)
    out.append(f'theorem {name} : accepts {machine} {source_name} {image} {body} = false := by decide +kernel')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('directory',type=pathlib.Path)
    p.add_argument('--output',type=pathlib.Path,default=pathlib.Path('spec/lean/NativeBitwiseObjectFixtures.lean'))
    args=p.parse_args()
    manifest=json.loads((args.directory/'manifest.json').read_text())
    targeted=json.loads((args.directory/'targeted-mutations.json').read_text())['mutations']
    out=['import Oak.NativeBitwiseObject','', '/-!',
         '# Complete production native object fixtures', '',
         'The byte literals below are complete outputs of the unchanged production',
         '`compiler.EmitNativeObject(asm.ELF)` path, from the included original sources.',
         'All admission/refusal facts use kernel reduction of the full ELF objects.',
         'The Go inspection and mutation manifests are diagnostic generators only.',
         'These finite fixtures neither prove whole-compiler correctness nor change',
         'production verification authority. Original-source parsing is not claimed.',
         '-/',
         'set_option autoImplicit false',
         'set_option maxRecDepth 8192',
         'set_option maxHeartbeats 1600000',
         'namespace Oak.NativeBitwiseObjectFixtures',
         'open Oak.NativeBitwiseObject',
         'open Oak.MinimalELF (Bytes)',
         '',
         '/-- Write exactly width low little-endian bytes, using bounded List.set. -/',
         'def setLE (image : Bytes) (offset width value : Nat) : Bytes :=',
         '  (List.range width).foldl (fun bytes i =>',
         '    bytes.set (offset + i) (BitVec.ofNat 8 (value / 256^i % 256))) image',
         '']
    positives=baseline=extra=replays=0
    for f in manifest['fixtures']:
        ident=f['id']; machine='.rv64' if f['target']=='linux/riscv64' else '.arm64'
        body=(f'(RiscVFramedBitwise.functionBytes .{f["operation"]})' if machine=='.rv64' else
              f'(fromUInt8 (AArch64BitwiseFunction.functionBytes .{f["operation"]}))')
        raw=(args.directory/f['object_path']).read_bytes()
        source=(args.directory/f['source_path']).read_bytes()
        out += [f'namespace {ident}',
                f'def source : List UInt8 := {literal(source)}',
                f'def name : List UInt8 := {literal(f["function"].encode())}',
                f'def object : List UInt8 := {literal(raw)}',
                'def nameBytes : Bytes := fromUInt8 name',
                'def image : Bytes := fromUInt8 object',
                f'theorem admitted : accepts {machine} nameBytes image {body} = true := by decide +kernel',
                f'end {ident}', '']
        positives+=1
        if f['operation']!='and' or f['function']!='bitwise':
            continue
        out.append(f'namespace {ident}')
        for mutation in f['mutations']:
            kind=mutation['kind']; off=mutation['offset']; value=mutation.get('value',0)
            if kind=='set_le': expr=setle('image',off,mutation['width'],value)
            elif kind=='xor_byte': expr=f'(image.set {off} ((image.getD {off} 0) ^^^ (BitVec.ofNat 8 {value})))'
            elif kind=='truncate': expr=f'(image.take {off})'
            elif kind=='append_byte': expr=f'(image ++ [{value}])'
            else: raise ValueError(kind)
            negative(out,'reject_'+mutation['name'],machine,'nameBytes',expr,body)
            baseline+=1
        for mutation in targeted:
            if mutation['base_fixture']!=ident:
                continue
            name='targeted_'+mutation['name']
            if 'complete_object_hex' in mutation:
                # Preserve the complete adversarial input as a literal for cases
                # which insert records or replace entire instruction wrappers.
                out.append(f'def {name}Image : Bytes := {literal(bytes.fromhex(mutation["complete_object_hex"]))}')
                expr=name+'Image'
            else:
                expr='image'
                for patch in mutation['patches']:
                    expr=setle(expr,patch['offset'],patch['width'],patch['value'])
                if 'truncate' in mutation: expr=f'({expr}.take {mutation["truncate"]})'
                if 'append_hex' in mutation: expr=f'({expr} ++ {literal(bytes.fromhex(mutation["append_hex"]))})'
            negative(out,'reject_'+name,machine,'nameBytes',expr,body,mutation.get('rationale',''))
            extra+=1
        wrong='.arm64' if machine=='.rv64' else '.rv64'
        negative(out,'reject_wrong_target',wrong,'nameBytes','image',body)
        negative(out,'reject_name_replay',machine,'(fromUInt8 [77,105,120,57])','image',body)
        negative(out,'reject_embedded_nul_requested_name',machine,'(nameBytes ++ [0,120])','image',body)
        other=(f'(RiscVFramedBitwise.functionBytes .or)' if machine=='.rv64' else
              '(fromUInt8 (AArch64BitwiseFunction.functionBytes .or))')
        negative(out,'reject_operation_replay',machine,'nameBytes','image',other)
        replays+=4
        if machine=='.rv64':
            out.append('def leafAnd : Bytes := [51,117,181,0,103,128,0,0]')
            negative(out,'reject_leaf_as_complete_object',machine,'nameBytes','leafAnd',body)
            negative(out,'reject_leaf_as_expected_body',machine,'nameBytes','image','leafAnd')
            replays+=2
        out += [f'end {ident}','']
    out += ['end Oak.NativeBitwiseObjectFixtures','']
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text('\n'.join(out))
    counts=dict(positive_admission=positives,baseline_mutation_refusals=baseline,targeted_mutation_refusals=extra,replay_and_leaf_refusals=replays,total=positives+baseline+extra+replays,compiled=False)
    (args.directory/'lean-fixture-counts.json').write_text(json.dumps(counts,indent=2)+'\n')
    print(json.dumps(counts))
    print(args.output)

if __name__=='__main__':
    main()
