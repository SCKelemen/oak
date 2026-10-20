#!/usr/bin/env python3
"""Enumerate complete-object negative cases; no acceptance/proof authority.

Uses only the bytes and metadata emitted by the neighboring Go generator.
Writes targeted-mutations.json and, with --materialize, complete mutated objects.
"""
import argparse
import hashlib
import json
import pathlib
import struct


def put(image, off, width, value):
    image[off:off+width] = value.to_bytes(width, 'little')


def targeted(f, raw):
    sh = f['section_header_offset']
    sy = next(s['Offset'] for s in f['sections'] if s['Name'] == '.symtab')
    st = next(s['Offset'] for s in f['sections'] if s['Name'] == '.strtab')
    n = f['text_size']
    fn = sy+3*24
    rows = []

    def add(name, family, patches=(), truncate=None, append=b'', custom=None, rationale=''):
        image = bytearray(raw) if custom is None else bytearray(custom)
        for off, width, value in patches:
            put(image, off, width, value)
        if truncate is not None:
            image = image[:truncate]
        image += append
        assert bytes(image) != raw, name
        row = dict(name=name, family=family, object_length=len(image),
                   object_sha256=hashlib.sha256(image).hexdigest(),
                   patches=[dict(offset=o, width=w, value=v) for o,w,v in patches],
                   rationale=rationale)
        if truncate is not None:
            row['truncate'] = truncate
        if append:
            row['append_hex'] = append.hex()
        if custom is not None:
            row['complete_object_hex'] = image.hex()
        rows.append((row, image))

    add('e_shoff_inside_header','header',[(40,8,40)])
    add('e_shoff_overflow','header',[(40,8,2**64-1)])
    add('text_offset_inside_header','sections',[(sh+64+24,8,40)])
    add('text_offset_overflow','sections',[(sh+64+24,8,2**64-1)])
    add('truncate_function_symbol','truncation',truncate=sy+95)
    add('truncate_final_section','truncation',truncate=sh+7*64-1)
    add('function_name_alias_suffix','name',[(fn,4,2)])
    add('function_undefined','symbols',[(fn+6,2,0)])
    add('function_in_rodata','symbols',[(fn+6,2,2)])
    add('function_local_info2','symbols',[(fn+4,1,2)])
    add('function_global_object_info17','symbols',[(fn+4,1,17)])
    add('function_suffix_value4','symbols',[(fn+8,8,4),(fn+16,8,n-4)],
        rationale='The symbol no longer covers the whole text section.')
    add('function_short_good_prefix','symbols',[(fn+16,8,n-4)])
    add('function_extent_into_padding_or_symbols','symbols',[(fn+16,8,n+4)])
    add('text_missing_exec','sections',[(sh+64+8,8,2)])
    add('symtab_wrong_string_link','sections',[(sh+4*64+40,4,6)])
    add('append_zero','append',append=b'\0')
    add('append_extra_symbol_record','append',append=raw[fn:fn+24])
    for r in f['bit_flip_regions']:
        if r['family']=='padding':
            add(f"nonzero_padding_{r['offset']}",'padding',[(r['offset'],1,1)])
    if f['target']=='linux/riscv64':
        add('rv_flags4_to_rvc5','header',[(48,4,5)])
        add('rv_flags4_to_soft0','header',[(48,4,0)])
        # A whole-object wrapper replacement, preserving complete container extent.
        leaf = bytes.fromhex('3375b50067800000')
        image = bytearray(raw)
        image[64:100] = leaf + bytes(28)
        add('rv_leaf_instead_of_framed_wrapper','body',custom=image)
    else:
        add('arm_wrong_flags4','header',[(48,4,4)])

    # Add a fifth, duplicate GLOBAL/FUNC symbol and consistently move all later
    # payloads/table offsets: this is not merely an append-to-file malformed case.
    extra = bytearray(raw[:st] + raw[fn:fn+24] + raw[st:])
    newsh = sh+24
    put(extra,40,8,newsh)
    put(extra,newsh+4*64+32,8,120)
    for section in (5,6):
        old = int.from_bytes(raw[sh+section*64+24:sh+section*64+32],'little')
        put(extra,newsh+section*64+24,8,old+24)
    add('extra_duplicate_function_symbol','symbols',custom=extra,
        rationale='Complete ELF with five symbols; later payload/table offsets shifted consistently.')

    # Add a relocation targeting offset zero of the only text section and move
    # the symbol/string tables consistently. ARM CALL26=283; RV CALL_PLT=19.
    reltype = 19 if f['target']=='linux/riscv64' else 283
    reloc = struct.pack('<QQq',0,(3<<32)|reltype,0)
    extra = bytearray(raw[:sy] + reloc + raw[sy:])
    put(extra,40,8,newsh)
    put(extra,newsh+3*64+32,8,24)
    for section in (4,5,6):
        old = int.from_bytes(raw[sh+section*64+24:sh+section*64+32],'little')
        put(extra,newsh+section*64+24,8,old+24)
    add('extra_relocation_touching_body','sections',custom=extra,
        rationale='Complete ELF with one relocation into .text; later payload/table offsets shifted consistently.')
    return rows


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('directory',type=pathlib.Path)
    p.add_argument('--materialize',action='store_true')
    args = p.parse_args()
    manifest = json.loads((args.directory/'manifest.json').read_text())
    output=[]
    for f in manifest['fixtures']:
        raw=(args.directory/f['object_path']).read_bytes()
        assert hashlib.sha256(raw).hexdigest()==f['object_sha256']
        rows=targeted(f,raw)
        if f['operation']=='and':
            other_id=f['id'][:-3]+'or'
            other=(args.directory/(other_id+'.o')).read_bytes()
            image=bytearray(raw)
            off,size=f['text_offset'],f['text_size']
            image[off:off+size]=other[off:off+size]
            rows.append((dict(name='and_object_with_or_opcode',family='body',
                             object_length=len(image),object_sha256=hashlib.sha256(image).hexdigest(),
                             complete_object_hex=image.hex(),
                             rationale='Retain AND expected operation and source; body is actual corresponding OR emission.'),image))
        for row,image in rows:
            row['base_fixture']=f['id']
            if args.materialize:
                rel=pathlib.Path('targeted-mutants')/f['id']/(row['name']+'.o')
                (args.directory/rel).parent.mkdir(parents=True,exist_ok=True)
                (args.directory/rel).write_bytes(image)
                row['object_path']=str(rel)
            output.append(row)
    result=dict(schema_version=1,scope='Diagnostic negative cases only. All must be checked with original expected operation, source name, target, and ABI.',mutations=output)
    (args.directory/'targeted-mutations.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'Enumerated {len(output)} targeted mutations from {len(manifest["fixtures"])} actual complete objects.')

if __name__=='__main__':
    main()
