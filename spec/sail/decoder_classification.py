#!/usr/bin/env python3
"""Trusted extraction/check orchestration for the explicitly bounded classifier.
The Lean checker binds certificates to complete embedded clause byte chunks;
this Python source inventory/file reconstruction is NOT a verified Sail parser.
"""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
DATA = ROOT / 'spec/lean/Oak/ArmDecoderClassification'
SOURCE = HERE / 'decoder_classification_source.sail'
PIN = '61a57876f4ac9b10849bf90bcd9bb74f6336737015cb3a5b1e1ebd85f11e6ae7'
WORDS = [('and', 0x0a010000), ('orr', 0x2a010000), ('eor', 0x4a010000), ('ret', 0xd65f03c0)]
BATCH = 8
PREFIX_PIN = '347634d8028c08ecf2fb7b861c752ee0bb1c15e5eee54e011ac2302bcc00d39f'

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def quoted(s):
    return json.dumps(s, ensure_ascii=True)

def parse_clause(raw):
    lines = raw.splitlines()
    h = re.fullmatch(r'function clause decode64 \(\((.+) as op_code\) if SEE < (\d+)\) = \{', lines[0])
    require(h is not None, 'unknown complete header')
    index = int(h[2])
    require(lines[1] == f'    SEE = {index};', 'SEE write/guard mismatch')
    segments = []
    chunks = ['function clause decode64 ((']
    mask = value = width = 0
    for j, token in enumerate(h[1].split(' @ ')):
        if j:
            chunks += [' @ ']
        fixed = re.fullmatch(r'0b([01]+)', token)
        wild = re.fullmatch(r'_ : bits\((\d+)\)', token)
        require(fixed or wild, 'unknown pattern token')
        if fixed:
            n = len(fixed[1]); v = int(fixed[1], 2)
            segments.append('.fixed ' + quoted(fixed[1]))
            chunks += ['0b', fixed[1]]
        else:
            n = int(wild[1]); v = 0
            segments.append('.any ' + str(n))
            chunks += ['_ : bits(', str(n), ')']
        require(0 < n <= 32, 'bad pattern width')
        width += n; mask = mask << n | ((1 << n)-1 if fixed else 0); value = value << n | v
    require(width == 32, 'pattern width must be 32')
    chunks += [' as op_code) if SEE < ', str(index), ') = {\n    SEE = ', str(index), ';\n']
    fields = []; args = []
    for line in lines[2:-2]:
        f = re.fullmatch(r'    ([A-Za-z_][A-Za-z_0-9]*) : bits\((\d+)\) = (op_code\[(\d+) \.\. (\d+)\]|\[op_code\[(\d+)\]\]);', line)
        require(f is not None, 'unknown field declaration')
        high = int(f[4] or f[6]); low = int(f[5] or f[6]); n = int(f[2]); single = f[6] is not None
        require(0 <= low <= high < 32 and n == high-low+1, 'invalid field width/bounds')
        args.append(f[1])
        chunks += ['    ', f[1], ' : bits(', str(n), ') = ']
        chunks += ['[op_code[', str(high), ']]'] if single else ['op_code[', str(high), ' .. ', str(low), ']']
        chunks += [';\n']
        fields.append('⟨'+quoted(f[1])+f', {n}, {high}, {low}, '+str(single).lower()+'⟩')
    call = re.fullmatch(r'    ([A-Za-z_][A-Za-z_0-9]*)\(([A-Za-z_0-9, ]*)\)', lines[-2])
    require(call is not None and lines[-1] == '}', 'unknown terminal call/end')
    callee = call[1]
    require(call[2].split(', ') == args and len(set(args)) == len(args), 'argument/binder mismatch')
    require(not ({'op_code', 'SEE', callee} & set(args)), 'binder capture')
    chunks += ['    ', callee, '(']
    for i, arg in enumerate(args):
        chunks += [arg] if i == 0 else [', ', arg]
    chunks += [')\n}\n']
    require(''.join(chunks) == raw, 'whole-clause reconstruction differs')
    cert = '⟨['+', '.join(segments)+f'], {index}, ['+', '.join(fields)+'], '+quoted(callee)+'⟩'
    return dict(index=index, mask=mask, value=value, chunks=chunks, cert=cert, raw=raw)

def inventory(data):
    require(data.isascii(), 'source must be ASCII')
    source = data.decode('ascii')
    marker = 'function clause decode64 '
    offset = source.find(marker)
    require(offset >= 0 and (offset == 0 or source[offset-1] == '\n'), 'missing anchored first clause')
    prefix = source[:offset]
    require(digest(prefix.encode('ascii')) == PREFIX_PIN, 'pinned prefix mismatch')
    # Fixed snapshot: only the declaration can mention decode64 before the region.
    require(prefix.count('decode64') == 1 and
            re.search(r'^val decode64 : bits\(32\) -> unit effect \{configuration, escape, undef, wreg, rreg, rmem, wmem\}\n', prefix, re.M),
            'unexpected decode64 declaration/comment/string in prefix')
    tail = source[offset:]
    clauses = []; gaps = []; pos = 0
    pattern = re.compile(r'function clause decode64 [^\n]*\n(?:[^\n]*\n)*?}\n')
    while pos < len(tail):
        match = pattern.match(tail, pos)
        require(match is not None, 'unmatched/unknown text in decode64 region')
        clauses.append(parse_clause(match[0])); pos = match.end()
        gap = re.match(r'\n*', tail[pos:])[0]; gaps.append(gap); pos += len(gap)
    require(len(clauses) == 917, 'missing/extra/duplicate clause')
    require([c['index'] for c in clauses] == list(range(1026,1943)), 'changed guard/order/duplicate index')
    require(source.count(marker) == 917 and len(re.findall(r'^function clause decode64\b',source,re.M)) == 917,
            'unaccounted decoder clause')
    rebuilt = prefix + ''.join(''.join(c['chunks']) + gap for c,gap in zip(clauses,gaps))
    require(rebuilt.encode('ascii') == data, 'complete-file reconstruction mismatch')
    return prefix, clauses, gaps

def generated(data):
    prefix, clauses, gaps = inventory(data)
    outputs = {}
    batch_names = []
    for start in range(0, len(clauses), BATCH):
        group = clauses[start:start+BATCH]; number = start//BATCH
        label = f'Batch{number:03d}'; batch_names.append(label)
        text = 'import Oak.ArmDecoderClassification.Checker\n\nnamespace Oak.ArmDecoderClassification.Data\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n\n'
        for c in group:
            i = c['index']; raw = '['+', '.join(map(quoted,c['chunks']))+']'
            text += f'def raw{i} : List String := {raw}\ndef clause{i} : Clause := {c["cert"]}\n'
            text += f'theorem checked{i} : check raw{i} clause{i} = true := by rfl\n'
            text += f'def row{i} : Row := ⟨{i}, {c["mask"]}, {c["value"]}⟩\n'
            text += f'theorem derived{i} : clause{i}.row = row{i} := by rfl\n'
            text += f'def entry{i} : CheckedRow := ⟨raw{i}, clause{i}, row{i}, checked{i}, derived{i}⟩\n\n'
        text += f'def entries{number} : List CheckedRow := ['+', '.join('entry'+str(c['index']) for c in group)+']\n'
        text += f'def rows{number} : List Row := ['+', '.join('row'+str(c['index']) for c in group)+']\n'
        text += f'theorem indices{number} : rows{number}.map Row.index = {[c["index"] for c in group]} := by rfl\n'
        text += f'theorem bound{number} : entries{number}.map CheckedRow.row = rows{number} := by rfl\n'
        for name, word in WORDS:
            choices = [c['index'] for c in group if word & c['mask'] == c['value']]
            text += f'theorem choices_{name}_{number} : choices rows{number} {word}#32 (-1) = {choices} := by rfl\n'
        text += '\nend Oak.ArmDecoderClassification.Data\n'
        outputs[label+'.lean'] = text.encode()
    text = ''.join('import Oak.ArmDecoderClassification.'+n+'\n' for n in batch_names)
    text += '\nnamespace Oak.ArmDecoderClassification\nopen Data\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n\n/-- Composes already checked batches without normalizing their raw source again. -/\nstructure Batch where\n  entries : List CheckedRow\n  rows : List Row\n  bound : entries.map CheckedRow.row = rows\n  indexList : List Nat\n  indices_bound : rows.map Row.index = indexList\n  andMatches : List Nat\n  and_bound : choices rows 0x0a010000#32 (-1) = andMatches\n  orrMatches : List Nat\n  orr_bound : choices rows 0x2a010000#32 (-1) = orrMatches\n  eorMatches : List Nat\n  eor_bound : choices rows 0x4a010000#32 (-1) = eorMatches\n  retMatches : List Nat\n  ret_bound : choices rows 0xd65f03c0#32 (-1) = retMatches\n\ninductive Word where | and | orr | eor | ret\n\ndef Word.bits : Word → BitVec 32\n  | .and => 0x0a010000 | .orr => 0x2a010000 | .eor => 0x4a010000 | .ret => 0xd65f03c0\n\ndef Batch.matches (b : Batch) : Word → List Nat\n  | .and => b.andMatches | .orr => b.orrMatches | .eor => b.eorMatches | .ret => b.retMatches\n\ntheorem Batch.proved (b : Batch) (w : Word) : choices b.rows w.bits (-1) = b.matches w := by\n  cases w with\n  | and => exact b.and_bound\n  | orr => exact b.orr_bound\n  | eor => exact b.eor_bound\n  | ret => exact b.ret_bound\n\ntheorem choices_flatMap (bs : List Batch) (word : BitVec 32) (see : Int) :\n    choices (bs.flatMap Batch.rows) word see = bs.flatMap (fun b => choices b.rows word see) := by\n  simp only [choices, List.filter_flatMap, List.map_flatMap]\n\n'
    for number, start in enumerate(range(0,len(clauses),BATCH)):
        group=clauses[start:start+BATCH]
        fields=[f'entries{number}',f'rows{number}',f'bound{number}',str([c['index'] for c in group]),f'indices{number}']
        for name,word in WORDS:
            fields.extend([str([c['index'] for c in group if word & c['mask']==c['value']]),f'choices_{name}_{number}'])
        text+=f'def batch{number} : Batch := ⟨'+', '.join(fields)+'⟩\n'
    text+='\ndef batches : List Batch := ['+', '.join(f'batch{i}' for i in range(len(batch_names)))+']\n'
    text+='def embedded : List CheckedRow := batches.flatMap Batch.entries\ndef table : List Row := batches.flatMap Batch.rows\n\n'
    text+='theorem table_bound : embedded.map CheckedRow.row = table := by\n  rw [embedded, table, List.map_flatMap]\n  exact congrArg (fun f => batches.flatMap f) (funext fun b => b.bound)\n\n'
    text+='theorem table_index_batches : table.map Row.index = batches.flatMap Batch.indexList := by\n  rw [table, List.map_flatMap]\n  exact congrArg (fun f => batches.flatMap f) (funext fun b => b.indices_bound)\n\n'
    text+='theorem table_indices : table.map Row.index = '+str(list(range(1026,1943)))+' := by\n  rw [table_index_batches]; rfl\n\n'
    text+='theorem table_choices (word : Word) : choices table word.bits (-1) = batches.flatMap (fun b => b.matches word) := by\n  rw [table, choices_flatMap]\n  exact congrArg (fun f => batches.flatMap f) (funext fun b => b.proved word)\n\n'
    text+='theorem embedded_bytes_bound (a : CheckedRow) (_ : a ∈ embedded) :\n    a.clause.valid = true ∧ String.join a.clause.chunks = String.join a.raw ∧ a.clause.row = a.row := row_bound a\n\n'
    for name,word in WORDS:
        selected=[c['index'] for c in clauses if word & c['mask']==c['value']]
        require(len(selected)==1,'target is not unique')
        text+=f'theorem unique_{name} : choices table {word}#32 (-1) = {selected} := by\n  change choices table Word.{name}.bits (-1) = _\n  rw [table_choices]; rfl\n'
        text+=f'theorem first_{name} : first table {word}#32 (-1) = some {selected[0]} := by\n  rw [first, unique_{name}]; rfl\n\n'
    text+='end Oak.ArmDecoderClassification\n'
    outputs['Selection.lean'] = text.encode()
    manifest = {'source_sha256':digest(data), 'source_bytes':len(data), 'prefix_bytes':len(prefix.encode()), 'prefix_sha256':digest(prefix.encode()),
                'clauses':len(clauses), 'clauses_bytes':sum(len(c['raw']) for c in clauses), 'separators':gaps,
                'boundary':'Complete-file extraction, parser completeness and source pin are trusted CI checks, not kernel-proved Sail parsing.',
                'files':{name:digest(content) for name,content in outputs.items()}}
    return outputs, manifest

def main():
    p=argparse.ArgumentParser();p.add_argument('--generate',action='store_true');p.add_argument('--source',type=pathlib.Path);args=p.parse_args()
    actual=args.source or ROOT/'external/sail-arm/arm-v8.5-a/model/aarch_decode.sail'
    data=actual.read_bytes();require(digest(data)==PIN,'pinned complete source mismatch')
    outputs,manifest=generated(data)
    if args.generate:
        SOURCE.write_bytes(data)
        for name,content in outputs.items():(DATA/name).write_bytes(content)
        (HERE/'decoder_classification_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    else:
        require(SOURCE.read_bytes()==data,'embedded complete source mismatch')
        require(json.loads((HERE/'decoder_classification_manifest.json').read_text())==manifest,'inventory manifest mismatch')
        require({x.name for x in DATA.glob('Batch*.lean')}=={n for n in outputs if n.startswith('Batch')},'extra/missing batch module')
        for name,content in outputs.items():require((DATA/name).read_bytes()==content,'certificate generation mismatch: '+name)
    print(f'Complete-file reconstruction checked: {len(data)} bytes, 917 clauses; trusted extraction boundary retained.')

if __name__=='__main__':main()
