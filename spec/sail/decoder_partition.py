#!/usr/bin/env python3
"""Untrusted partition certificates; independent source copying is separate."""
import argparse
import json
import pathlib
import decoder_classification as old
import copy_decoder_source_pages as source_copy

OUT=source_copy.OUT
BATCH=8

def header(imports):
    return '\n'.join('import '+s for s in sorted(set(imports)))+'\n\nnamespace Oak.ArmDecoderPartition.Data\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\nset_option linter.unusedSimpArgs false\n'

def inventory(data):
    pre,clauses,gaps=old.inventory(data)
    if gaps!=['\n']*916+['']:raise RuntimeError('unexpected separator layout')
    segments=[('pre',0,len(pre))];pos=len(pre)
    for c,g in zip(clauses,gaps):
        size=len(''.join(c['chunks']));segments.append(('c'+str(c['index']),pos,pos+size));pos+=size
        if g:segments.append(('lf',pos,pos+1));pos+=1
    if pos!=len(data):raise RuntimeError('partition EOF')
    pagecells={};partcells={};precells=[]
    for kind,start,end in segments:
        a=start
        while a<end:
            b=min(end,(a//1024+1)*1024);page=a//1024
            name='lf' if kind=='lf' else f'cell{a}'
            pagecells.setdefault(page,[]).append((name,a,b))
            if kind=='pre':precells.append(name)
            elif kind!='lf':partcells.setdefault(int(kind[1:]),[]).append((name,page))
            a=b
    return pre,clauses,pagecells,partcells,precells

def page_declarations(page,pc):
    lines=[];lengths=[b-a for _,a,b in pc[:-1]];gapproofs=[]
    for k,(name,a,b) in enumerate(pc):
        offset=a-page*1024
        expr=f'(Source.page{page}.drop {offset})' if offset else f'Source.page{page}'
        if k<len(pc)-1:expr+=f'.take {b-a}'
        if name!='lf':
            lines.append(f'def {name} : Cell := ⟨{expr}, {b-a}, by simp only [List.length_take, List.length_drop, Source.size{page}] <;> rfl⟩')
        else:
            gp=f'gap{a}';gapproofs.append(gp)
            lines.append(f'theorem {gp} : {expr} = [10] := by rfl')
    refs=', '.join(x[0] for x in pc)
    lines.append(f'def coveredPage{page} : Page := ⟨Source.page{page}, [{refs}], by')
    if not lengths:lines.append('  rfl⟩')
    else:
        lines.append(f'  have h := (cutBytes_cover {lengths} Source.page{page}).symm')
        lines.append('  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd'+''.join(', '+g for g in gapproofs)+'] at h')
        lines.append('  exact h⟩')
    return '\n'.join(lines)+'\n'

def scan_state(data):
    return '('+str(list(data[:7]))+', '+str(data.count(b'decode64'))+')'

def generated(data):
    pre,clauses,pagecells,partcells,precells=inventory(data);expected={}
    pages=len(pagecells);prebytes=pre.encode();prepages=(len(prebytes)+1023)//1024
    for start in range(0,pages,BATCH):
        indices=range(start,min(start+BATCH,pages))
        text=header(['Oak.ArmDecoderPartition.Checker']+[f'Oak.ArmDecoderPartition.SourceBatch{i//16:03}' for i in indices])
        text+=''.join(page_declarations(i,pagecells[i]) for i in indices)
        text+='end Oak.ArmDecoderPartition.Data\n';expected[f'PageBatch{start//BATCH:03}.lean']=text
    for start in range(0,len(clauses),BATCH):
        indices=[c['index'] for c in clauses[start:start+BATCH]]
        imports=[f'Oak.ArmDecoderClassification.Batch{start//8:03}']+[f'Oak.ArmDecoderPartition.PageBatch{page//BATCH:03}' for i in indices for _,page in partcells[i]]
        text=header(imports)
        for i in indices:
            refs=', '.join(n for n,_ in partcells[i])
            text+=f'def part{i} : Part := ⟨Oak.ArmDecoderClassification.Data.entry{i}, [{refs}], by rfl⟩\n'
        text+='end Oak.ArmDecoderPartition.Data\n';expected[f'PartBatch{start//BATCH:03}.lean']=text
    for start in range(0,prepages,BATCH):
        indices=range(start,min(start+BATCH,prepages))
        imports=['Oak.ArmDecoderPartition.Prefix']+[f'Oak.ArmDecoderPartition.PageBatch{i//BATCH:03}' for i in indices]
        text=header(imports)
        for i in indices:
            a=i*1024;b=min(a+1024,len(prebytes));expr=f'cell{a}.bytes'
            text+=f'theorem scanPage{i} : scan {expr} {scan_state(prebytes[b:])} = {scan_state(prebytes[a:])} := by rfl\n'
        text+='end Oak.ArmDecoderPartition.Data\n';expected[f'PrefixBatch{start//BATCH:03}.lean']=text
    imports=['Oak.ArmDecoderClassification.Selection','Oak.ArmDecoderClassification.ByteBinding','Oak.ArmDecoderPartition.Declaration']
    imports += [f'Oak.ArmDecoderPartition.PartBatch{i:03}' for i in range((len(clauses)+7)//8)]
    imports += [f'Oak.ArmDecoderPartition.PrefixBatch{i:03}' for i in range((prepages+7)//8)]
    text=header(imports)
    text+='def inputs : List SizedBytes := ['+', '.join(f'Source.input{i}' for i in range(pages))+']\n'
    text+='def pages : List Page := ['+', '.join(f'coveredPage{i}' for i in range(pages))+']\n'
    text+='def pre : List Cell := ['+', '.join(precells)+']\n'
    text+='def parts : List Part := ['+', '.join(f'part{c["index"]}' for c in clauses)+']\n'
    text+='def sourceBytes : Bytes := inputs.flatMap SizedBytes.bytes\ndef prefixBytes : Bytes := pre.flatMap Cell.bytes\n'
    text+='theorem page_input : pages.map Page.bytes = inputs.map SizedBytes.bytes := by rfl\n'
    text+='theorem cell_order : pages.flatMap Page.cells = pre ++ separated Part.cells parts := by rfl\n'
    text+='theorem same_entries : parts.map Part.entry = Oak.ArmDecoderClassification.embedded := by rfl\n'
    text+='''theorem complete_source : sourceBytes = prefixBytes ++
    separatedBytes (fun e => rawBytes e.raw) Oak.ArmDecoderClassification.embedded := by
  have h := partition_sound pages pre parts cell_order
  have hb : pages.flatMap Page.bytes = sourceBytes := by
    exact congrArg List.flatten page_input
  rw [hb, ← separatedBytes_map (fun e => rawBytes e.raw) Part.entry, same_entries] at h
  exact h

theorem source_size : sourceBytes.length = 833374 := by
  rw [sourceBytes, sizedBytes_length]; rfl

theorem prefix_size : prefixBytes.length = 400975 := by
  rw [prefixBytes, cell_lengths]; rfl

theorem same_table : parts.map (fun p => p.entry.row) = Oak.ArmDecoderClassification.table := by
  have h := congrArg (List.map Oak.ArmDecoderClassification.CheckedRow.row) same_entries
  simpa only [List.map_map, Function.comp_def, Oak.ArmDecoderClassification.table_bound] using h

theorem source_prefix : sourceBytes.take 400975 = prefixBytes := by
  rw [complete_source, ← prefix_size, List.take_left]

theorem source_region : sourceBytes.drop 400975 =
    separatedBytes (fun e => rawBytes e.raw) Oak.ArmDecoderClassification.embedded := by
  rw [complete_source, ← prefix_size, List.drop_left]
'''
    text+='def prefixBlocks : List Bytes := ['+', '.join(f'cell{i*1024}.bytes' for i in range(prepages))+']\n'
    text+='theorem prefix_blocks : prefixBlocks = pre.map Cell.bytes := by rfl\n'
    text+='theorem prefix_trace : ScanTrace prefixBlocks ([],0) '+scan_state(prebytes)+' :=\n'
    text+='  '+''.join(f'.cons scanPage{i} (' for i in range(prepages))+'.nil ([],0)'+')'*prepages+'\n'
    text+='''theorem prefix_occurrences : occurrences prefixBytes = 1 := by
  have h := prefix_trace.sound
  rw [prefix_blocks] at h
  change scan prefixBytes = _ at h
  have hc := congrArg Prod.snd h
  rw [scan_exact] at hc
  exact hc

theorem prefix_declaration : declaration <:+: prefixBytes := by
  have hm : Source.page3 ∈ prefixBlocks := by
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have h := declaration_in_page.trans (List.infix_of_mem_flatten hm)
  rw [prefix_blocks] at h
  exact h

theorem prefix_ends_lf : ([10] : Bytes) <:+ prefixBytes := by
  have h : prefixBlocks = prefixBlocks.take 391 ++ [cell400384.bytes] := by rfl
  have hb := congrArg List.flatten h
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] at hb
  rw [prefix_blocks] at hb
  change prefixBytes = _ at hb
  rw [hb]
  exact prefix_last_lf.trans (List.suffix_append _ _)

theorem first_header : (sourceBytes.drop 400975).take 27 =
    rawBytes ["function clause decode64 (("] := by
  rw [source_region]
  rfl

theorem clause_count : Oak.ArmDecoderClassification.embedded.length = 917 := by
  have h := congrArg List.length Oak.ArmDecoderClassification.table_indices
  rw [List.length_map] at h
  have hb := congrArg List.length Oak.ArmDecoderClassification.table_bound
  rw [List.length_map] at hb
  exact hb.trans h

theorem clause_bytes_from_partition {α : Type} (f : α → Bytes) (xs : List α)
    (source pre : Bytes) (bound : source = pre ++ separatedBytes f xs)
    (sourceSize : source.length = 833374) (prefixSize : pre.length = 400975)
    (count : xs.length = 917) : (xs.map (fun e => (f e).length)).sum = 431483 := by
  have h := congrArg List.length bound
  rw [sourceSize, List.length_append, prefixSize, separatedBytes_length, count] at h
  omega

theorem clause_bytes :
    (Oak.ArmDecoderClassification.embedded.map (fun e => (rawBytes e.raw).length)).sum = 431483 :=
  clause_bytes_from_partition _ _ _ _ complete_source source_size prefix_size clause_count

theorem function_bytes_classified (op : Oak.BitwiseFunction.Op) :
    Oak.ArmDecoderClassification.classifyFunction
      (Oak.AArch64BitwiseFunction.functionBytes op) =
      some (Oak.ArmDecoderClassification.logicalIndex op,1522) :=
  Oak.ArmDecoderClassification.function_bytes_classified op
'''
    text+='end Oak.ArmDecoderPartition.Data\n';expected['Complete.lean']=text
    return expected

def main():
    p=argparse.ArgumentParser();p.add_argument('--source',type=pathlib.Path,required=True);p.add_argument('--generate',action='store_true');args=p.parse_args()
    data=source_copy.check(args.source)
    expected=generated(data)
    patterns=['Page*.lean','Part*.lean','PrefixBatch*.lean','Complete.lean']
    existing={x.name:x for pat in patterns for x in OUT.glob(pat)}
    if args.generate:
        for name,path in existing.items():
            if name not in expected:path.unlink()
        for name,text in expected.items():(OUT/name).write_text(text)
    elif set(existing)!=set(expected):raise RuntimeError('partition module inventory mismatch')
    for name,text in expected.items():
        if (OUT/name).read_text()!=text:raise RuntimeError('partition certificate drift: '+name)
    print(f'Partition certificates checked: {len(expected)} modules; original-byte copy remains independent.')

if __name__=='__main__':main()
