"""Exact local checker witnesses and ordered clause composition."""
import hashlib
import re
from common import require

ctx = None

def refuse(message):
    raise ValueError(message)

def charge(amount=1):
    ctx.charge(amount)

def digest(raw):
    charge(len(raw))
    return hashlib.sha256(raw).hexdigest()

def split_top(text):
    charge(len(text))
    pairs = {']': '[', ')': '(', '⟩': '⟨', '}': '{'}
    stack, parts = [], []
    start = 0
    for index, character in enumerate(text):
        if character == '"' or text[index:index+2] in ('--', '/-', '-/'):
            refuse('unsupported literal grammar')
        if character in '[({⟨':
            stack.append(character)
            if len(stack) > 64:
                refuse('literal nesting cap')
        elif character in pairs:
            if not stack or stack.pop() != pairs[character]:
                refuse('literal delimiter mismatch')
        elif character == ',' and not stack:
            parts.append(text[start:index].strip())
            start = index + 1
    if stack:
        refuse('unclosed literal')
    parts.append(text[start:].strip())
    if any(not part for part in parts):
        refuse('empty literal field')
    charge(len(parts))
    return parts


def literal(text):
    if not text.startswith('[') or not text.endswith(']'):
        refuse('literal list expected')
    values = [] if text == '[]' else split_top(text[1:-1])
    if '[' + ', '.join(values) + ']' != text:
        refuse('noncanonical list')
    return values


def tuple_fields(text, size):
    if not text.startswith('⟨') or not text.endswith('⟩'):
        refuse('tuple expected')
    values = split_top(text[1:-1])
    if len(values) != size or '⟨' + ', '.join(values) + '⟩' != text:
        refuse('tuple shape')
    return values


def balanced(values, combine=None):
    charge(1)
    if not values:
        refuse('empty append expression')
    if len(values) == 1:
        return values[0]
    middle = len(values) // 2
    left, right = balanced(values[:middle], combine), balanced(values[middle:], combine)
    return ('(' + left + ' ++ ' + right + ')') if combine is None else combine(left, right)


def header(imports):
    return ''.join('import ' + name + '\n' for name in imports) + '''
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TypedCNFInstance
open Oak
open Oak.RupCheck Oak.TseitinCNF Oak.CNFBuilderTrace Oak.CNFDenseAllocation
open Oak.CNFCheckComposition

'''


def member_proof(index, names, hypothesis='member'):
    if len(names) == 1:
        if index != 0:
            refuse('membership leaf')
        return hypothesis
    middle = len(names) // 2
    if index < middle:
        return '(List.mem_append_left ' + balanced(names[middle:]) + ' ' + member_proof(index, names[:middle], hypothesis) + ')'
    return '(List.mem_append_right ' + balanced(names[:middle]) + ' ' + member_proof(index-middle, names[middle:], hypothesis) + ')'


def nat(text):
    if not re.fullmatch(r'0|[1-9][0-9]*', text):
        refuse('natural literal')
    value = int(text)
    if value > 100000:
        refuse('natural literal cap')
    return value


def raw_gate(values):
    op, x, y, z, out = values
    def edge(value):
        return '⟨%d, %s⟩' % (value // 2, str(value % 2 == 0).lower())
    if op not in range(4) or (op != 3 and z != 0):
        refuse('gate tag/unused edge')
    return '(.%s %d %s)' % (['andGate','orGate','xorGate','iteGate'][op], out,
                          ' '.join(edge(value) for value in ([x,y,z] if op == 3 else [x,y])))


def memo_key(values):
    op,x,y,z,_ = values
    return ('.ite %d %d %d' % (x,y,z)) if op == 3 else ('.binary %d %d %d' % (op,x,y))


def intervals(start, stop, depth):
    if depth == 0:
        return [(start,stop)]
    middle = start + (stop-start+1)//2
    return intervals(start,middle,depth-1) + intervals(middle,stop,depth-1)


def save(name, text):
    raw = text if isinstance(text, bytes) else (text + '\nend TypedCNFInstance\n').encode()
    return ctx.save('TypedCNFInstance.' + name, raw)


def project(stage):
    global ctx
    ctx = stage
    sources, blocks = {}, {}
    required = ['InputData00'] + ['GateData%02d'%i for i in range(5)] + ['MemoData%02d'%i for i in range(5)] + ['ClauseData%02d'%i for i in range(21)] + ['Data','Checks'] + ['Nodes%02d'%i for i in range(15)] + ['Final']
    sources = {}
    blocks = {}
    for name in required:
        module = 'TypedCNFInstance.' + name
        raw = stage.source('data', module) if module in stage.receipt('data') else stage.raw(module)
        sources[name] = raw
        for line in raw.decode().splitlines():
            match = re.fullmatch(r'def (typed(?:Input|Gate|Memo|Clause)Block[0-9]{3}) : .* := (\[.*\])',line)
            if match:
                if match[1] in blocks:
                    refuse('duplicate block')
                blocks[match[1]] = literal(match[2])
    expected_sizes = {'Input':(3,353),'Gate':(20,2537),'Memo':(20,2537),'Clause':(81,10351)}
    for family,(count,total) in expected_sizes.items():
        if sum(len(blocks['typed%sBlock%03d'%(family,i)]) for i in range(count)) != total:
            refuse('block aggregate count')
        for i in range(count):
            if len(blocks['typed%sBlock%03d'%(family,i)]) != min(128,total-128*i):
                refuse('block size')
    if len(blocks) != 124:
        refuse('block inventory')
    gates = [[nat(field) for field in tuple_fields(value,5)] for i in range(20) for value in blocks['typedGateBlock%03d'%i]]
    memos = [value for i in range(20) for value in blocks['typedMemoBlock%03d'%i]]
    memo_index = {}
    for index,value in enumerate(memos):
        key,output = tuple_fields(value,2)
        if key in memo_index:
            refuse('duplicate memo key')
        memo_index[key] = (index,nat(output),value)
    gate_bindings = []
    for index,gate in enumerate(gates):
        key = memo_key(gate)
        entry_index,out,entry = memo_index[key]
        if out != gate[4]:
            refuse('memo output differs')
        gate_bindings.append([index,entry_index//128,entry_index%128])
    gate_ends=[0]
    for first in range(0,len(gates),128):
        gate_ends.append(gate_ends[-1]+sum([3,3,4,6][gate[0]] for gate in gates[first:first+128]))
    if gate_ends != [0,410,832,1426,2176,2872,3383,3784,4230,4666,5084,5528,6008,6444,6959,7508,7988,8633,9305,9881,10351]:
        refuse('gate clause endpoints')
    original_ranges=intervals(0,10352,6)
    for i in range(32):
        raw=stage.source('refutation', 'TypedCNFRefutation.Clauses%02d'%i).decode()
        for block in (2*i,2*i+1):
            lines=[line for line in raw.splitlines() if line.startswith('def block%02d : '%block)]
            if len(lines)!=1:
                refuse('original block inventory')
            ids=[int(value) for value in re.findall(r'Original.leaf c([0-9]+)',lines[0])]
            start,stop=original_ranges[block]
            if ids!=list(range(start+1,stop+1)):
                refuse('original ordered block IDs')
    boundaries=sorted(set([0,10351,10352]+list(range(0,10351,128))+gate_ends+[point for pair in original_ranges for point in pair]))
    segments=list(zip(boundaries,boundaries[1:]))
    if len(segments)!=163 or max(stop-start for start,stop in segments)>128:
        refuse('segment inventory/cap')
    def indexes(start,stop):
        result=[i for i,(left,right) in enumerate(segments) if start<=left and right<=stop]
        if not result or segments[result[0]][0]!=start or segments[result[-1]][1]!=stop:
            refuse('segment span')
        return result
    def signed(ids):
        return balanced(['signedSegment%03d'%i for i in ids])
    def decoded(ids):
        return balanced(['decodedSegment%03d'%i for i in ids])
    outputs=[]
    text=header(['Oak.CNFCheckComposition','TypedCNFInstance.Data'])
    text+='''theorem allocation_shape : Shape allocation := by
  have sourceUnique : (inputSources allocation).Nodup :=
    strictNatIncreasing_nodup (by decide)
  have memoUnique : (memoKeys allocation).Nodup :=
    nodup_of_map_nodup memoCode (strictNatIncreasing_nodup (by decide))
  have outputShape := outputs_shape_of_sorted (snapshot := allocation) (by decide)
  exact ⟨rfl, sourceUnique, memoUnique, by decide, by decide, by decide,
    by decide, outputShape.1, outputShape.2⟩

'''
    memo_names=['typedMemoBlock%03d'%i for i in range(20)]
    for i in range(20):
        text+=('theorem memoBlock%02d_member {entry : MemoEntry}\n    (member : entry ∈ %s) : entry ∈ allocation.memo := by\n  change entry ∈ %s\n  exact %s\n\n')%(i,memo_names[i],balanced(memo_names),member_proof(i,memo_names))
    outputs.append(save('CheckShape',text))
    for block in range(20):
        first=128*block; chunk=gates[first:first+128]
        previous=0 if first==0 else gates[first-1][4]
        text=header(['TypedCNFInstance.CheckShape'])
        text+='def rawGates%02d : List RawGate := [%s]\n\n'%(block,', '.join(raw_gate(gate) for gate in chunk))
        text+='theorem gateChunk%02d : GateChunk 2890 allocation.memo %d %d typedGateBlock%03d rawGates%02d := by\n'%(block,previous,chunk[-1][4],block,block)
        for offset,gate in enumerate(chunk):
            key=memo_key(gate); entry_index,_,entry=memo_index[key]
            text+='  refine GateChunk.cons (key := %s) (by rfl) (by decide) (by decide)\n'%('('+key+')')
            text+='    ((operandsBefore_eq_true_iff _ _).mp (by decide)) (by decide) ?_ ?_\n'
            text+='  · exact lookupMemo_of_mem allocation_shape.memoKeysUnique\n'
            text+='      (memoBlock%02d_member (entry := %s) (by decide))\n'%(entry_index//128,entry)
        text+='  exact GateChunk.nil _ _ _\n'
        outputs.append(save('CheckGate%02d'%block,text))
    text=header(['TypedCNFInstance.CheckGate%02d'%i for i in range(20)])
    text+='def rawGates : List RawGate := '+balanced(['rawGates%02d'%i for i in range(20)])+'\n\n'
    text+='theorem allocation_exact : CNFDenseAllocation.check allocation = some rawGates := by\n'
    text+='  apply allocation_check_complete\n  refine ⟨allocation_shape, ?_⟩\n  exact GateChunk.close '+balanced(['gateChunk%02d'%i for i in range(20)],lambda l,r:'(GateChunk.append '+l+' '+r+')')+'\n\n'
    text+='def explicitChecked : CNFClauseTrace.Checked := ⟨rawGates, [⟨2890, false⟩]⟩\n'
    outputs.append(save('CheckAllocation',text))
    segment_inventory=[]
    for module in range(11):
        text=header(['Oak.CNFCheckComposition','TypedCNFInstance.Data'])
        for i in range(16*module,min(16*module+16,163)):
            start,stop=segments[i]; block=start//128; offset=start%128; count=stop-start
            expr='[[-2890]]' if start==10351 else '(typedClauseBlock%03d.drop %d).take %d'%(block,offset,count)
            if start!=10351 and offset+count>len(blocks['typedClauseBlock%03d'%block]):
                refuse('segment outside local source block')
            segment_inventory.append([i,start+1,stop,None if start==10351 else block,offset,count])
            text+='def signedSegment%03d : List (List Int) := %s\n'%(i,expr)
            text+='def decodedSegment%03d : List Clause := [%s]\n'%(i,', '.join('TypedCNFRefutation.c%d'%j for j in range(start+1,stop+1)))
            text+='theorem segment%03d_decode : CNFClauseTrace.decodeClauses signedSegment%03d = some decodedSegment%03d := by decide\n\n'%(i,i,i)
        outputs.append(save('CheckSegments%02d'%module,text))
    all_segments=['TypedCNFInstance.CheckSegments%02d'%i for i in range(11)]
    for module in range(5):
        text=header(all_segments)
        for block in range(17*module,min(17*module+17,81)):
            start=128*block; stop=min(start+128,10351)
            text+='theorem clauseBlock%02d_exact : typedClauseBlock%03d = %s := by decide\n'%(block,block,signed(indexes(start,stop)))
            text+='theorem clauseBlock%02d_length : typedClauseBlock%03d.length = %d := by decide\n\n'%(block,block,stop-start)
        outputs.append(save('CheckClauseBlocks%02d'%module,text))
    for module in range(4):
        text=header(all_segments)
        for block in range(16*module,16*module+16):
            start,stop=original_ranges[block]
            text+='theorem originalBlock%02d_exact : TypedCNFRefutation.block%02d.toList = %s := by decide\n\n'%(block,block,decoded(indexes(start,stop)))
        outputs.append(save('CheckOriginalBlocks%02d'%module,text))
    for module in range(4):
        text=header(['TypedCNFInstance.CheckAllocation']+all_segments)
        for block in range(5*module,5*module+5):
            text+='theorem gateBlock%02d_clauses : CNFClauseTrace.encodeClauses (gateClauses rawGates%02d) = %s := by decide\n\n'%(block,block,signed(indexes(gate_ends[block],gate_ends[block+1])))
        outputs.append(save('CheckGateClauses%02d'%module,text))
    imports=['TypedCNFInstance.CheckAllocation']+['TypedCNFInstance.CheckClauseBlocks%02d'%i for i in range(5)]+['TypedCNFInstance.CheckOriginalBlocks%02d'%i for i in range(4)]+['TypedCNFInstance.CheckGateClauses%02d'%i for i in range(4)]
    text=header(imports)
    text+='theorem builder_exact : typedBuilderClauses = CNFClauseTrace.encodeClauses (gateClauses rawGates) := by\n'
    text+='  simp only [typedBuilderClauses, rawGates, gateClauses_append, encodeClauses_append,\n    '+', '.join('clauseBlock%02d_exact'%i for i in range(81))+',\n    '+', '.join('gateBlock%02d_clauses'%i for i in range(20))+', List.append_assoc]\n\n'
    text+='theorem builder_length : typedBuilderClauses.length = 10351 := by\n'
    text+='  simp only [typedBuilderClauses, List.length_append, '+', '.join('clauseBlock%02d_length'%i for i in range(81))+']\n\n'
    text+='''theorem trace_explicit : CNFClauseTrace.check trace = some explicitChecked := by
  apply clause_check_complete
  refine ⟨allocation_exact, ?_, by decide, by decide, builder_exact, ?_⟩
  · change typedBuilderClauses.length ≤ 50000000
    rw [builder_length]
    decide
  · change typedBuilderClauses ++ [[-2890]] =
      CNFClauseTrace.encodeClauses (builderClauses rawGates [⟨2890, false⟩])
    rw [encodeBuilderClauses, ← builder_exact]
    rfl

theorem trace_some : (CNFClauseTrace.check trace).isSome = true := by
  rw [trace_explicit]
  rfl

def checked : CNFClauseTrace.Checked := (CNFClauseTrace.check trace).get trace_some
theorem trace_accepted : CNFClauseTrace.check trace = some checked := Option.eq_some_of_isSome trace_some

'''
    text+='theorem emitted_segments : trace.emitted = '+signed(list(range(163)))+' := by\n'
    text+='  change typedBuilderClauses ++ [[-2890]] = _\n'
    text+='  simp only [typedBuilderClauses, '+', '.join('clauseBlock%02d_exact'%i for i in range(81))+', signedSegment162, List.append_assoc]\n\n'
    text+='theorem original_segments : TypedCNFRefutation.original.toList = '+decoded(list(range(163)))+' := by\n'
    text+='  change '+balanced(['TypedCNFRefutation.block%02d.toList'%i for i in range(64)])+' = _\n'
    text+='  simp only ['+', '.join('originalBlock%02d_exact'%i for i in range(64))+', List.append_assoc]\n\n'
    text+='theorem clauses_bound : CNFClauseTrace.decodeClauses trace.emitted = some TypedCNFRefutation.original.toList := by\n'
    text+='  rw [emitted_segments, original_segments]\n  exact '+balanced(['segment%03d_decode'%i for i in range(163)],lambda l,r:'(decodeClauses_append '+l+' '+r+')')+'\n\n'
    text+='''theorem database_bound : CNFClauseTrace.emittedDatabase? trace = some (databaseOfClauses TypedCNFRefutation.original.toList) := by
  simp only [CNFClauseTrace.emittedDatabase?, clauses_bound, Option.map_some]
'''
    outputs.append(save('Checks',text))
    stage.finish(47, {'segments': len(segments), 'gates': len(gates),
                      'gate_clause_endpoints': gate_ends})
