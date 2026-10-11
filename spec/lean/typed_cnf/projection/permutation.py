"""Exact direct 23-step allocation output-permutation witness."""
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

def balanced(items,operator=None):
    charge(1)
    if not items:refuse('empty append')
    if len(items)==1:return items[0]
    middle=len(items)//2
    left,right=balanced(items[:middle],operator),balanced(items[middle:],operator)
    return '('+left+' ++ '+right+')' if operator is None else operator(left,right)

def literal(values):
    charge(len(values));return '['+', '.join(str(value) for value in values)+']'

def project(stage):
    global ctx
    ctx = stage
    blocks=[]
    for family,count,modules,fields in [('Input',3,1,2),('Gate',20,5,5)]:
        found={}
        for module in range(modules):
            raw=stage.source('data', 'TypedCNFInstance.%sData%02d'%(family,module))
            for line in raw.decode().splitlines():
                match=re.fullmatch(r'def (typed'+family+r'Block([0-9]{3})) : .* := (\[.*\])',line)
                if not match:continue
                if int(match[2]) in found:refuse('duplicate block')
                tuples=re.findall(r'⟨([^⟩]+)⟩',match[3]);entries=[]
                for entry in tuples:
                    numbers=entry.split(', ')
                    if len(numbers)!=fields or any(re.fullmatch(r'0|[1-9][0-9]*',value) is None for value in numbers):refuse('record grammar')
                    values=[int(value) for value in numbers]
                    if any(value>100000 for value in values):refuse('record natural bound')
                    entries.append(values)
                rebuilt='['+', '.join('⟨'+', '.join(str(value) for value in row)+'⟩' for row in entries)+']'
                charge(len(match[3])+len(entries))
                if rebuilt!=match[3]:refuse('literal record reconstruction')
                found[int(match[2])]=(match[1],[row[-1] for row in entries])
        if set(found)!=set(range(count)):refuse('block inventory')
        for index in range(count):
            name,values=found[index]
            expected=min(128,(353 if family=='Input' else 2537)-128*index)
            if len(values)!=expected:refuse('block cardinality')
            blocks.append((family,index,name,values))
    if len(blocks)!=23:refuse('chunk inventory')
    remaining=list(range(1,2891));ranks=[];remainders=[remaining[:]];statistics=[]
    for number,(family,index,name,values) in enumerate(blocks):
        before=len(remaining);positions=[]
        for value in values:
            if family=='Gate':
                charge(1)
                if not remaining or remaining[0]!=value:refuse('gate is not the next remaining value')
                position=0
            else:
                charge(len(remaining))
                try:position=remaining.index(value)
                except ValueError:refuse('input output missing from remaining range')
            charge(len(remaining))
            if remaining.pop(position)!=value:refuse('extraction simulation')
            positions.append(position)
        ranks.append(positions);remainders.append(remaining[:]);charge(len(remaining))
        statistics.append({'chunk':number,'family':family,'block':index,'entries':len(values),'before':before,'after':len(remaining),'maximum_index':max(positions),'extraction_steps':sum(position+1 for position in positions)})
    if remaining or sum(row['extraction_steps'] for row in statistics)!=268028:refuse('final empty remainder/work identity')
    if [statistics[i]['maximum_index'] for i in range(3)]!=[1998,1890,1773]:refuse('input position maxima')
    gate_maps=['(typedGateBlock%03d.map EncodedGate.out)'%i for i in range(20)]
    gate_values=[value for family,index,name,values in blocks if family=='Gate' for value in values]
    if remainders[3]!=gate_values:refuse('third remainder differs from exact gate-output list')
    for number in range(3,24):
        expected=[value for _,_,_,values in blocks[number:] for value in values]
        charge(len(expected))
        if remainders[number]!=expected:refuse('remaining gate block order')
    original=stage.source('checks', 'TypedCNFInstance.CheckShape').decode()
    old_line='  have outputShape := outputs_shape_of_sorted (snapshot := allocation) (by decide)\n'
    if original.count(old_line)!=1:refuse('original Shape proof boundary')
    text=original.replace('import Oak.CNFCheckComposition\n','import Oak.CNFCheckComposition\nimport Oak.CNFOutputPermutation\n',1)
    text=text.replace('open Oak.CNFCheckComposition\n','open Oak.CNFCheckComposition\nopen Oak.CNFOutputPermutation\n',1)
    text=text.replace(old_line,'  have outputShape := outputs_shape_of_perm output_permutation\n',1)
    prefix=''
    for number in range(24):
        if number==0:expression="List.range' 1 2890"
        elif number<3:expression=literal(remainders[number])
        elif number==23:expression='[]'
        else:expression=balanced(gate_maps[number-3:])
        prefix+='def outputRemaining%02d : List Nat := %s\n'%(number,expression)
    prefix+='\n'
    for number,(family,index,name,values) in enumerate(blocks):
        accessor='InputAllocation.output' if family=='Input' else 'EncodedGate.out'
        prefix+='def outputValues%02d : List Nat := %s.map %s\n'%(number,name,accessor)
        prefix+='def outputIndices%02d : List Nat := %s\n'%(number,literal(ranks[number]))
        prefix+='theorem outputExtract%02d : extractValues outputValues%02d outputIndices%02d outputRemaining%02d = some outputRemaining%02d := by decide\n'%(number,number,number,number,number+1)
        prefix+='theorem outputPerm%02d : (outputValues%02d ++ outputRemaining%02d).Perm outputRemaining%02d := extractValues_perm outputExtract%02d\n\n'%(number,number,number+1,number,number)
    prefix+="theorem output_permutation : (outputs allocation).Perm (List.range' 1 allocation.variables) := by\n"
    prefix+='  have complete := '+balanced(['outputPerm%02d'%i for i in range(23)],lambda l,r:'(perm_chain '+l+' '+r+')')+'\n'
    mapped_inputs='('+balanced(['typedInputBlock%03d'%i for i in range(3)])+').map InputAllocation.output'
    mapped_gates='('+balanced(['typedGateBlock%03d'%i for i in range(20)])+').map EncodedGate.out'
    prefix+="  change (%s ++ %s).Perm (List.range' 1 2890)\n"%(mapped_inputs,mapped_gates)
    prefix+='  simpa only ['+', '.join('outputValues%02d'%i for i in range(23))+', outputRemaining00, outputRemaining23, List.append_nil, List.map_append, List.append_assoc] using complete\n\n'
    marker='theorem allocation_shape : Shape allocation := by\n'
    if text.count(marker)!=1:refuse('allocation_shape declaration boundary')
    text=text.replace(marker,prefix+marker,1)
    stage.save('TypedCNFInstance.CheckShape', text)
    stage.finish(1, {'chunks': 23, 'extraction_steps': 268028,
                     'final_remainder_length': 0})
