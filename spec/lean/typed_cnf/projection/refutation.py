"""Exact depth-six supplied-LRAT consequence source construction."""
import hashlib
from common import require
ctx = None
MAX_ID = 65536
CHUNK = 100
CNF_HASH = 'ca659ecd4ed22d4e5d461edb10999857acfb6a008572baee77d0bd35cacb962a'
PROOF_HASH = '3d189c4e459438315c2bef4485ae81dda1ad4c2e931a5ff6879c910fcbde66c4'

def charge(amount=1):
    ctx.charge(amount)

def save(name, text):
    return ctx.save('TypedCNFRefutation.' + name[:-5], text)

def tokens(line):
    values=line.split();charge(len(values));return values

def number(token):
    if not token or token in ('+','-') or (token[0]=='+' or any(c not in '0123456789' for c in token.lstrip('-'))):
        raise RuntimeError('integer syntax')
    value=int(token)
    if abs(value)>MAX_ID: raise RuntimeError('integer cap')
    return value

def read_formula(text):
    header=None;clauses=[];clause=[]
    for line in text.splitlines():
        fields=tokens(line)
        if not fields or fields[0]=='c': continue
        if fields[0]=='p':
            if header is not None or clauses or clause or len(fields)!=4 or fields[1]!='cnf': raise RuntimeError('header')
            header=(number(fields[2]),number(fields[3]));continue
        if header is None: raise RuntimeError('missing header')
        for token in fields:
            value=number(token)
            if value==0: clauses.append(clause);clause=[]
            elif abs(value)>header[0]: raise RuntimeError('literal range')
            else: clause.append(value)
    if header!=(2890,10352) or clause or len(clauses)!=header[1]: raise RuntimeError('formula inventory')
    return clauses

def read_proof(text,clauses):
    known={i+1:clause for i,clause in enumerate(clauses)}
    live=set(known);last=len(clauses);additions=[];deletions=0;empty=None
    for line in text.splitlines():
        fields=tokens(line)
        if not fields or fields[0]=='c':continue
        ident=number(fields[0])
        if ident<=0:raise RuntimeError('proof ID')
        if len(fields)>1 and fields[1]=='d':
            if ident<last or fields[-1]!='0':raise RuntimeError('deletion record')
            for token in fields[2:-1]:
                deleted=number(token)
                if deleted<=0:raise RuntimeError('deletion ID')
                if deleted not in live:raise RuntimeError('deleting nonlive clause')
                live.remove(deleted);deletions+=1
            continue
        if ident<=last or ident in known:raise RuntimeError('ID reuse or nonincreasing addition')
        body=[number(token) for token in fields[1:]]
        if body.count(0)!=2 or not body or body[-1]!=0:raise RuntimeError('addition delimiters')
        delimiter=body.index(0);clause=body[:delimiter];hints=body[delimiter+1:-1]
        if any(abs(value)>2890 for value in clause):raise RuntimeError('proof literal range')
        if any(hint<=0 or hint not in live or hint not in known for hint in hints):raise RuntimeError('forward/deleted/missing hint')
        charge(len(clause)+len(hints))
        additions.append((ident,clause,hints));known[ident]=clause;live.add(ident);last=ident
        if not clause:empty=ident
    if len(additions)!=5409 or deletions!=6163 or empty is None:raise RuntimeError('proof inventory')
    return additions,deletions,empty

def literal(value):return '⟨%d, %s⟩'%(abs(value),'true' if value>0 else 'false')
def clause(value):return '['+', '.join(map(literal,value))+']'

def project(stage):
    global ctx
    ctx = stage
    fixture = stage.repo / 'asm' / 'testdata' / 'typed_cnf'
    formula = stage.read_file(fixture / 'raw.cnf', CNF_HASH, 164134).decode('ascii')
    proof = stage.read_file(fixture / 'raw.lrat', PROOF_HASH, 478063).decode('ascii')
    clauses=read_formula(formula);additions,deletions,empty=read_proof(proof,clauses)
    header='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace TypedCNFRefutation\nopen Oak.RupCheck Oak.TseitinCNF Oak.CNFSuppliedRefutation\n\n'
    # Factor at exactly depth six of the original balanced tree.  The tuple
    # boundaries and path prefixes come from that same midpoint recursion.
    blocks=[]
    def top_tree(first,last,path):
        if len(path)==6:
            ident=len(blocks);blocks.append((ident,first,last,path))
            return 'block%02d'%ident
        middle=(first+last)//2
        return '(Original.branch %s %s)'%(top_tree(first,middle,path+[False]),top_tree(middle+1,last,path+[True]))
    top=top_tree(1,len(clauses),[])
    if len(blocks)!=64 or any(last-first+1 not in (161,162) for _,first,last,_ in blocks):
        raise RuntimeError('fixed subtree inventory')
    local_paths={}
    owners={}
    def local_tree(first,last,path,owner):
        if first==last:
            local_paths[first]=path;owners[first]=owner
            return '(Original.leaf c%d)'%first
        middle=(first+last)//2
        return '(Original.branch %s %s)'%(local_tree(first,middle,path+[False],owner),local_tree(middle+1,last,path+[True],owner))
    records=[]
    for pair in range(32):
        group=blocks[2*pair:2*pair+2]
        first,last=group[0][1],group[1][2]
        if last-first+1>324:raise RuntimeError('clause module inventory')
        source=['import Oak.CNFSuppliedRefutation\n\n',header]
        for ident in range(first,last+1):
            source.append('def c%d : Clause := %s\n'%(ident,clause(clauses[ident-1])))
        for owner,first,last,_ in group:
            source.append('def block%02d : Original := %s\n'%(owner,local_tree(first,last,[],owner)))
        source.append('\nend TypedCNFRefutation\n')
        records.append(save('Clauses%02d.lean'%pair,''.join(source)))
    if sorted(owners)!=list(range(1,len(clauses)+1)):
        raise RuntimeError('original ID coverage')
    source=['import Oak.CNFSuppliedSubtree\n']
    source.extend('import TypedCNFRefutation.Clauses%02d\n'%pair for pair in range(32))
    source.extend(['\n',header,'','def original : Original := '+top+'\n'])
    for owner,_,_,path in blocks:
        witness='(Original.Subtree.refl block%02d)'%owner
        for bit in reversed(path):
            witness='(Original.Subtree.%s %s)'%('right' if bit else 'left',witness)
        source.append('theorem subtree%02d : Original.Subtree original block%02d := %s\n'%(owner,owner,witness))
    source.append('\nend TypedCNFRefutation\n')
    records.append(save('Top.lean',''.join(source)))
    used_original=sorted({hint for _,_,hints in additions for hint in hints if hint<=len(clauses)})
    if len(used_original)!=7160:raise RuntimeError('original hint inventory')
    for offset in range(0,len(used_original),100):
        source=['import TypedCNFRefutation.Top\n\n',header,'']
        for ident in used_original[offset:offset+100]:
            owner=owners[ident]
            path='['+', '.join('true' if bit else 'false' for bit in local_paths[ident])+']'
            source.append('theorem base%d : Consequence original.toList c%d :=\n  subtree%02d.lift_consequence (original_consequence block%02d %s c%d (by decide))\n'%(ident,ident,owner,owner,path,ident))
        source.append('\nend TypedCNFRefutation\n')
        records.append(save('Base%02d.lean'%(offset//100),''.join(source)))
    records.append(save('Original.lean',''.join('import TypedCNFRefutation.Base%02d\n'%i for i in range(72))))
    previous='Original'
    for offset in range(0,len(additions),CHUNK):
        chunk=additions[offset:offset+CHUNK];name='Chunk%02d'%(offset//CHUNK)
        source=['import TypedCNFRefutation.%s\n\n'%previous,header]
        for ident,value,hints in chunk:
            source.append('def c%d : Clause := %s\n'%(ident,clause(value)))
            names=', '.join('c%d'%hint for hint in hints)
            source.append('theorem consequence%d : Consequence original.toList c%d :=\n  checked_addition (hints := [%s]) (by decide)\n    '%(ident,ident,names))
            for hint in hints:
                premise='base%d'%hint if hint<=len(clauses) else 'consequence%d'%hint
                source.append('(HintConsequences.cons %s '%premise)
            source.append('HintConsequences.nil'+')'*len(hints)+'\n')
        source.append('\nend TypedCNFRefutation\n');records.append(save(name+'.lean',''.join(source)));previous=name
    finish='import TypedCNFRefutation.%s\n\n'%previous+header+'theorem exact_cnf_unsatisfiable : Unsatisfiable (databaseOfClauses original.toList) :=\n  empty_refutes consequence%d\n\nend TypedCNFRefutation\n'%empty
    records.append(save('Final.lean',finish))
    require(empty == 15761, 'final empty addition identity')
    stage.finish(162, {'clauses': 10352, 'additions': len(additions),
                       'deletions': deletions, 'empty_id': empty,
                       'base_proofs': len(used_original), 'subtrees': 64})
