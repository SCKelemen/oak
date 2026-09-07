"""Untrusted external trace decoders. Every imported trace is replayed by verify.
Receipts detect accidental stale inputs; hashes do not authenticate a solver.
"""
import json
import re
from circuit import digest
from finite_model import need, value
from verify import FORMAT, verify


def sexprs(text):
    tokens=re.findall(r'\(|\)|[^\s()]+',text); pos=0
    def read(depth=0):
        nonlocal pos
        need(pos<len(tokens) and depth<128,'invalid S-expression')
        token=tokens[pos];pos+=1
        if token=='(':
            result=[]
            while pos<len(tokens) and tokens[pos]!=')': result.append(read(depth+1))
            need(pos<len(tokens),'unterminated S-expression');pos+=1;return result
        need(token!=')','unexpected closing parenthesis');return token
    result=[]
    while pos<len(tokens): result.append(read())
    return result


def smt_value(model,typ,raw):
    if typ=='Bool':
        need(raw in ('true','false'),'expected SMT Boolean');return raw=='true'
    width=model.width(typ)
    if type(raw) is str and re.fullmatch(r'#b[01]+',raw):
        need(len(raw)-2==width,'bit-vector width mismatch');number=int(raw[2:],2)
    elif type(raw) is str and re.fullmatch(r'#x[0-9a-fA-F]+',raw):
        need((len(raw)-2)*4==width,'bit-vector width mismatch');number=int(raw[2:],16)
    else:
        need(type(raw) is list and len(raw)==3 and raw[0]=='_' and re.fullmatch(r'bv[0-9]+',raw[1]) and raw[2]==str(width),'invalid SMT bit-vector')
        number=int(raw[1][2:]);need(number<2**width,'bit-vector out of range')
    if typ=='u8': return number
    need(number<len(model.enums[typ]),'unused enum encoding');return model.enums[typ][number]


def from_z3(model,text,bound):
    expressions=sexprs(text)
    need(len(expressions)==2 and expressions[0]=='sat' and type(expressions[1]) is list,'expected sat and one get-value result')
    values={}
    for pair in expressions[1]:
        need(type(pair) is list and len(pair)==2 and type(pair[0]) is str and pair[0] not in values,'invalid/duplicate SMT value');values[pair[0]]=pair[1]
    names={f's{i}_f_{f}' for i in range(bound+1) for f in model.fields}
    need(set(values)==names,'SMT values do not match BMC variables')
    return [{f:smt_value(model,t,values[f's{i}_f_{f}']) for f,t in model.fields.items()} for i in range(bound+1)]


def from_tlc(model,text):
    # TLC v1.8.0 _JsonTrace: a set of <<level, record-of-spec-variables>>.
    def unique(pairs):
        result={}
        for k,v in pairs:
            need(k not in result,'duplicate JSON key');result[k]=v
        return result
    raw=json.loads(text,object_pairs_hook=unique)
    need(type(raw) is dict and raw.get('vars')==['state'],'unexpected TLC variable set')
    graph=raw.get('counterexample');need(type(graph) is dict,'missing TLC counterexample')
    entries=graph.get('state');need(type(entries) is list and 0<len(entries)<=4096,'invalid TLC trace states')
    levels={}
    for entry in entries:
        need(type(entry) is list and len(entry)==2 and type(entry[0]) is int and entry[0]>0 and entry[0] not in levels,'invalid/duplicate TLC level')
        record=entry[1];need(type(record) is dict and set(record)=={'state'},'unexpected TLC state variables')
        fields=record['state'];need(type(fields) is dict and set(fields)=={'f_'+f for f in model.fields},'TLC fields mismatch')
        state={}
        for f,t in model.fields.items():
            v=fields['f_'+f]
            if t in model.enums:
                need(type(v) is str and v.startswith(t+'.'),'nominal enum mismatch');v=v[len(t)+1:]
            state[f]=v
        model.valid_state(state);levels[entry[0]]=state
    need(set(levels)==set(range(1,len(levels)+1)),'noncontiguous TLC trace')
    return [levels[i] for i in range(1,len(levels)+1)]


def receipt(model,backend,query,raw,bound=None):
    return {'format':'oak-trace-receipt-1','semantic_digest':model.digest,'backend':backend,'query_sha256':digest(query),'output_sha256':digest(raw),'bound':bound}


def import_trace(model,backend,query,raw,record,bound=None):
    need(record==receipt(model,backend,query,raw,bound),'stale/mismatched trace receipt')
    # Recompute the exact projection; a receipt alone is not a semantic check.
    if backend=='z3':
        from projections import bmc
        need(type(bound) is int and query==bmc(model,bound,True),'wrong BMC query')
        states=from_z3(model,raw,bound)
    elif backend=='tlc':
        import tempfile
        from pathlib import Path
        from projections import emit
        with tempfile.TemporaryDirectory() as folder:
            emit(model,folder)
            expected=(Path(folder)/'Model.tla').read_text()+'\n'+(Path(folder)/'Model.cfg').read_text()
        need(bound is None and query==expected,'wrong TLC specification/configuration')
        states=from_tlc(model,raw)
    else: raise ValueError('unsupported trace backend')
    # BMC can continue after its first violation. Replay the whole candidate
    # first, then retain the shortest prefix ending at an unsafe state.
    for state in states: model.valid_state(state)
    need(value(model.terms['initial'],{'s':states[0]}),'invalid initial state')
    for s,t in zip(states,states[1:]): need(s==t or value(model.terms['step'],{'s':s,'t':t}),'illegal transition')
    end=next((i for i,s in enumerate(states) if not value(model.terms['invariant'],{'s':s})),None)
    need(end is not None,'no safety violation')
    cert={'format':FORMAT,'semantic_digest':model.digest,'kind':'trace','states':states[:end+1]}
    verify(model,cert)
    return cert
