"""Versioned typed finite fragment; native Oak is the default frontend.
The experimental parser is retained explicitly for offline differential tests.
"""
import hashlib
import itertools
import json
import math
from pathlib import Path
import re
import subprocess
from circuit import Circuit

FORMAT = 'oak-finite-1'
ROOT = Path(__file__).resolve().parent


def need(ok, why):
    if not ok:
        raise ValueError(why)


class Reader:
    def __init__(self, source):
        self.tokens = []
        pos = 0
        token = re.compile(r'\s+|//[^\n]*|->|=>|&&|\|\||==|!=|<=|>=|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[{}():=,.!?|+<>-]')
        while pos < len(source):
            m = token.match(source, pos)
            need(m is not None, f'unsupported source near offset {pos}')
            value = m.group(); pos = m.end()
            if not value.isspace() and not value.startswith('//'):
                self.tokens.append(value)
        self.tokens.append('<end>'); self.i = 0

    def peek(self):
        return self.tokens[self.i]

    def take(self, expected=None):
        value = self.peek()
        need(value != '<end>' and (expected is None or value == expected), f'expected {expected}, got {value}')
        self.i += 1
        return value

    def ident(self):
        value = self.take()
        need(re.fullmatch('[A-Za-z_][A-Za-z_0-9]*', value) and value not in ('true','false','type','Bool','u8'), 'expected name')
        return value

    def expr(self, minimum=0):
        if self.peek() == '!':
            self.take(); left = ['!', self.expr(6)]
        elif self.peek() == '(':
            self.take(); left = self.expr(); self.take(')')
        elif self.peek() in ('true', 'false'):
            left = ['bool', self.take() == 'true']
        elif self.peek().isdigit():
            left = ['integer', int(self.take())]
        else:
            name = self.take()
            need(re.fullmatch('[A-Za-z_][A-Za-z_0-9]*', name), 'expected expression name')
            if self.peek() == '.':
                self.take(); left = ['member', name, self.ident()]
            elif self.peek() == '(':
                self.take(); args = []
                while self.peek() != ')':
                    args.append(self.expr())
                    if self.peek() != ',': break
                    self.take()
                self.take(')'); left = ['call', name, args]
            else: left = ['ref', name]
        precedence = {'||':1, '&&':2, '==':3, '!=':3, '<':4, '>':4, '<=':4, '>=':4, '+':5, '-':5}
        while self.peek() in precedence and precedence[self.peek()] >= minimum:
            op = self.take(); left = [op, left, self.expr(precedence[op]+1)]
        if minimum == 0 and self.peek() == '?':
            self.take(); self.take('{'); arms = []
            while self.peek() == '|':
                self.take(); token = self.take()
                if token == '_': pattern = ['wildcard']
                elif token in ('true','false'): pattern = ['bool',token=='true']
                elif token.isdigit(): pattern = ['integer',int(token)]
                else:
                    self.take('.'); pattern = ['member',token,self.ident()]
                self.take('=>'); arms.append([pattern,self.expr()])
            self.take('}'); left = ['match',left,arms]
        return left

    def document(self):
        doc = {'format': FORMAT, 'state':'', 'fields':[], 'enums':{}, 'functions':{}}
        names = set()
        while self.peek() != '<end>':
            name = self.ident(); need(name not in names, 'duplicate declaration'); names.add(name)
            self.take(':')
            if self.peek() == 'type':
                self.take(); self.take('=')
                if self.peek() == '|':
                    cases = []
                    while self.peek() == '|':
                        self.take(); cases.append(self.ident())
                    doc['enums'][name] = cases
                else:
                    need(not doc['state'], 'one record supported'); doc['state'] = name
                    self.take('{')
                    while self.peek() != '}':
                        field = self.ident(); self.take(':'); typ = self.take()
                        doc['fields'].append([field, typ])
                        if self.peek() == ',': self.take()
                    self.take('}')
            else:
                self.take('('); params = []
                while self.peek() != ')':
                    p = self.ident(); self.take(':'); typ = self.take()
                    need(typ == doc['state'], 'predicate arguments must be the state record'); params.append(p)
                    if self.peek() != ',': break
                    self.take()
                self.take(')'); need(self.take() in (':','->'), 'expected return type'); self.take('Bool'); self.take('=')
                doc['functions'][name] = {'params':params, 'body':self.expr()}
        return doc


class Model:
    def __init__(self, doc, config):
        need(doc.get('format') == FORMAT, 'unsupported frontend format')
        self.arithmetic = config.get('arithmetic')
        need(self.arithmetic in (None,'u8-wrap'), 'unsupported arithmetic profile')
        self.doc = doc; self.state = doc['state']; self.enums = doc['enums']; self.functions = doc['functions']
        need(self.state and self.state not in self.enums, 'invalid state type')
        need(len(doc['fields']) == len({x[0] for x in doc['fields']}), 'duplicate field')
        self.fields = dict(doc['fields'])
        need(1 <= len(self.fields) <= 6, 'one to six fields required')
        for name, cases in self.enums.items():
            need(name not in ('Bool','u8') and 1 <= len(cases) <= 16 and len(cases) == len(set(cases)), 'invalid enum')
        for typ in self.fields.values(): need(typ in ('Bool','u8') or typ in self.enums, 'unsupported field type')
        need(sum(self.width(t) for t in self.fields.values()) <= 16, 'prototype limit: 16 state bits')
        for role, arity in (('initial',1),('invariant',1),('step',2)):
            need(config[role] in self.functions and len(self.functions[config[role]]['params']) == arity, 'invalid role signature')
        # Resolve and type check all definitions, not just reachable roles.
        for name in self.functions:
            self.expand(name, [f'p{i}' for i in range(len(self.functions[name]['params']))], [])
        self.terms = {role:self.expand(config[role], ['s','t'][:arity], [])[0] for role, arity in (('initial',1),('invariant',1),('step',2))}

    def width(self, typ):
        return 1 if typ == 'Bool' else 8 if typ == 'u8' else max(1, (len(self.enums[typ])-1).bit_length())

    def domain(self, typ):
        return [False, True] if typ == 'Bool' else range(256) if typ == 'u8' else self.enums[typ]

    def states(self, limit=1024):
        size = math.prod(len(self.domain(t)) for t in self.fields.values())
        need(size <= limit, f'finite enumeration exceeds {limit} states; use symbolic backend')
        return [dict(zip(self.fields, values)) for values in itertools.product(*(self.domain(t) for t in self.fields.values()))]

    def valid_state(self, value):
        need(type(value) is dict and set(value) == set(self.fields), 'state field mismatch')
        for f, typ in self.fields.items():
            v = value[f]
            need((type(v) is bool if typ == 'Bool' else type(v) is int and 0 <= v < 256 if typ == 'u8' else type(v) is str and v in self.enums[typ]), f'invalid value for {f}')

    def expand(self, name, arguments, active):
        need(name in self.functions and name not in active, 'unknown or recursive function')
        fn = self.functions[name]; params = fn['params']
        need(len(params) == len(set(params)) and len(params) == len(arguments), 'invalid parameters')
        need(not set(params).intersection(self.functions) and not set(params).intersection(self.enums), 'shadowed declaration unsupported')
        env = dict(zip(params, arguments))
        def walk(e):
            need(type(e) in (list,tuple) and len(e)>0, 'invalid frontend node')
            op = e[0]
            if op == 'bool':
                need(len(e)==2 and type(e[1]) is bool, 'invalid Boolean'); return ['bool',e[1]], 'Bool'
            if op == 'member':
                need(len(e)==3, 'invalid member')
                if e[1] in env:
                    need(e[2] in self.fields, 'unknown state field'); return ['var',env[e[1]],e[2],self.fields[e[2]]], self.fields[e[2]]
                need(e[1] in self.enums and e[2] in self.enums[e[1]], 'unknown enum constructor')
                return ['enum',e[1],e[2]], e[1]
            if op == 'call':
                need(len(e)==3 and type(e[2]) is list, 'invalid call')
                if e[1] == 'u8':
                    need(len(e[2])==1 and e[2][0][0]=='integer' and type(e[2][0][1]) is int and 0<=e[2][0][1]<256, 'u8 requires a literal in 0..255')
                    return ['byte',e[2][0][1]], 'u8'
                args=[]
                for a in e[2]:
                    need(len(a)==2 and a[0]=='ref' and a[1] in env, 'state reference expected')
                    args.append(env[a[1]])
                return self.expand(e[1],args,active+[name])
            if op == 'match':
                need(len(e)==3 and type(e[2]) is list and len(e[2])>0, 'invalid match')
                scrutinee,st=walk(e[1]); seen=set(); arms=[]; default=None; result_type=None
                for index,(pattern,body) in enumerate(e[2]):
                    node,bt=walk(body)
                    need(result_type is None or result_type==bt, 'match result type mismatch'); result_type=bt
                    if pattern==['wildcard']:
                        need(index==len(e[2])-1,'wildcard must be last'); default=node; continue
                    if pattern[0]=='integer':
                        need(st=='u8' and type(pattern[1]) is int and 0<=pattern[1]<256,'invalid integer pattern')
                        pat=['byte',pattern[1]]; pt='u8'; key=pattern[1]
                    else:
                        pat,pt=walk(pattern); key=pat[-1]
                        need(pat[0] in ('bool','enum'),'nonconstant pattern')
                    need(st==pt and key not in seen,'duplicate or mismatched pattern');seen.add(key)
                    arms.append((['==',scrutinee,pat],node))
                if default is None:
                    need(seen==set(self.domain(st)),'nonexhaustive match')
                    default=arms.pop()[1]
                for condition,node in reversed(arms): default=['ite',condition,node,default]
                return default,result_type
            arities={'!':1,'&&':2,'||':2,'==':2,'!=':2,'+':2,'-':2,'<':2,'>':2,'<=':2,'>=':2,'ite':3}
            need(op in arities and len(e)==arities[op]+1,'unsupported expression')
            children=[walk(x) for x in e[1:]]; nodes=[x[0] for x in children]; types=[x[1] for x in children]
            if op in ('!','&&','||'): need(all(t=='Bool' for t in types),'Boolean operator type mismatch'); typ='Bool'
            elif op == 'ite': need(types[0]=='Bool' and types[1]==types[2], 'match type mismatch'); typ=types[1]
            elif op in ('==','!='): need(types[0]==types[1], 'nominal equality type mismatch'); typ='Bool'
            else:
                need(types==['u8','u8'], 'arithmetic requires explicit u8 operands')
                if op in ('+','-'): need(self.arithmetic=='u8-wrap', 'machine arithmetic requires explicit experimental arithmetic: u8-wrap')
                typ='u8' if op in ('+','-') else 'Bool'
            return [op,*nodes],typ
        value,typ=walk(fn['body']); need(typ=='Bool','predicate must return Bool'); return value,typ


def value(e, states):
    op=e[0]
    if op in ('bool','byte'): return e[1]
    if op=='enum': return e[1]+'.'+e[2]
    if op=='var':
        result=states[e[1]][e[2]]
        return result if e[3] in ('Bool','u8') else e[3]+'.'+result
    if op=='!': return not value(e[1],states)
    if op=='ite': return value(e[2] if value(e[1],states) else e[3],states)
    a=value(e[1],states); b=value(e[2],states)
    if op=='&&': return a and b
    if op=='||': return a or b
    if op=='+': return (a+b)%256
    if op=='-': return (a-b)%256
    return {'==':lambda:a==b,'!=':lambda:a!=b,'<':lambda:a<b,'>':lambda:a>b,'<=':lambda:a<=b,'>=':lambda:a>=b}[op]()


def rename(e, p):
    if e[0]=='var': return ['var',p,e[2],e[3]]
    if e[0] in ('bool','byte','enum'): return e
    return [e[0],*(rename(x,p) for x in e[1:])]


def load(path, frontend='oak', timeout=60):
    path=Path(path).resolve(); config=json.loads(path.read_text())
    need({'source','initial','step','invariant'} <= set(config) <= {'source','initial','step','invariant','arithmetic'} and all(type(x) is str for x in config.values()),'invalid project')
    source_path=(path.parent/config['source']).resolve(); need(source_path.is_relative_to(path.parent),'source must remain inside project directory')
    source=source_path.read_text(); source_hash=hashlib.sha256(source.encode()).hexdigest()
    if frontend=='experimental': doc=Reader(source).document()
    else:
        need(frontend=='oak','unknown frontend')
        command=['go','run','.',str(source_path)]
        run=subprocess.run(command,cwd=ROOT/'frontend',capture_output=True,text=True,timeout=timeout)
        need(run.returncode==0, f'Oak frontend failed: {run.stderr}')
        doc=json.loads(run.stdout)
        need(doc.get('source_sha256')==source_hash,'frontend source digest mismatch')
        doc.pop('source_sha256')
    model=Model(doc,config)
    identity={'format':FORMAT,'source_sha256':source_hash,'config':config,'frontend':frontend,'model':doc,'semantics':'u8-wrap-enum-nominal-safety-v1'}
    model.digest=hashlib.sha256(json.dumps(identity,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    model.frontend=frontend
    return model


def encode(model, role):
    c=Circuit()
    def bits(e):
        op=e[0]
        if op=='bool': return c.constant(int(e[1]),1)
        if op=='byte': return c.constant(e[1],8)
        if op=='enum': return c.constant(model.enums[e[1]].index(e[2]),model.width(e[1]))
        if op=='var': return [c.input(f'{e[1]}.{e[2]}.{i}') for i in range(model.width(e[3]))]
        a=bits(e[1])
        if op=='!': return [-a[0]]
        b=bits(e[2])
        if op=='ite':
            d=bits(e[3]); return [c.or_(c.and_(a[0],x),c.and_(-a[0],y)) for x,y in zip(b,d)]
        if op=='&&': return [c.and_(a[0],b[0])]
        if op=='||': return [c.or_(a[0],b[0])]
        if op=='+': return c.add(a,b)
        if op=='-': return c.add(c.add(a,[-x for x in b]),c.constant(1,8))
        if op=='==': return [c.equal(a,b)]
        if op=='!=': return [-c.equal(a,b)]
        if op=='<': return [c.less(a,b)]
        if op=='>': return [c.less(b,a)]
        if op=='<=': return [-c.less(b,a)]
        if op=='>=': return [-c.less(a,b)]
        raise ValueError('unsupported encoded operator')
    def domain(p):
        guards=[]
        for field,typ in model.fields.items():
            v=bits(['var',p,field,typ])
            if typ in model.enums and len(model.enums[typ]) < 2**len(v):
                guards.append(c.less(v,c.constant(len(model.enums[typ]),len(v))))
        return c.and_(*guards)
    t=model.terms
    if role=='initial': root=c.and_(domain('s'),bits(t['initial'])[0])
    elif role=='base': root=c.and_(domain('s'),bits(t['initial'])[0],-bits(t['invariant'])[0])
    elif role=='step': root=c.and_(domain('s'),domain('t'),bits(t['invariant'])[0],bits(t['step'])[0],-bits(rename(t['invariant'],'t'))[0])
    else: raise ValueError('unknown obligation')
    return c,root
