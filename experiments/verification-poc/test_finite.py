import copy
import itertools
import json
from pathlib import Path
import random
import shutil
import tempfile
import unittest
from unittest.mock import patch
from circuit import Circuit,digest
from finite_model import ROOT,Reader,Model,load,encode,value,rename
from finite import local_proof,trace
from import_trace import import_trace,receipt,from_z3,from_tlc
from projections import emit,bmc,term
from verify import verify
from local_lrat import prove
import lrat
import backend_suite


def model(name): return load(ROOT/f'examples/native/{name}.json','experimental')
def holds(clauses,assignment): return all(any(assignment[abs(x)]==(x>0) for x in c) for c in clauses)


class CircuitTests(unittest.TestCase):
    def test_gate_equivalences_including_aliases_constants_and_polarities(self):
        for op in ('and','or','xor'):
            for ix,iy in itertools.product(range(6),repeat=2):
                c=Circuit();x=c.input('x');y=c.input('y');ls=[x,-x,y,-y,c.one,-c.one];root=c.gate(op,ls[ix],ls[iy])
                for bits in itertools.product((False,True),repeat=c.count):
                    env=dict(enumerate(bits,1))
                    if not env[c.one]: continue
                    a=env[abs(ls[ix])]==(ls[ix]>0);b=env[abs(ls[iy])]==(ls[iy]>0)
                    expected=(a and b) if op=='and' else (a or b) if op=='or' else a!=b
                    self.assertEqual(holds(c.clauses,env),(env[abs(root)]==(root>0))==expected)

    def test_small_bitvectors_exhaustive(self):
        c=Circuit();a=[c.input('a'+str(i)) for i in range(4)];b=[c.input('b'+str(i)) for i in range(4)]
        add=c.add(a,b);less=c.less(a,b);eq=c.equal(a,b)
        for x,y in itertools.product(range(16),repeat=2):
            env=c.complete({p+str(i):bool(n&(1<<i)) for p,n in [('a',x),('b',y)] for i in range(4)})
            bit=lambda v:env[abs(v)]==(v>0)
            self.assertEqual(sum(bit(v)<<i for i,v in enumerate(add)),(x+y)%16)
            self.assertEqual(bit(less),x<y);self.assertEqual(bit(eq),x==y)
            self.assertTrue(holds(c.clauses,env))

    def test_u8_wrap_and_subtraction(self):
        c=Circuit();a=[c.input(str(i)) for i in range(8)];plus=c.add(a,c.constant(1,8));minus=c.add(a,c.constant(255,8))
        for x in range(256):
            env=c.complete({str(i):bool(x&(1<<i)) for i in range(8)})
            number=lambda bits:sum((env[abs(v)]==(v>0))<<i for i,v in enumerate(bits))
            self.assertEqual(number(plus),(x+1)%256);self.assertEqual(number(minus),(x-1)%256)

    def test_obligations_match_direct_semantics(self):
        for name in ('enum','enum-broken','counter','counter-broken','wrap'):
            m=model(name);states=m.states();states=states if len(states)<10 else [states[i] for i in (0,1,2,3,4,127,128,254,255)]
            for role in ('initial','base','step'):
                c,root=encode(m,role)
                for s,t in itertools.product(states,repeat=2):
                    envs={'s':s,'t':t};inputs={}
                    for key in c.inputs:
                        p,f,i=key.split('.');v=envs[p][f];typ=m.fields[f]
                        if typ in m.enums: v=m.enums[typ].index(v)
                        inputs[key]=bool(int(v)&(1<<int(i)))
                    env=c.complete(inputs)
                    actual=env[abs(root)]==(root>0)
                    ini=value(m.terms['initial'],envs);inv=value(m.terms['invariant'],envs)
                    expected=ini if role=='initial' else ini and not inv if role=='base' else inv and value(m.terms['step'],envs) and not value(rename(m.terms['invariant'],'t'),envs)
                    self.assertEqual(actual,expected,(name,role,s,t));self.assertTrue(holds(c.clauses,env))

    def test_smt_projection_matches_model(self):
        from import_trace import sexprs
        def evaluate(e,env):
            if type(e) is str: return e=='true' if e in ('true','false') else env[e]
            op=e[0]
            if op=='_': return (int(e[1][2:]),int(e[2]))
            args=[evaluate(x,env) for x in e[1:]]
            if op=='not': return not args[0]
            if op=='and': return all(args)
            if op=='or': return any(args)
            if op=='ite': return args[1] if args[0] else args[2]
            a,b=args
            if op=='=': return a==b
            if op=='distinct': return a!=b
            self.assertEqual(a[1],b[1]);x,y=a[0],b[0];width=a[1]
            if op=='bvadd': return ((x+y)%(1<<width),width)
            if op=='bvsub': return ((x-y)%(1<<width),width)
            return {'bvult':x<y,'bvugt':x>y,'bvule':x<=y,'bvuge':x>=y}[op]
        for name in ('enum','enum-broken','counter','counter-broken','wrap'):
            m=model(name);states=m.states();states=states if len(states)<10 else [states[i] for i in (0,1,2,3,4,127,128,254,255)]
            for role,e in m.terms.items():
                translated=sexprs(term(m,e,'smt'))[0]
                for s,t in itertools.product(states,repeat=2):
                    env={}
                    for p,state in [('s',s),('t',t)]:
                        for f,typ in m.fields.items():
                            v=state[f]
                            if typ in m.enums: v=m.enums[typ].index(v)
                            env[p+'_f_'+f]=v if typ=='Bool' else (v,m.width(typ))
                    self.assertEqual(evaluate(translated,env),value(e,{'s':s,'t':t}),(name,role,s,t))

    def test_unused_enum_encoding_is_excluded(self):
        source='''E: type = | A | B | C
State: type = { mode: E }
initial: (s: State): Bool = true
safe: (s: State): Bool = false
step: (s: State, t: State): Bool = true'''
        m=Model(Reader(source).document(),{'initial':'initial','invariant':'safe','step':'step'})
        c,root=encode(m,'base')
        for n in range(4):
            env=c.complete({key:bool(n&(1<<int(key.rsplit('.',1)[1]))) for key in c.inputs})
            self.assertEqual(env[abs(root)]==(root>0),n<3)


class LRATTests(unittest.TestCase):
    def test_small_cnf_refutations_against_exhaustive_truth(self):
        rng=random.Random(420)
        for _ in range(100):
            clauses=[rng.sample([1,-1,2,-2,3,-3],rng.randrange(4)) for _ in range(rng.randrange(1,9))]
            cnf=f'p cnf 3 {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)
            sat=any(holds(clauses,dict(enumerate(a,1))) for a in itertools.product((False,True),repeat=3))
            if sat:
                with self.assertRaises(ValueError): prove(cnf)
                with self.assertRaises(ValueError): lrat.check(cnf,f'{len(clauses)+1} 0 0\n')
            else: self.assertTrue(lrat.check(cnf,prove(cnf))['accepted'])

    def test_rejects_corrupt_hints_missing_empty_rat_and_deleted_references(self):
        cnf='p cnf 1 2\n1 0\n-1 0\n'
        self.assertTrue(lrat.check(cnf,'3 0 1 2 0\n')['accepted'])
        for bad in ('','3 0 0','3 0 1 0','3 0 1 9 0','3 0 -1 2 0','2 0 1 2 0','3 2 0 1 2 0','2 d 1 0\n3 0 1 2 0','3 0 1 2 2 0'):
            with self.assertRaises(ValueError): lrat.check(cnf,bad)
        self.assertTrue(lrat.check(cnf,'3 1 0 1 0\n3 d 1 0\n4 0 3 2 0')['accepted'])

    def test_source_bound_proofs_reconstruct_cnf(self):
        for name in ('enum','counter','wrap'):
            m=model(name);cert=local_proof(m);self.assertTrue(verify(m,cert)['accepted'])
            bad=copy.deepcopy(cert);bad['proofs']['step']['cnf_sha256']='0'*64
            with self.assertRaises(ValueError): verify(m,bad)
            bad=copy.deepcopy(cert);bad['proofs']['step']['lrat']=''
            with self.assertRaises(ValueError): verify(m,bad)
        with self.assertRaises(ValueError): verify(model('enum-broken'),local_proof(model('enum')))
        with self.assertRaises(ValueError): local_proof(model('enum-broken'))


class ModelTraceTests(unittest.TestCase):
    def test_boolean_reference_preserves_original_models(self):
        from project import load_project,evaluate
        for name in ('borrow','broken'):
            _,old,_=load_project(ROOT/f'examples/{name}.json')
            new=load(ROOT/f'examples/reference/{name}.json','experimental')
            for s,t in itertools.product(new.states(),repeat=2):
                for role in ('initial','step','invariant'):
                    self.assertEqual(evaluate(old[role],{'s':s,'t':t}),value(new.terms[role],{'s':s,'t':t}))

    def test_explicit_arithmetic_and_nominal_type_rejections(self):
        m=model('wrap');config={'initial':'initial','step':'step','invariant':'safe'}
        with self.assertRaisesRegex(ValueError,'explicit experimental arithmetic'): Model(m.doc,config)
        source=(ROOT/'examples/native/enum.oak').read_text().replace('| Phase.Conflict => t.phase == Phase.Conflict','')
        with self.assertRaisesRegex(ValueError,'nonexhaustive'): Model(Reader(source).document(),config)
        source=source.replace('s.phase == Phase.Idle','s.phase == u8(0)')
        with self.assertRaises(ValueError): Model(Reader(source).document(),config)

    def test_trace_replay_and_forgery_rejection(self):
        for name,length in [('enum-broken',3),('counter-broken',5)]:
            m=model(name);cert=trace(m);self.assertEqual(len(cert['states']),length);self.assertTrue(verify(m,cert)['accepted'])
            bad=copy.deepcopy(cert);bad['states']=[cert['states'][0],cert['states'][-1]]
            with self.assertRaises(ValueError): verify(m,bad)
        m=model('wrap')
        with self.assertRaises(ValueError): trace(m)
        for state in ({'count':True},{'count':256},{'count':-1},{'count':1,'extra':1}):
            with self.assertRaises(ValueError): m.valid_state(state)

    def test_synthetic_z3_import_and_stale_receipts(self):
        m=model('counter-broken');bound=5;query=bmc(m,bound,True)
        raw='sat\n('+ ' '.join(f'(s{i}_f_count #x{i:02x})' for i in range(bound+1))+')\n'
        record=receipt(m,'z3',query,raw,bound);cert=import_trace(m,'z3',query,raw,record,bound)
        self.assertEqual(cert['states'],[{'count':i} for i in range(5)])
        with self.assertRaises(ValueError): import_trace(m,'z3',query,raw+' ',record,bound)
        bad=raw.replace('#x02','#xff')
        with self.assertRaises(ValueError): import_trace(m,'z3',query,bad,receipt(m,'z3',query,bad,bound),bound)
        for bad in ('unknown',raw.replace('#x00','#b0'),raw.replace('s1_f_count','s0_f_count')):
            with self.assertRaises(ValueError): from_z3(m,bad,bound)

    def test_synthetic_tlc_import(self):
        m=model('enum-broken');states=trace(m)['states']
        raw=json.dumps({'vars':['state'],'counterexample':{'state':[[i+1,{'state':{'f_phase':'Phase.'+s['phase']}}] for i,s in enumerate(states)],'action':[]}})
        with tempfile.TemporaryDirectory() as out:
            emit(m,out);query=(Path(out)/'Model.tla').read_text()+'\n'+(Path(out)/'Model.cfg').read_text()
        cert=import_trace(m,'tlc',query,raw,receipt(m,'tlc',query,raw));self.assertEqual(cert['states'],states)
        bad=json.loads(raw);bad['counterexample']['state'][1][0]=1
        with self.assertRaises(ValueError): from_tlc(m,json.dumps(bad))
        with self.assertRaises(ValueError): from_tlc(m,raw.replace('Phase.Idle','Other.Idle'))

    def test_backend_never_accepts_unknown_missing_or_bad_exit(self):
        with patch('backend_suite.shutil.which',return_value=None):
            with self.assertRaises(ValueError): backend_suite.probe('z3',ROOT,1)
        for exit_code,stdout in [(0,'unknown\n'),(1,'sat\n'),(None,'')]:
            with patch('backend_suite.run',return_value={'exit_code':exit_code,'stdout':stdout,'stderr':''}):
                self.assertFalse(backend_suite.backend(model('enum'),'z3',ROOT,True,3,1,None)['passed'])

    @unittest.skipUnless(shutil.which('go'),'Go unavailable: native frontend integration not executed')
    def test_native_frontend_matches_reference(self):
        for name in ('enum','enum-broken','counter','counter-broken','wrap'):
            self.assertEqual(load(ROOT/f'examples/native/{name}.json','oak').doc,model(name).doc)


if __name__=='__main__': unittest.main()
