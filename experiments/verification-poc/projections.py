"""Finite model projections; all consume the same typed model."""
import json
from pathlib import Path
from finite_model import encode, rename
from circuit import digest


def term(model, e, backend):
    op=e[0]
    if op=='bool': return str(e[1]).upper() if backend=='tla' else str(e[1]).lower()
    if op=='byte': return str(e[1]) if backend=='tla' else f'(BitVec.ofNat 8 {e[1]})' if backend=='lean' else f'(_ bv{e[1]} 8)'
    if op=='enum':
        return json.dumps(e[1]+'.'+e[2]) if backend=='tla' else f'E_{e[1]}.c_{e[2]}' if backend=='lean' else f'(_ bv{model.enums[e[1]].index(e[2])} {model.width(e[1])})'
    if op=='var': return f'{e[1]}_f_{e[2]}' if backend=='smt' else f'{e[1]}.f_{e[2]}'
    args=[term(model,x,backend) for x in e[1:]]
    if backend=='smt':
        if op=='ite': return f"(ite {' '.join(args)})"
        eq={'!':'not','&&':'and','||':'or','==':'=','!=':'distinct','+':'bvadd','-':'bvsub','<':'bvult','>':'bvugt','<=':'bvule','>=':'bvuge'}
        return f"({eq[op]} {' '.join(args)})"
    if op=='ite':
        return f'(IF {args[0]} THEN {args[1]} ELSE {args[2]})' if backend=='tla' else f'(bif {args[0]} then {args[1]} else {args[2]})'
    if op=='!': return f"({'~' if backend=='tla' else '!'}{args[0]})"
    if backend=='tla':
        symbol={'&&':'/\\','||':'\\/','==':'=','!=':'#','+':'+','-':'-','<':'<','>':'>','<=':'<=','>=':'>='}[op]
        result=f'({args[0]} {symbol} {args[1]})'
        if op=='-': result=f'({args[0]} + 256 - {args[1]})'
        return f'({result} % 256)' if op in ('+','-') else result
    if op in ('==','!=','<','>','<=','>='):
        symbol={'==':'=','!=':'≠'}.get(op,op)
        return f'(decide ({args[0]} {symbol} {args[1]}))'
    return f'({args[0]} {op} {args[1]})'


def smt_domain(model,p):
    guards=[]
    for f,t in model.fields.items():
        if t in model.enums and len(model.enums[t])<2**model.width(t):
            guards.append(f'(bvult {p}_f_{f} (_ bv{len(model.enums[t])} {model.width(t)}))')
    return '(and true '+ ' '.join(guards)+')'


def declarations(model, names):
    return '\n'.join(f'(declare-const {p}_f_{f} '+('Bool' if t=='Bool' else f'(_ BitVec {model.width(t)})')+')' for p in names for f,t in model.fields.items())


def bmc(model, bound, values=False):
    if not 0<=bound<=64: raise ValueError('BMC bound must be 0..64')
    ps=[f's{i}' for i in range(bound+1)]
    lines=['(set-logic QF_BV)',declarations(model,ps)]
    for p in ps: lines.append(f'(assert {smt_domain(model,p)})')
    lines.append('(assert '+term(model,rename(model.terms['initial'],'s0'),'smt')+')')
    for i in range(bound):
        # Rename both formal transition states independently.
        def rewrite(e):
            if e[0]=='var': return ['var',ps[i] if e[1]=='s' else ps[i+1],e[2],e[3]]
            if e[0] in ('bool','byte','enum'): return e
            return [e[0],*(rewrite(x) for x in e[1:])]
        action=term(model,rewrite(model.terms['step']),'smt')
        same='(and '+ ' '.join(f'(= {ps[i]}_f_{f} {ps[i+1]}_f_{f})' for f in model.fields)+')'
        lines.append(f'(assert (or {same} {action}))')
    bad='(or '+ ' '.join('(not '+term(model,rename(model.terms['invariant'],p),'smt')+')' for p in ps)+')'
    lines += [f'(assert {bad})','(check-sat)']
    if values: lines.append('(get-value ('+' '.join(f'{p}_f_{f}' for p in ps for f in model.fields)+'))')
    return '\n'.join(lines)+'\n'


def emit(model, directory):
    out=Path(directory);out.mkdir(parents=True,exist_ok=True)
    obligations={}
    for role in ('initial','base','step'):
        c,root=encode(model,role); text=c.dimacs(root)
        (out/f'{role}.cnf').write_text(text)
        obligations[role]={'sha256':digest(text),'variables':c.count,'inputs':c.inputs}
    ini=term(model,model.terms['initial'],'smt'); inv=term(model,model.terms['invariant'],'smt')
    nxt=term(model,model.terms['step'],'smt'); inv_t=term(model,rename(model.terms['invariant'],'t'),'smt')
    assertions={'initial':f'(and {smt_domain(model,"s")} {ini})','base':f'(and {smt_domain(model,"s")} {ini} (not {inv}))','step':f'(and {smt_domain(model,"s")} {smt_domain(model,"t")} {inv} {nxt} (not {inv_t}))'}
    for role,assertion in assertions.items():
        (out/f'{role}.smt2').write_text('(set-logic QF_BV)\n'+declarations(model,['s','t'])+f'\n(assert {assertion})\n(check-sat)\n')
    lines=['import Std.Tactic.BVDecide','namespace OakFinite']
    for name,cases in model.enums.items():
        lines += [f'inductive E_{name} where',*[f'  | c_{case}' for case in cases],'  deriving DecidableEq']
    lines += ['structure State where']
    for f,t in model.fields.items(): lines.append(f'  f_{f} : '+('BitVec 8' if t=='u8' else 'Bool' if t=='Bool' else 'E_'+t))
    lines += ['  deriving DecidableEq']
    for role,name in (('initial','oakInitial'),('invariant','oakInvariant'),('step','oakStep')):
        params='s t' if role=='step' else 's'
        lines += [f'def {name} ({params} : State) : Bool := {term(model,model.terms[role],"lean")}']
    for name,statement,ps in (('base','oakInitial s = true → oakInvariant s = true',['s']),('step','oakInvariant s = true → oakStep s t = true → oakInvariant t = true',['s','t'])):
        lines += [f'theorem {name} ({" ".join(ps)} : State) : {statement} := by']
        for p in ps: lines.append('  rcases '+p+' with ⟨'+', '.join(f'{p}{i}' for i in range(len(model.fields)))+'⟩')
        split=[f'cases {p}{i}' for p in ps for i,t in enumerate(model.fields.values()) if t in model.enums]
        lines.append('  '+' <;> '.join(split+['simp_all only [oakInitial, oakInvariant, oakStep]','bv_decide']))
    lines+=['end OakFinite',''];(out/'Model.lean').write_text('\n'.join(lines))
    domain='['+', '.join('f_'+f+' : '+('BOOLEAN' if t=='Bool' else '0..255' if t=='u8' else '{'+', '.join(json.dumps(t+'.'+v) for v in model.enums[t])+'}') for f,t in model.fields.items())+']'
    lines=['---- MODULE Model ----','EXTENDS Integers, TLC','VARIABLE state','StateSpace == '+domain]
    for role,name in (('initial','OakInitial'),('invariant','OakInvariant'),('step','OakStep')):
        params='s, t' if role=='step' else 's'
        lines.append(f'{name}({params}) == {term(model,model.terms[role],"tla")}')
    lines += ['Init == state \\in StateSpace /\\ OakInitial(state)', "Next == \\E target \\in StateSpace : state' = target /\\ OakStep(state, target)", 'Spec == Init /\\ [][Next]_state','TypeOK == state \\in StateSpace','Safe == OakInvariant(state)','====','']
    (out/'Model.tla').write_text('\n'.join(lines));(out/'Model.cfg').write_text('SPECIFICATION Spec\nINVARIANT TypeOK\nINVARIANT Safe\nCHECK_DEADLOCK FALSE\n')
    manifest={'format':'oak-projection-1','semantic_digest':model.digest,'frontend':model.frontend,'obligations':obligations,'translation_trusted':True}
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return manifest
