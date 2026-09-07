"""Trusted finite bit-vector encoding. Every gate is defined by equivalence."""
import hashlib
import itertools


class Circuit:
    def __init__(self):
        self.count = 0
        self.clauses = []
        self.inputs = {}
        self.gates = []
        self.cache = {}
        self.one = self.new()
        self.clauses.append([self.one])

    def new(self):
        self.count += 1
        return self.count

    def input(self, name):
        if name not in self.inputs:
            self.inputs[name] = self.new()
        return self.inputs[name]

    def gate(self, op, *args):
        if op not in ('and','or','xor') or len(args)!=2: raise ValueError('unsupported gate')
        x,y=args
        if op=='and':
            if x==-self.one or y==-self.one or x==-y: return -self.one
            if x==self.one or x==y: return y
            if y==self.one: return x
        if op=='or':
            if x==self.one or y==self.one or x==-y: return self.one
            if x==-self.one or x==y: return y
            if y==-self.one: return x
        if op=='xor':
            if x==y: return -self.one
            if x==-y: return self.one
            if x==self.one: return -y
            if y==self.one: return -x
            if x==-self.one: return y
            if y==-self.one: return x
        key=(op,*sorted(args))
        if key in self.cache: return self.cache[key]
        z = self.new()
        self.cache[key]=z
        # Equivalences in propagation-friendly CNF (never one-way implications).
        if op=='and': self.clauses.extend([[-z,x],[-z,y],[z,-x,-y]])
        elif op=='or': self.clauses.extend([[z,-x],[z,-y],[-z,x,y]])
        else:
            for bits in itertools.product((False,True),repeat=2):
                expected=bits[0]!=bits[1]
                self.clauses.append([(-arg if bit else arg) for arg,bit in zip(args,bits)]+[z if expected else -z])
        self.gates.append((z, op, args))
        return z

    def and_(self, *args):
        result = self.one
        for arg in args:
            result = self.gate('and', result, arg)
        return result

    def or_(self, *args):
        result = -self.one
        for arg in args:
            result = self.gate('or', result, arg)
        return result

    def equal(self, a, b):
        return self.and_(*[-self.gate('xor', x, y) for x, y in zip(a, b)])

    def add(self, a, b):
        carry = -self.one
        result = []
        for x, y in zip(a, b):
            xy = self.gate('xor', x, y)
            result.append(self.gate('xor', xy, carry))
            carry = self.or_(self.and_(x, y), self.and_(carry, xy))
        return result

    def less(self, a, b):
        result = -self.one
        for x, y in zip(a, b):
            result = self.or_(self.and_(-x, y), self.and_(-self.gate('xor', x, y), result))
        return result

    def constant(self, n, width):
        return [self.one if n & (1 << i) else -self.one for i in range(width)]

    def dimacs(self, root):
        clauses = self.clauses + [[root]]
        # Remove duplicate literals. Tautological clauses may remain: they are valid DIMACS.
        clauses = [list(dict.fromkeys(c)) for c in clauses]
        return f'p cnf {self.count} {len(clauses)}\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c in clauses)

    def complete(self, values):
        """Test/witness helper; not used by the LRAT checker."""
        env = {self.one: True, **{identifier: values[name] for name, identifier in self.inputs.items()}}
        def value(lit):
            return env[abs(lit)] if lit > 0 else not env[abs(lit)]
        for z, op, args in self.gates:
            bits = list(map(value, args))
            env[z] = all(bits) if op == 'and' else any(bits) if op == 'or' else bits[0] != bits[1]
        return env


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()
