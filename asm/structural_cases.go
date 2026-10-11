package asm

// A structural case proof complements the bit-level equality decision. A
// summarized memory can retain the stores from several mutually exclusive
// paths: the whole diagram repeats all those paths even when each path makes
// the two results the same term. Cofactor one exact Boolean guard at a time,
// retaining both outcomes, and accept only when every leaf is identical.
// Failure is only a missed shortcut; the original decision follows unchanged.

type structuralCaseLimits struct{ inputs, nodes, work, depth int }

// Complete comparable keys, not hash digests, identify the private nodes.
// In particular a read keeps its memory name, element width and entire index;
// neither distinct memories nor possibly-aliasing indices are equated here.
type structuralCaseNode struct {
	kind              termKind
	width, declared   int
	op, name          string
	value             uint64
	cond, left, right int
}

type structuralCases struct {
	limits    structuralCaseLimits
	nodes     []structuralCaseNode
	ids       map[structuralCaseNode]int
	work      int
	exhausted bool
	leaves    int
	reverse   bool // test the same proof with the other case visited first
}

func structurallyEqualByCases(a, b *term) bool {
	s := newStructuralCases(structuralCaseLimits{1 << 16, 1 << 17, 1 << 20, 4})
	return s.equal(a, b)
}

func newStructuralCases(limits structuralCaseLimits) *structuralCases {
	return &structuralCases{limits: limits, ids: map[structuralCaseNode]int{}}
}

func (s *structuralCases) spend() bool {
	if s.exhausted || s.work >= s.limits.work {
		s.exhausted = true
		return false
	}
	s.work++
	return true
}

func (s *structuralCases) put(n structuralCaseNode) int {
	if id, ok := s.ids[n]; ok {
		return id
	}
	if s.exhausted || len(s.nodes) >= s.limits.nodes {
		s.exhausted = true
		return -1
	}
	id := len(s.nodes)
	s.ids[n] = id
	s.nodes = append(s.nodes, n)
	return id
}

func (s *structuralCases) constant(value uint64, width int) int {
	return s.put(structuralCaseNode{kind: termConst, width: width, value: value & mask(width), cond: -1, left: -1, right: -1})
}

// fold only uses local identities. It never invokes a term constructor that
// could populate an input term's significant-bit cache or walk its DAG.
func (s *structuralCases) fold(n structuralCaseNode) int {
	if n.kind == termConst {
		n.value &= mask(n.width)
	}
	if n.kind == termIte {
		c, l, r := s.nodes[n.cond], s.nodes[n.left], s.nodes[n.right]
		if c.kind == termConst {
			chosen := n.right
			if c.value != 0 {
				chosen = n.left
			}
			// A selected arm is observed at the ITE's width. Leaving a
			// mismatched width intact is conservative, including extensions.
			if s.nodes[chosen].width == n.width {
				return chosen
			}
		}
		if n.left == n.right && l.width == n.width && r.width == n.width {
			return n.left
		}
	}
	if n.kind == termBinary {
		l, r := s.nodes[n.left], s.nodes[n.right]
		m := mask(n.width)
		if l.kind == termConst && r.kind == termConst {
			switch n.op {
			case "add", "sub", "mul", "and", "or", "xor", "shl", "shr", "sar":
				return s.constant(evalBinary(n.op, l.value&m, r.value&m, n.width), n.width)
			}
		}
		switch n.op {
		case "and":
			if l.kind == termConst && l.value&m == 0 || r.kind == termConst && r.value&m == 0 {
				return s.constant(0, n.width)
			}
			if l.kind == termConst && l.value&m == m && r.width == n.width {
				return n.right
			}
			if r.kind == termConst && r.value&m == m && l.width == n.width {
				return n.left
			}
		case "add", "or", "xor":
			if l.kind == termConst && l.value&m == 0 && r.width == n.width {
				return n.right
			}
			if r.kind == termConst && r.value&m == 0 && l.width == n.width {
				return n.left
			}
		}
	}
	if n.kind == termCmp {
		l, r := s.nodes[n.left], s.nodes[n.right]
		if l.kind == termConst && r.kind == termConst {
			v := uint64(0)
			if conditionHolds(n.op, l.value, r.value, l.width) {
				v = 1
			}
			return s.constant(v, n.width)
		}
	}
	return s.put(n)
}

func (s *structuralCases) equal(a, b *term) bool {
	if a == nil || b == nil || a.width != b.width {
		return false
	}
	ids, ok := s.importTerms(a, b)
	return ok && s.cases(ids[0], ids[1], 0) && !s.exhausted
}

// Import is iterative and bounded, preserves sharing, and reads no mutable
// analysis caches. Quantifier bindings and uninterpreted applications are
// deliberately outside this shortcut; their normal verifier remains in charge.
func (s *structuralCases) importTerms(roots ...*term) ([]int, bool) {
	type frame struct {
		t    *term
		exit bool
	}
	state, ids := map[*term]uint8{}, map[*term]int{nil: -1}
	stack := []frame{}
	for _, t := range roots {
		stack = append(stack, frame{t: t})
	}
	for len(stack) > 0 {
		f := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if !s.spend() {
			return nil, false
		}
		if f.t == nil || state[f.t] == 2 {
			continue
		}
		t := f.t
		if !f.exit {
			if state[t] != 0 || len(state) >= s.limits.inputs || t.width < 1 || t.width > 64 || t.declared < 0 || t.declared > 64 || len(t.args) != 0 {
				return nil, false
			}
			switch t.kind {
			case termParam, termConst:
				if t.cond != nil || t.left != nil || t.right != nil {
					return nil, false
				}
				if t.kind == termConst && t.value&mask(t.width) != t.value {
					return nil, false
				}
			case termBinary, termCmp:
				if t.cond != nil || t.left == nil || t.right == nil {
					return nil, false
				}
				if t.kind == termBinary {
					if (t.op == "shl" || t.op == "shr" || t.op == "sar") && (t.left.width != t.width || t.right.width != t.width || t.width&(t.width-1) != 0) {
						return nil, false
					}
					switch t.op {
					case "add", "sub", "mul", "and", "or", "xor", "shl", "shr", "sar":
					default:
						return nil, false
					}
				} else {
					if t.left.width != t.right.width {
						return nil, false
					}
					switch t.op {
					case "eq", "ne", "hs", "cs", "lo", "cc", "hi", "ls", "ge", "lt", "gt", "le", "mi", "pl", "vs", "vc":
					default:
						return nil, false
					}
				}
			case termIte:
				if t.cond == nil || t.cond.width != 1 || t.left == nil || t.right == nil {
					return nil, false
				}
			case termSelect:
				if t.cond != nil || t.left == nil || t.right != nil {
					return nil, false
				}
			default:
				return nil, false
			}
			state[t] = 1
			stack = append(stack, frame{t, true}, frame{t.right, false}, frame{t.left, false}, frame{t.cond, false})
			continue
		}
		id := s.fold(structuralCaseNode{t.kind, t.width, t.declared, t.op, t.name, t.value, ids[t.cond], ids[t.left], ids[t.right]})
		if id < 0 {
			return nil, false
		}
		ids[t], state[t] = id, 2
	}
	out := make([]int, len(roots))
	for i, t := range roots {
		out[i] = ids[t]
	}
	return out, true
}

// A cofactor owns its memo. Its parent has already been normalized under the
// preceding path, so the only new assumption is guard=value. Its sibling
// starts from that same immutable parent, never this cofactor's results.
func (s *structuralCases) cofactor(a, b, guard int, value bool) (int, int, bool) {
	complement := -1
	g := s.nodes[guard]
	if g.kind == termCmp && (g.op == "eq" || g.op == "ne") {
		if g.op == "eq" {
			g.op = "ne"
		} else {
			g.op = "eq"
		}
		complement = s.put(g)
		if complement < 0 {
			return 0, 0, false
		}
	}
	memo := map[int]int{-1: -1}
	type frame struct {
		id   int
		exit bool
	}
	stack := []frame{{a, false}, {b, false}}
	for len(stack) > 0 {
		f := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if !s.spend() {
			return 0, 0, false
		}
		if _, seen := memo[f.id]; seen {
			continue
		}
		n := s.nodes[f.id]
		if f.id == guard || f.id == complement {
			v := uint64(0)
			if value == (f.id == guard) {
				v = 1
			}
			memo[f.id] = s.constant(v, n.width)
			if memo[f.id] < 0 {
				return 0, 0, false
			}
			continue
		}
		if !f.exit {
			stack = append(stack, frame{f.id, true}, frame{n.right, false}, frame{n.left, false}, frame{n.cond, false})
			continue
		}
		n.cond, n.left, n.right = memo[n.cond], memo[n.left], memo[n.right]
		id := s.fold(n)
		if id < 0 {
			return 0, 0, false
		}
		memo[f.id] = id
	}
	return memo[a], memo[b], true
}

// Prefer a discriminator used by both current roots before splitting individual
// memory addresses. A scalar/constant comparison often selects an entire path
// of stores; splitting each final address first can use every case on one path.
// This is only an ordering choice: the scalar stays symbolic and both outcomes
// still have to close. Compare full keys, including exact eq/ne complements.
func (s *structuralCases) discriminator(a, b int) int {
	key := func(id int) (structuralCaseNode, bool) {
		n := s.nodes[id]
		if n.kind != termCmp || n.width != 1 || n.op != "eq" && n.op != "ne" {
			return structuralCaseNode{}, false
		}
		l, r := s.nodes[n.left], s.nodes[n.right]
		p, c := l, r
		if p.kind != termParam {
			p, c = r, l
		}
		if p.kind != termParam || c.kind != termConst || p.width != c.width || p.declared != p.width {
			return structuralCaseNode{}, false
		}
		n.op = "eq"
		return n, true
	}
	shared := map[structuralCaseNode]bool{}
	// Both walks are over the current cofactored roots, never the interner's
	// earlier branches. Their storage and traversal share the ordinary caps.
	for pass, root := range []int{b, a} {
		seen, stack := map[int]bool{}, []int{root}
		for len(stack) > 0 {
			id := stack[len(stack)-1]
			stack = stack[:len(stack)-1]
			if !s.spend() {
				return -1
			}
			if id < 0 || seen[id] {
				continue
			}
			seen[id] = true
			if k, ok := key(id); ok {
				if pass == 0 {
					shared[k] = true
				} else if shared[k] {
					return id
				}
			}
			n := s.nodes[id]
			stack = append(stack, n.right, n.left, n.cond)
		}
	}
	return -1
}

// Descend matching structure before splitting an outer ITE: the first real
// difference can be a small conditional read deep inside a common guard.
// If the differing nodes themselves have no ITE, use the nearest enclosing
// condition. This is a heuristic only; neither polarity can be omitted.
func (s *structuralCases) split(a, b int) int {
	if guard := s.discriminator(a, b); guard >= 0 || s.exhausted {
		return guard
	}
	type pair struct{ a, b, fallback int }
	stack, seen := []pair{{a, b, -1}}, map[[2]int]bool{}
	for len(stack) > 0 {
		p := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if !s.spend() {
			return -1
		}
		if p.a == p.b || seen[[2]int{p.a, p.b}] {
			continue
		}
		seen[[2]int{p.a, p.b}] = true
		if p.a < 0 || p.b < 0 {
			return p.fallback
		}
		x, y := s.nodes[p.a], s.nodes[p.b]
		fallback := p.fallback
		for _, n := range []structuralCaseNode{y, x} {
			if n.kind == termIte && s.nodes[n.cond].width == 1 {
				fallback = n.cond
			}
		}
		x.cond, x.left, x.right = -1, -1, -1
		y.cond, y.left, y.right = -1, -1, -1
		if x != y {
			return fallback
		}
		x, y = s.nodes[p.a], s.nodes[p.b]
		stack = append(stack, pair{x.right, y.right, fallback}, pair{x.left, y.left, fallback}, pair{x.cond, y.cond, fallback})
	}
	return -1
}

func (s *structuralCases) cases(a, b, depth int) bool {
	if !s.spend() {
		return false
	}
	if a == b {
		s.leaves++
		return true
	}
	if depth >= s.limits.depth {
		return false
	}
	guard := s.split(a, b)
	if guard < 0 || s.nodes[guard].width != 1 {
		return false
	}
	for _, value := range []bool{s.reverse, !s.reverse} {
		x, y, ok := s.cofactor(a, b, guard, value)
		if !ok || !s.cases(x, y, depth+1) {
			return false
		}
	}
	return !s.exhausted
}
