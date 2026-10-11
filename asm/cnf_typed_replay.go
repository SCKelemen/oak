package asm

// Independent, audit-only replay of a completed typed implication circuit.
// This does not change the native certificate grammar, verifier, or verdict
// cache. A checked Go execution is not a Lean refinement proof of that Go
// execution. In particular a successful audit never creates DecisionProven.

import (
	"context"
	"errors"
	"fmt"
)

var errTypedCNFResource = errors.New("typed CNF replay resource limit")

// All limits are diagnostic ceilings, not verifier proof budgets. Work counts
// one visit for each node, field-vector element, bit, primitive gate request,
// input binding and read-class comparison. Before the existing allocation and
// ordered-clause validators, their complete linear scans are conservatively
// reserved as 32 visits per variable/gate and 8 per clause. The reservation is
// charged even on early refusal. No deletion or memo hit replenishes work.
type typedCNFLimits struct{ Nodes, Visits, Gates, Variables int }

var typedCNFDiagnosticLimits = typedCNFLimits{8192, 4194304, 65536, 65536}

type typedCNFAudit struct {
	Nodes, Inputs, Gates, ReadBlocks, Visits int
	Claim, Obligation                        int
	// The snapshot owns all slices/maps/terms inspected by replay. Callers must
	// have exclusive access while snapshotting the producer. Replay itself never
	// reads producer contents again, and its result shares nothing mutable with it.
	snapshot *blaster
	roots    [4]*term
}

type typedCNFReplay struct {
	*nativeCNFReplay
	ctx        context.Context
	limit      typedCNFLimits
	visits     int
	active     map[*term]bool
	structural map[*term]int
	structures map[typedCNFStructure]int
	readSlots  map[int]int // complete structural read ID -> exact producer slot
	slotReads  map[int]int
}

type typedCNFStructure struct {
	Kind              termKind
	Width, Declared   int
	Name, Op          string
	Value             uint64
	Cond, Left, Right int
}

func (r *typedCNFReplay) charge(n int) error {
	if err := r.ctx.Err(); err != nil {
		return err
	}
	if n < 0 || n > r.limit.Visits-r.visits {
		return errTypedCNFResource
	}
	r.visits += n
	return nil
}

// checkTypedCNFImplication admits precisely P -> L=R, with no domain or trap
// roots. claim must be the explicit three-node eq/true/ITE wrapper. The source
// graph can contain any names and any number of structural read classes.
func checkTypedCNFImplication(ctx context.Context, producer *blaster, premise, left, right, claim *term, emitted [][]int, limits typedCNFLimits) (typedCNFAudit, error) {
	r := &typedCNFReplay{ctx: ctx, limit: limits, active: map[*term]bool{}, structural: map[*term]int{}, structures: map[typedCNFStructure]int{}, readSlots: map[int]int{}, slotReads: map[int]int{}}
	if ctx == nil {
		return typedCNFAudit{}, fmt.Errorf("missing replay context")
	}
	if limits.Nodes <= 0 || limits.Visits <= 0 || limits.Gates <= 0 || limits.Variables <= 0 {
		return typedCNFAudit{}, errTypedCNFResource
	}
	snapshot, roots, clauses, err := r.snapshot(producer, [4]*term{premise, left, right, claim}, emitted)
	if err != nil {
		return typedCNFAudit{}, err
	}
	r.nativeCNFReplay = &nativeCNFReplay{bl: snapshot, terms: map[*term][]int{}, inputs: map[int]bool{}, gateKeys: map[cnfKey]bool{}, maxInt: int(^uint(0) >> 1), startShape: snapshotCNFObligationCounts(snapshot)}
	premise, left, right, claim = roots[0], roots[1], roots[2], roots[3]
	if premise.width != 1 || left.width != right.width || claim.kind != termIte || claim.width != 1 || claim.cond != premise || claim.left == nil || claim.right == nil || claim.left.kind != termCmp || claim.left.width != 1 || claim.left.op != "eq" || claim.left.left != left || claim.left.right != right || claim.right.kind != termConst || claim.right.width != 1 || claim.right.value != 1 {
		return typedCNFAudit{}, fmt.Errorf("the exact implication wrapper is missing")
	}
	if err := r.charge(32*(snapshot.cnf.variables+len(snapshot.cnf.gates)) + 8*len(clauses)); err != nil {
		return typedCNFAudit{}, err
	}
	if err := validateCNFGateMemo(snapshot.cnf); err != nil {
		return typedCNFAudit{}, fmt.Errorf("gate memo: %w", err)
	}
	bits, err := r.term(claim)
	if err != nil {
		return typedCNFAudit{}, err
	}
	// This formula-only diagnostic refuses settled cases. Neither abstract SAT
	// nor a constant-true violation is claimed to be a concrete counterexample.
	if len(bits) != 1 || bits[0] < 2 {
		return typedCNFAudit{}, fmt.Errorf("implication settled without a refutable CNF")
	}
	obligation := bits[0] ^ 1
	if err := validateCNFTrace(snapshot.cnf, []int{obligation}, clauses); err != nil {
		return typedCNFAudit{}, fmt.Errorf("ordered clause trace: %w", err)
	}
	if err := r.finish(); err != nil {
		return typedCNFAudit{}, err
	}
	if len(r.slotReads) != len(snapshot.selects) {
		return typedCNFAudit{}, fmt.Errorf("unaccounted read block")
	}
	if err := r.charge(0); err != nil {
		return typedCNFAudit{}, err
	}
	return typedCNFAudit{len(r.terms), len(r.inputs), len(r.gateKeys), len(r.slotReads), r.visits, bits[0], obligation, snapshot, roots}, nil
}

// snapshot preserves pointer identity via a bijection, including distinct
// structurally identical nodes. It rejects cycles before recursive replay and
// checks every count before proportional allocation. Strings are immutable.
func (r *typedCNFReplay) snapshot(bl *blaster, roots [4]*term, emitted [][]int) (*blaster, [4]*term, [][]int, error) {
	fail := func(msg string) (*blaster, [4]*term, [][]int, error) {
		return nil, [4]*term{}, nil, fmt.Errorf("typed snapshot: %s", msg)
	}
	if bl == nil || bl.cnf == nil {
		return fail("missing producer")
	}
	c := bl.cnf
	if bl.grouped || bl.components || bl.assumed || bl.slots != selectSlots || c.exceeded {
		return fail("unsupported ordering or incomplete producer")
	}
	if len(bl.memo) > r.limit.Nodes || len(bl.params) > r.limit.Nodes || len(bl.selects) > r.limit.Nodes || c.variables < 0 || c.variables > r.limit.Variables || len(c.gates) > r.limit.Gates || len(c.inputs) > r.limit.Variables || len(c.memo) != len(c.gates) || len(c.clauses) > 6*len(c.gates) || len(emitted) != len(c.clauses)+1 {
		return fail("collection limit or shape")
	}
	if len(bl.params) != len(bl.index) || len(bl.params) != len(bl.widths) || len(bl.owners) > len(c.inputs) {
		return fail("declaration table shape")
	}
	if err := r.charge(1 + len(bl.params)*4 + len(c.inputs)*2 + len(c.gates)*2 + len(c.memo) + len(bl.owners)*2); err != nil {
		return nil, [4]*term{}, nil, err
	}
	owned := &blaster{slots: selectSlots, params: append([]string(nil), bl.params...), index: map[string]int{}, widths: map[string]int{}, owners: map[int]variableOwner{}, memo: map[*term][]int{}, cnf: &cnfBuilder{variables: c.variables, inputs: map[int]int{}, memo: map[cnfKey]int{}, gates: append([]cnfGate(nil), c.gates...)}}
	for position, name := range bl.params {
		p, ok := bl.index[name]
		w, known := bl.widths[name]
		if name == "" || len(name) > 128 || !ok || p != position || !known || w < 1 || w > 64 {
			return fail("invalid declaration")
		}
		if _, dup := owned.index[name]; dup {
			return fail("duplicate declaration")
		}
		owned.index[name] = p
		owned.widths[name] = w
	}
	for source, v := range c.inputs {
		owned.cnf.inputs[source] = v
	}
	for key, v := range c.memo {
		owned.cnf.memo[key] = v
	}
	for source, v := range bl.owners {
		position, known := owned.index[v.param]
		width := owned.widths[v.param]
		if _, present := c.inputs[source]; !present || !known || v.bit < 0 || v.bit >= width || source != v.bit*(len(bl.params)+selectSlots)+position {
			return fail("invalid owner binding")
		}
		owned.owners[source] = v
	}
	cloneClauses := func(src [][]int) ([][]int, error) {
		result := make([][]int, len(src))
		for i, clause := range src {
			if len(clause) > 3 {
				return nil, fmt.Errorf("typed snapshot: clause width")
			}
			if err := r.charge(1 + len(clause)); err != nil {
				return nil, err
			}
			result[i] = append([]int(nil), clause...)
		}
		return result, nil
	}
	var err error
	owned.cnf.clauses, err = cloneClauses(c.clauses)
	if err != nil {
		return nil, [4]*term{}, nil, err
	}
	clauses, err := cloneClauses(emitted)
	if err != nil {
		return nil, [4]*term{}, nil, err
	}
	clones := map[*term]*term{}
	active := map[*term]bool{}
	var clone func(*term) (*term, error)
	clone = func(t *term) (*term, error) {
		if err := r.charge(1); err != nil {
			return nil, err
		}
		if t == nil {
			return nil, nil
		}
		if active[t] {
			return nil, fmt.Errorf("typed snapshot: cyclic graph")
		}
		if v, ok := clones[t]; ok {
			return v, nil
		}
		if len(clones) >= r.limit.Nodes || len(t.args) != 0 || t.width < 1 || t.width > 64 || t.declared < 0 || t.declared > 64 || len(t.name) > 128 || len(t.op) > 8 {
			return nil, fmt.Errorf("typed snapshot: term limit or shape")
		}
		bits, ok := bl.memo[t]
		if !ok || len(bits) != t.width {
			return nil, fmt.Errorf("typed snapshot: missing or malformed term roots")
		}
		if err := r.charge(len(bits) + 3); err != nil {
			return nil, err
		}
		v := *t
		v.args = nil
		clones[t] = &v
		active[t] = true
		if v.cond, err = clone(t.cond); err != nil {
			return nil, err
		}
		if v.left, err = clone(t.left); err != nil {
			return nil, err
		}
		if v.right, err = clone(t.right); err != nil {
			return nil, err
		}
		delete(active, t)
		owned.memo[&v] = append([]int(nil), bits...)
		return &v, nil
	}
	var copied [4]*term
	for i, t := range roots {
		if t == nil {
			return fail("missing root")
		}
		copied[i], err = clone(t)
		if err != nil {
			return nil, [4]*term{}, nil, err
		}
	}
	if len(clones) != len(bl.memo) {
		return fail("unreachable producer term")
	}
	owned.selects = make([]selectAbstraction, len(bl.selects))
	for i, read := range bl.selects {
		idx, present := clones[read.index]
		if !present || len(read.idx) != 32 || len(read.vars) != 32 || read.span == "" || len(read.span) > 128 {
			return fail("read block shape or index")
		}
		if err := r.charge(65); err != nil {
			return nil, [4]*term{}, nil, err
		}
		// Producer linear forms have no semantic authority in this profile.
		owned.selects[i] = selectAbstraction{span: read.span, index: idx, idx: append([]int(nil), read.idx...), vars: append([]int(nil), read.vars...)}
	}
	return owned, copied, clauses, nil
}

func (r *typedCNFReplay) term(t *term) ([]int, error) {
	if err := r.charge(1); err != nil {
		return nil, err
	}
	if t == nil {
		return nil, fmt.Errorf("missing typed term")
	}
	if out, ok := r.terms[t]; ok {
		return out, nil
	}
	if r.active[t] {
		return nil, fmt.Errorf("cyclic typed graph")
	}
	r.active[t] = true
	defer delete(r.active, t)
	if t.width < 1 || t.width > 64 || len(t.args) != 0 {
		return nil, fmt.Errorf("malformed typed term")
	}
	var out []int
	var err error
	switch t.kind {
	case termParam, termConst:
		// The narrow leaf checks retain exact raw/effective declaration metadata.
		if err = r.charge(t.width); err != nil {
			return nil, err
		}
		out, err = r.nativeCNFReplay.term(t)
		if err != nil {
			return nil, err
		}
		if t.kind == termParam {
			for bit := 0; bit < t.width && bit < t.declaredWidth(); bit++ {
				source := bit*(len(r.bl.params)+selectSlots) + r.bl.index[t.name]
				owner, ok := r.bl.owners[source]
				if !ok || owner.param != t.name || owner.bit != bit {
					return nil, fmt.Errorf("parameter owner binding")
				}
			}
		}
	case termBinary, termCmp:
		if t.name != "" || t.value != 0 || t.declared != 0 || t.cond != nil || t.left == nil || t.right == nil {
			return nil, fmt.Errorf("malformed typed operation")
		}
		a, e := r.term(t.left)
		if e != nil {
			return nil, e
		}
		b, e := r.term(t.right)
		if e != nil {
			return nil, e
		}
		if t.kind == termCmp {
			if len(a) != len(b) {
				return nil, fmt.Errorf("comparison operand widths differ")
			}
			var edge int
			edge, err = r.compare(t.op, a, b)
			out = make([]int, t.width)
			out[0] = edge
		} else {
			if err = r.charge(3 * t.width); err != nil {
				return nil, err
			}
			a = replayAdapt(a, t.width)
			b = replayAdapt(b, t.width)
			switch t.op {
			case "and", "or", "xor":
				operation := map[string]int{"and": opAnd, "or": opOr, "xor": opXor}[t.op]
				out = make([]int, t.width)
				for i := range out {
					out[i], err = r.apply(operation, a[i], b[i])
					if err != nil {
						return nil, err
					}
				}
			case "add", "sub":
				carry := bddFalse
				if t.op == "sub" {
					carry = bddTrue
					for i := range b {
						b[i] ^= 1
					}
				}
				out, _, err = r.add(a, b, carry)
			case "shl", "shr":
				if t.width != 32 && t.width != 64 {
					return nil, fmt.Errorf("logical shift width is outside 32/64")
				}
				if t.right.kind == termConst {
					out, err = r.shift(a, int(t.right.value%uint64(t.width)), t.op == "shl")
				} else {
					out, err = r.barrel(a, b, t.op == "shl")
				}
			default:
				return nil, fmt.Errorf("unsupported typed binary %q", t.op)
			}
		}
	case termIte:
		if t.name != "" || t.op != "" || t.value != 0 || t.declared != 0 || t.cond == nil || t.left == nil || t.right == nil {
			return nil, fmt.Errorf("malformed typed ITE")
		}
		guard, e := r.term(t.cond)
		if e != nil {
			return nil, e
		}
		// The independent derivation has already established every guard bit.
		// Requiring literal false above bit zero proves Boolean range for all
		// valuations, including declaration-width-one views and wide comparisons.
		for _, edge := range guard[1:] {
			if edge != bddFalse {
				return nil, fmt.Errorf("ITE guard has no zero/one derivation")
			}
		}
		a, e := r.term(t.left)
		if e != nil {
			return nil, e
		}
		b, e := r.term(t.right)
		if e != nil {
			return nil, e
		}
		if err = r.charge(3*t.width + len(guard)); err != nil {
			return nil, err
		}
		a = replayAdapt(a, t.width)
		b = replayAdapt(b, t.width)
		out = make([]int, t.width)
		for i := range out {
			out[i], err = r.ite(guard[0], a[i], b[i])
			if err != nil {
				return nil, err
			}
		}
	case termSelect:
		if t.name == "" || t.width != 32 || t.op != "" || t.value != 0 || t.declared != 0 || t.cond != nil || t.left == nil || t.left.width != 32 || t.right != nil {
			return nil, fmt.Errorf("read requires exact span and 32-bit index/value")
		}
		idx, e := r.term(t.left)
		if e != nil {
			return nil, e
		}
		out, err = r.read(t, idx)
	default:
		return nil, fmt.Errorf("unsupported typed kind %d", t.kind)
	}
	if err != nil {
		return nil, err
	}
	if err = r.charge(len(out)); err != nil {
		return nil, err
	}
	if err = r.recordTerm(t, out); err != nil {
		return nil, err
	}
	key := typedCNFStructure{t.kind, t.width, t.declared, t.name, t.op, t.value, r.structural[t.cond], r.structural[t.left], r.structural[t.right]}
	id, ok := r.structures[key]
	if !ok {
		id = len(r.structures) + 1
		r.structures[key] = id
	}
	r.structural[t] = id
	return out, nil
}

func (r *typedCNFReplay) apply(op, x, y int) (int, error) {
	if err := r.charge(1); err != nil {
		return 0, err
	}
	return r.nativeCNFReplay.apply(op, x, y)
}
func (r *typedCNFReplay) ite(c, t, e int) (int, error) {
	if c < 0 || t < 0 || e < 0 {
		return 0, fmt.Errorf("negative CNF edge")
	}
	if err := r.charge(1); err != nil {
		return 0, err
	}
	switch {
	case c == bddTrue:
		return t, nil
	case c == bddFalse:
		return e, nil
	case t == e:
		return t, nil
	case t == bddTrue && e == bddFalse:
		return c, nil
	case t == bddFalse && e == bddTrue:
		return c ^ 1, nil
	case t == bddTrue:
		return r.apply(opOr, c, e)
	case t == bddFalse:
		return r.apply(opAnd, c^1, e)
	case e == bddTrue:
		return r.apply(opOr, c^1, t)
	case e == bddFalse:
		return r.apply(opAnd, c, t)
	}
	return r.gateEdge(cnfKey{cnfIte, c, t, e})
}
func (r *typedCNFReplay) add(a, b []int, carry int) ([]int, int, error) {
	if err := r.charge(len(a)); err != nil {
		return nil, 0, err
	}
	out := make([]int, len(a))
	for i := range a {
		axb, e := r.apply(opXor, a[i], b[i])
		if e != nil {
			return nil, 0, e
		}
		out[i], e = r.apply(opXor, axb, carry)
		if e != nil {
			return nil, 0, e
		}
		ab, e := r.apply(opAnd, a[i], b[i])
		if e != nil {
			return nil, 0, e
		}
		cx, e := r.apply(opAnd, carry, axb)
		if e != nil {
			return nil, 0, e
		}
		carry, e = r.apply(opOr, ab, cx)
		if e != nil {
			return nil, 0, e
		}
	}
	return out, carry, nil
}
func (r *typedCNFReplay) compare(op string, a, b []int) (int, error) {
	if op == "eq" || op == "ne" {
		eq := bddTrue
		for i := len(a) - 1; i >= 0; i-- {
			x, e := r.apply(opXor, a[i], b[i])
			if e != nil {
				return 0, e
			}
			eq, e = r.apply(opAnd, eq, x^1)
			if e != nil {
				return 0, e
			}
		}
		if op == "ne" {
			eq ^= 1
		}
		return eq, nil
	}
	if op != "lo" && op != "hs" {
		return 0, fmt.Errorf("unsupported typed comparison %q", op)
	}
	if err := r.charge(len(b)); err != nil {
		return 0, err
	}
	neg := make([]int, len(b))
	for i := range b {
		neg[i] = b[i] ^ 1
	}
	sum, carry, e := r.add(a, neg, bddTrue)
	if e != nil {
		return 0, e
	}
	// condition constructs auxiliary overflow, zero and N=V gates even when
	// its returned condition uses only carry. Replay all of them for coverage.
	top := len(a) - 1
	x, e := r.apply(opXor, a[top], b[top])
	if e != nil {
		return 0, e
	}
	y, e := r.apply(opXor, sum[top], a[top])
	if e != nil {
		return 0, e
	}
	v, e := r.apply(opAnd, x, y)
	if e != nil {
		return 0, e
	}
	z := bddTrue
	for i := top; i >= 0; i-- {
		z, e = r.apply(opAnd, z, sum[i]^1)
		if e != nil {
			return 0, e
		}
	}
	if _, e = r.apply(opXor, sum[top], v); e != nil {
		return 0, e
	}
	if op == "lo" {
		carry ^= 1
	}
	return carry, nil
}
func (r *typedCNFReplay) shift(a []int, k int, left bool) ([]int, error) {
	if err := r.charge(len(a)); err != nil {
		return nil, err
	}
	out := make([]int, len(a))
	for i := range out {
		j := i + k
		if left {
			j = i - k
		}
		if j >= 0 && j < len(a) {
			out[i] = a[j]
		}
	}
	return out, nil
}
func (r *typedCNFReplay) barrel(a, count []int, left bool) ([]int, error) {
	stages := 5
	if len(a) == 64 {
		stages = 6
	}
	current := a
	for stage := 0; stage < stages; stage++ {
		shifted, e := r.shift(current, 1<<uint(stage), left)
		if e != nil {
			return nil, e
		}
		if e = r.charge(len(a)); e != nil {
			return nil, e
		}
		next := make([]int, len(a))
		for i := range a {
			next[i], e = r.ite(count[stage], shifted[i], current[i])
			if e != nil {
				return nil, e
			}
		}
		current = next
	}
	return current, nil
}
func (r *typedCNFReplay) read(t *term, idx []int) ([]int, error) {
	indexID, ok := r.structural[t.left]
	if !ok {
		return nil, fmt.Errorf("read index has no structural derivation")
	}
	key := typedCNFStructure{Kind: termSelect, Width: 32, Name: t.name, Left: indexID}
	class, known := r.structures[key]
	if !known {
		class = len(r.structures) + 1
		r.structures[key] = class
	}
	slot, known := r.readSlots[class]
	if !known {
		slot = -1
		for i, read := range r.bl.selects {
			if err := r.charge(1); err != nil {
				return nil, err
			}
			if read.span == t.name && r.structural[read.index] == indexID {
				if slot != -1 {
					return nil, fmt.Errorf("duplicate structural read blocks")
				}
				slot = i
			}
		}
		if slot < 0 {
			return nil, fmt.Errorf("producer read merge lacks complete structural identity")
		}
		if old, present := r.slotReads[slot]; present && old != class {
			return nil, fmt.Errorf("distinct structural reads share a block")
		}
		r.readSlots[class] = slot
		r.slotReads[slot] = class
	}
	read := r.bl.selects[slot]
	if !sameReplayBits(read.idx, idx) {
		return nil, fmt.Errorf("read index roots differ")
	}
	if err := r.charge(96); err != nil {
		return nil, err
	}
	out := make([]int, 32)
	stride := len(r.bl.params) + selectSlots
	for bit := range out {
		source := 0
		if slot < selectSlots {
			source = bit*stride + len(r.bl.params) + slot
		} else {
			source = 64*stride + 64*(slot-selectSlots) + bit
		}
		if read.vars[bit] != source {
			return nil, fmt.Errorf("read source bit binding")
		}
		if _, owned := r.bl.owners[source]; owned {
			return nil, fmt.Errorf("read source is also a scalar")
		}
		edge, e := r.inputEdge(source)
		if e != nil {
			return nil, e
		}
		out[bit] = edge
	}
	return out, nil
}
