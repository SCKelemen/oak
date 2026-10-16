package asm

import (
	"fmt"
	"reflect"
	"sync"
	"testing"
)

// Build raw nodes: constructors can simplify the intended control, change a
// width, or warm a significant-bit cache before the checker sees the input.
func structuralControlParam(name string, width int) *term {
	return &term{kind: termParam, name: name, width: width, declared: width}
}

func structuralControlConst(value uint64, width int) *term {
	return &term{kind: termConst, value: value & mask(width), width: width}
}

func structuralControlBinary(op string, width int, left, right *term) *term {
	return &term{kind: termBinary, op: op, width: width, left: left, right: right}
}

func structuralControlCmp(op string, left, right *term) *term {
	return &term{kind: termCmp, op: op, width: 1, left: left, right: right}
}

func structuralControlITE(width int, cond, left, right *term) *term {
	return &term{kind: termIte, width: width, cond: cond, left: left, right: right}
}

func structuralControlRead(span string, index *term, width int) *term {
	return &term{kind: termSelect, name: span, width: width, left: index}
}

func structuralControlLimits() structuralCaseLimits {
	return structuralCaseLimits{inputs: 4096, nodes: 8192, work: 131072, depth: 4}
}

func structuralControlDistribution(width int, guard, x, y, z *term) (*term, *term) {
	add := func(a, b *term) *term { return structuralControlBinary("add", width, a, b) }
	return add(structuralControlITE(width, guard, x, y), z),
		structuralControlITE(width, guard, add(x, z), add(y, z))
}

// This oracle deliberately calls the actual bit blaster, never the equality
// dispatcher that now contains the shortcut under test.
func structuralControlBDDEqual(t *testing.T, a, b *term, names []string, widths map[string]int) bool {
	t.Helper()
	bl := newBlaster(names, widths).withBudget(32768)
	left, right := bl.blast(a), bl.blast(b)
	if bl.exceeded() || len(left) != a.width || len(right) != b.width {
		t.Fatal("bounded independent BDD oracle could not blast the control")
	}
	if len(left) != len(right) {
		return false
	}
	difference := bddFalse
	for bit := range left {
		difference = bl.apply(opOr, difference, bl.apply(opXor, left[bit], right[bit]))
	}
	difference = bl.apply(opAnd, bl.consistency(), difference)
	if bl.exceeded() {
		t.Fatal("bounded independent BDD oracle exhausted its budget")
	}
	return difference == bddFalse
}

func TestStructuralCasesRequireBothPolarities(t *testing.T) {
	g := structuralControlParam("g", 1)
	x, y, z := structuralControlParam("x", 4), structuralControlParam("y", 4), structuralControlParam("z", 4)
	for _, reverse := range []bool{false, true} {
		t.Run(fmt.Sprint(reverse), func(t *testing.T) {
			left, right := structuralControlITE(4, g, x, z), structuralControlITE(4, g, y, z)
			if reverse {
				left, right = structuralControlITE(4, g, z, x), structuralControlITE(4, g, z, y)
			}
			s := newStructuralCases(structuralControlLimits())
			s.reverse = reverse
			if s.equal(left, right) || s.leaves != 1 {
				t.Fatalf("one successful polarity must not prove equality: leaves=%d", s.leaves)
			}
			if structuralControlBDDEqual(t, left, right, []string{"g", "x", "y", "z"}, map[string]int{"g": 1, "x": 4, "y": 4, "z": 4}) {
				t.Fatal("the control must have a reachable unequal polarity")
			}
		})
	}
	left, right := structuralControlDistribution(4, g, x, y, z)
	if !structurallyEqualByCases(left, right) {
		t.Fatal("both equal polarities must prove the positive control")
	}
}

func TestStructuralCasesComplementaryAndCorrelatedGuards(t *testing.T) {
	x, y := structuralControlParam("x", 4), structuralControlParam("y", 4)
	eq, ne := structuralControlCmp("eq", x, y), structuralControlCmp("ne", x, y)
	a, b, bad := structuralControlConst(3, 4), structuralControlConst(9, 4), structuralControlConst(12, 4)
	for _, reverse := range []bool{false, true} {
		for _, pair := range [][2]*term{
			{structuralControlITE(4, eq, a, b), structuralControlITE(4, ne, b, a)},
			{structuralControlITE(4, eq, structuralControlITE(4, ne, bad, a), b), structuralControlITE(4, eq, a, b)},
			{structuralControlITE(4, ne, b, structuralControlITE(4, eq, a, bad)), structuralControlITE(4, eq, a, b)},
		} {
			s := newStructuralCases(structuralControlLimits())
			s.reverse = reverse
			if !s.equal(pair[0], pair[1]) || s.leaves < 2 {
				t.Fatalf("complementary correlated guards did not close, reverse=%v leaves=%d", reverse, s.leaves)
			}
			if !structuralControlBDDEqual(t, pair[0], pair[1], []string{"x", "y"}, map[string]int{"x": 4, "y": 4}) {
				t.Fatal("accepted correlated-guard control is not BDD equal")
			}
		}
	}
	// A similarly spelled comparison is not the complement: it has a
	// different operand, even though some assignments correlate the guards.
	other := structuralControlCmp("ne", x, structuralControlConst(0, 4))
	if structurallyEqualByCases(structuralControlITE(4, eq, a, b), structuralControlITE(4, other, b, a)) {
		t.Fatal("different comparison operands acquired a complementary fact")
	}
}

func TestStructuralCasesSharedDAGAlternatingFacts(t *testing.T) {
	g, h := structuralControlParam("g", 1), structuralControlParam("h", 1)
	x, y := structuralControlParam("x", 4), structuralControlParam("y", 4)
	bad := structuralControlConst(13, 4)
	shared := structuralControlITE(4, g, x, y)
	// The same shared node is reached under opposite facts in siblings.
	left := structuralControlITE(4, h,
		structuralControlITE(4, g, shared, bad),
		structuralControlITE(4, g, bad, shared))
	right := structuralControlITE(4, h,
		structuralControlITE(4, g, x, bad),
		structuralControlITE(4, g, bad, y))
	for _, reverse := range []bool{false, true} {
		s := newStructuralCases(structuralControlLimits())
		s.reverse = reverse
		if !s.equal(left, right) || s.leaves < 2 {
			t.Fatalf("shared DAG retained a sibling's fact: reverse=%v leaves=%d", reverse, s.leaves)
		}
	}
	if !structuralControlBDDEqual(t, left, right, []string{"g", "h", "x", "y"}, map[string]int{"g": 1, "h": 1, "x": 4, "y": 4}) {
		t.Fatal("alternating shared-DAG control is not equal")
	}
	wrong := structuralControlITE(4, h,
		structuralControlITE(4, g, x, bad),
		structuralControlITE(4, g, bad, x))
	for _, reverse := range []bool{false, true} {
		s := newStructuralCases(structuralControlLimits())
		s.reverse = reverse
		if s.equal(left, wrong) {
			t.Fatalf("a sibling fact proved an unequal DAG, reverse=%v", reverse)
		}
	}
}

func TestStructuralCasesPreserveUnrepresentedSymbolicKinds(t *testing.T) {
	kind := structuralControlParam("kind", 2)
	value := func(n uint64) *term { return structuralControlConst(n, 4) }
	match := func(n uint64) *term { return structuralControlCmp("eq", kind, structuralControlConst(n, 2)) }
	// Matching representative kind values 0 and 1 says nothing about the
	// remaining symbolic values. A changed kind 2 or 3 must remain visible.
	left := structuralControlITE(4, match(0), value(5),
		structuralControlITE(4, match(1), value(7), value(9)))
	for _, otherKind := range []uint64{2, 3} {
		right := structuralControlITE(4, match(0), value(5),
			structuralControlITE(4, match(1), value(7),
				structuralControlITE(4, match(otherKind), value(11), value(9))))
		for _, reverse := range []bool{false, true} {
			s := newStructuralCases(structuralControlLimits())
			s.reverse = reverse
			if s.equal(left, right) {
				t.Fatalf("unrepresented symbolic kind %d was discarded, reverse=%v", otherKind, reverse)
			}
		}
		for k := uint64(0); k < 4; k++ {
			env := map[string]uint64{"kind": k}
			if (left.eval(env) != right.eval(env)) != (k == otherKind) {
				t.Fatalf("kind control differs at the wrong value: kind=%d changed=%d", k, otherKind)
			}
		}
		if structuralControlBDDEqual(t, left, right, []string{"kind"}, map[string]int{"kind": 2}) {
			t.Fatal("BDD failed to distinguish the unrepresented symbolic kind")
		}
	}
}

func TestStructuralCasesReadIdentityAndWraparound(t *testing.T) {
	g := structuralControlParam("g", 1)
	i, j := structuralControlParam("i", 32), structuralControlParam("j", 32)
	readI, readJ := structuralControlRead("words", i, 32), structuralControlRead("words", j, 32)
	left, right := structuralControlDistribution(32, g, readI, readJ, readI)
	if !structurallyEqualByCases(left, right) {
		t.Fatal("distribution over possibly aliasing word reads must close")
	}
	for _, pair := range [][2]uint64{{0, 0}, {0, 1}, {1, 0}, {0xffffffff, 0}, {0xffffffff, 0xffffffff}} {
		for guard := uint64(0); guard < 2; guard++ {
			env := map[string]uint64{"g": guard, "i": pair[0], "j": pair[1], "words[0]": 0x12345678, "words[1]": 0x89abcdef, "words[4294967295]": 0xfedcba98}
			if left.eval(env) != right.eval(env) {
				t.Fatalf("accepted alias/overlap control differs at i=%#x j=%#x g=%d", pair[0], pair[1], guard)
			}
		}
	}
	wrong := structuralControlITE(32, g, readI, readI)
	if structurallyEqualByCases(structuralControlITE(32, g, readI, readJ), wrong) {
		t.Fatal("potential aliasing was treated as unconditional read equality")
	}
	for name, other := range map[string]*term{
		"span":              structuralControlRead("other.words", i, 32),
		"index":             readJ,
		"index width":       structuralControlRead("words", structuralControlParam("i", 16), 32),
		"index declaration": structuralControlRead("words", &term{kind: termParam, name: "i", width: 32, declared: 16}, 32),
		"element width":     structuralControlRead("words", i, 16),
	} {
		t.Run(name, func(t *testing.T) {
			if structurallyEqualByCases(readI, other) {
				t.Fatal("a distinct read identity was merged")
			}
		})
	}
	// The arithmetic is modulo 2^32 before a read sees the index.
	wrappedIndex := structuralControlBinary("add", 32, structuralControlConst(0xffffffff, 32), structuralControlConst(1, 32))
	wrapped := structuralControlRead("words", wrappedIndex, 32)
	zero := structuralControlRead("words", structuralControlConst(0, 32), 32)
	if !structurallyEqualByCases(wrapped, zero) || wrapped.eval(nil) != zero.eval(nil) {
		t.Fatal("constant 32-bit wrapping index did not preserve the read")
	}
	next := structuralControlRead("words", structuralControlBinary("add", 32, i, structuralControlConst(1, 32)), 32)
	if structurallyEqualByCases(readI, next) {
		t.Fatal("adjacent indices were merged across the 32-bit wrap")
	}
	env := map[string]uint64{"i": 0xffffffff, "words[4294967295]": 7, "words[0]": 11}
	if readI.eval(env) == next.eval(env) || next.eval(env) != 11 {
		t.Fatal("the wrapping-index negative control lacks its expected witness")
	}
}

func TestStructuralCasesWidthAndSignedControls(t *testing.T) {
	g := structuralControlParam("g", 1)
	x4 := structuralControlParam("x", 4)
	x2 := &term{kind: termParam, name: "x", width: 2, declared: 4}
	zero4, zero2 := structuralControlConst(0, 4), structuralControlConst(0, 2)
	widen := func(x *term) *term { return structuralControlBinary("or", 4, x, zero4) }
	tests := []struct {
		name        string
		left, right *term
		value       uint64
	}{
		{"same ITE arms narrow result", widen(structuralControlITE(2, g, x4, x4)), x4, 4},
		{"constant ITE guard narrow result", widen(structuralControlITE(2, structuralControlConst(1, 1), x4, x4)), x4, 4},
		{"narrow ITE arms wide result", structuralControlITE(4, g, x2, x2), x4, 4},
		{"add identity retains result width", widen(structuralControlBinary("add", 2, x4, zero2)), x4, 4},
		{"and identity retains result width", widen(structuralControlBinary("and", 2, x4, structuralControlConst(3, 2))), x4, 4},
		{"signed comparison operand width", structuralControlCmp("lt", x2, zero2), structuralControlCmp("lt", x4, zero4), 2},
		{"signed versus unsigned comparison", structuralControlCmp("lt", x4, zero4), structuralControlCmp("lo", x4, zero4), 8},
		{"signed versus logical shift", structuralControlBinary("sar", 4, x4, structuralControlConst(1, 4)), structuralControlBinary("shr", 4, x4, structuralControlConst(1, 4)), 8},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if structurallyEqualByCases(test.left, test.right) {
				t.Fatal("width/signed negative control was proved")
			}
			env := map[string]uint64{"g": 1, "x": test.value}
			if test.left.eval(env) == test.right.eval(env) {
				t.Fatal("negative control lacks a concrete unequal evaluation")
			}
			if structuralControlBDDEqual(t, test.left, test.right, []string{"g", "x"}, map[string]int{"g": 1, "x": 4}) {
				t.Fatal("independent BDD failed to distinguish width/signed control")
			}
		})
	}
	// Mixed-width arithmetic can still be proved when the identical operand
	// views survive on both sides of each case.
	y2 := &term{kind: termParam, name: "y", width: 2, declared: 4}
	left, right := structuralControlDistribution(4, g, x2, y2, structuralControlConst(1, 4))
	// Keep the conditional at the narrow view's width on the factored side;
	// the other side's arithmetic performs the same explicit adaptation.
	left.left.width = 2
	s := newStructuralCases(structuralControlLimits())
	if !s.equal(left, right) || s.leaves != 2 {
		t.Fatalf("safe mixed-width proof must close both cofactors, got %d leaves", s.leaves)
	}
	if !structuralControlBDDEqual(t, left, right, []string{"g", "x", "y"}, map[string]int{"g": 1, "x": 4, "y": 4}) {
		t.Fatal("accepted mixed-width case was not BDD equal")
	}
	for xv := uint64(0); xv < 16; xv++ {
		for yv := uint64(0); yv < 16; yv++ {
			for gv := uint64(0); gv < 2; gv++ {
				env := map[string]uint64{"x": xv, "y": yv, "g": gv}
				if left.eval(env) != right.eval(env) {
					t.Fatal("accepted mixed-width cofactors disagree under exhaustive evaluation")
				}
			}
		}
	}
}

func TestStructuralCasesRejectMalformedAndUnsupported(t *testing.T) {
	x := structuralControlParam("x", 4)
	badCycle := structuralControlBinary("add", 4, x, nil)
	badCycle.right = badCycle
	first, second := structuralControlITE(4, structuralControlParam("g", 1), x, nil), structuralControlBinary("xor", 4, x, nil)
	first.right, second.right = second, first
	tests := map[string]*term{
		"nil":                   nil,
		"zero width":            {kind: termParam, width: 0},
		"negative width":        {kind: termParam, width: -1},
		"oversized width":       {kind: termParam, width: 65},
		"negative declaration":  {kind: termParam, width: 4, declared: -1},
		"oversized declaration": {kind: termParam, width: 4, declared: 65},
		"unmasked constant":     {kind: termConst, width: 4, value: 16},
		"parameter child":       {kind: termParam, width: 4, left: x},
		"constant child":        {kind: termConst, width: 4, right: x},
		"unexpected arguments":  {kind: termParam, width: 4, args: []*term{x}},
		"missing binary child":  structuralControlBinary("add", 4, x, nil),
		"unknown binary":        structuralControlBinary("mystery", 4, x, x),
		"binary condition":      {kind: termBinary, op: "add", width: 4, left: x, right: x, cond: x},
		"unknown comparison":    structuralControlCmp("mystery", x, x),
		"always comparison":     structuralControlCmp("al", x, x),
		"never comparison":      structuralControlCmp("nv", x, x),
		"comparison widths":     structuralControlCmp("eq", x, structuralControlParam("y", 2)),
		"missing ITE condition": structuralControlITE(4, nil, x, x),
		"wide ITE condition":    structuralControlITE(4, x, x, x),
		"missing ITE arm":       structuralControlITE(4, structuralControlParam("g", 1), x, nil),
		"missing read index":    structuralControlRead("memory", nil, 4),
		"extra read operand":    {kind: termSelect, name: "memory", width: 4, left: x, right: x},
		"floating operation":    {kind: termFloat, op: "fadd", width: 4, left: x, right: x},
		"application":           {kind: termApply, name: "f", width: 4, args: []*term{x}},
		"quantifier":            {kind: termQuant, op: "forall", name: "q", width: 1, value: 4, left: x, right: x},
		"unknown kind":          {kind: termKind(255), width: 4},
		"self cycle":            badCycle,
		"two-node cycle":        first,
	}
	for _, op := range []string{"shl", "shr", "sar"} {
		tests[op+" non-power-of-two width"] = structuralControlBinary(op, 3, structuralControlParam("a", 3), structuralControlParam("b", 3))
		tests[op+" left width mismatch"] = structuralControlBinary(op, 4, structuralControlParam("a", 2), x)
		tests[op+" right width mismatch"] = structuralControlBinary(op, 4, x, structuralControlParam("b", 2))
	}
	for name, root := range tests {
		t.Run(name, func(t *testing.T) {
			if structurallyEqualByCases(root, root) {
				t.Fatal("pointer identity bypassed admitted-term validation")
			}
			if root != nil {
				// Even an unreachable malformed/unsupported arm must be
				// rejected before normalization can discard it.
				dead := structuralControlITE(4, structuralControlConst(0, 1), root, x)
				if structurallyEqualByCases(dead, x) {
					t.Fatal("normalization hid an unsupported or malformed arm")
				}
			}
		})
	}
}

func TestStructuralCasesExactInternerKeys(t *testing.T) {
	s := newStructuralCases(structuralControlLimits())
	base := structuralCaseNode{kind: termSelect, width: 32, declared: 16, op: "op", name: "span\x00:index", value: 7, cond: -1, left: 2, right: -1}
	keys := []structuralCaseNode{base}
	for field := 0; field < 9; field++ {
		changed := base
		switch field {
		case 0:
			changed.kind = termParam
		case 1:
			changed.width++
		case 2:
			changed.declared++
		case 3:
			changed.op += "\x00"
		case 4:
			changed.name += "\x00"
		case 5:
			changed.value++
		case 6:
			changed.cond++
		case 7:
			changed.left++
		case 8:
			changed.right++
		}
		keys = append(keys, changed)
	}
	ids := map[int]bool{}
	for _, key := range keys {
		id := s.put(key)
		if id < 0 || ids[id] || s.put(key) != id || s.nodes[id] != key {
			t.Fatal("interner did not preserve a complete exact comparable key")
		}
		ids[id] = true
	}
	// Separators in strings cannot turn two structured keys into one key.
	a, b := base, base
	a.op, a.name = "a:b", "c"
	b.op, b.name = "a", "b:c"
	if s.put(a) == s.put(b) {
		t.Fatal("string concatenation was used in place of exact field identity")
	}
}

func TestStructuralCasesResourceLimitsFailClosed(t *testing.T) {
	g := structuralControlParam("g", 1)
	x, y, z := structuralControlParam("x", 4), structuralControlParam("y", 4), structuralControlParam("z", 4)
	left, right := structuralControlDistribution(4, g, x, y, z)
	baseline := newStructuralCases(structuralControlLimits())
	if !baseline.equal(left, right) || baseline.leaves != 2 {
		t.Fatal("resource control must first prove both leaves without exhaustion")
	}
	for _, resource := range []string{"inputs", "nodes", "work", "depth"} {
		t.Run(resource, func(t *testing.T) {
			limits := structuralControlLimits()
			a, b := left, right
			switch resource {
			case "inputs":
				// Source admission precedes all leaves; unlike the other
				// bounds, this cap cannot first fire after a successful leaf.
				limits.inputs = 3
			case "nodes":
				limits.nodes = len(baseline.nodes) - 1
			case "work":
				limits.work = baseline.work - 1
			case "depth":
				h := structuralControlParam("h", 1)
				nested := structuralControlITE(4, g, x, y)
				a, b = structuralControlDistribution(4, h, nested, z, z)
				b.left = structuralControlITE(4, g,
					structuralControlBinary("add", 4, x, z), structuralControlBinary("add", 4, y, z))
				limits.depth = 1
			}
			s := newStructuralCases(limits)
			if s.equal(a, b) {
				t.Fatal("resource exhaustion produced a partial proof")
			}
			if resource == "inputs" {
				if s.leaves != 0 {
					t.Fatal("source-input admission should fail before case leaves")
				}
			} else if s.leaves != 1 {
				t.Fatalf("control must exhaust after exactly one successful leaf, got %d", s.leaves)
			}
			if s.equal(x, y) || structurallyEqualByCases(x, y) {
				t.Fatal("failed query contaminated a later unequal query")
			}
			if !structurallyEqualByCases(left, right) {
				t.Fatal("failed query contaminated a fresh complete proof")
			}
		})
	}
	for _, limits := range []structuralCaseLimits{
		{inputs: 0, nodes: 8192, work: 131072, depth: 4},
		{inputs: 4096, nodes: 0, work: 131072, depth: 4},
		{inputs: 4096, nodes: 8192, work: 0, depth: 4},
		{inputs: 4096, nodes: 8192, work: 131072, depth: 0},
	} {
		if newStructuralCases(limits).equal(left, right) {
			t.Fatal("zero resource cap accepted a case proof")
		}
	}
}

func structuralControlSnapshot(roots ...*term) map[*term]term {
	seen := map[*term]term{}
	stack := append([]*term(nil), roots...)
	for len(stack) > 0 {
		node := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if node == nil {
			continue
		}
		if _, exists := seen[node]; exists {
			continue
		}
		copy := *node
		if node.args != nil {
			copy.args = append([]*term{}, node.args...)
		}
		seen[node] = copy
		stack = append(stack, node.left, node.right, node.cond)
		stack = append(stack, node.args...)
	}
	return seen
}

func structuralControlUnchanged(t *testing.T, before map[*term]term) {
	t.Helper()
	for node, snapshot := range before {
		if !reflect.DeepEqual(*node, snapshot) {
			t.Fatalf("checker mutated an input node (kind=%d width=%d declared=%d id=%d sigBits=%d)", snapshot.kind, snapshot.width, snapshot.declared, snapshot.id, snapshot.sigBits)
		}
	}
}

func TestStructuralCasesInputNonmutation(t *testing.T) {
	g, x, y := structuralControlParam("g", 1), structuralControlParam("x", 4), structuralControlParam("y", 4)
	x.id, x.sigBits, x.declared = 17, 3, 2
	read := structuralControlRead("words", structuralControlParam("i", 32), 4)
	left, right := structuralControlDistribution(4, g, x, y, read)
	before := structuralControlSnapshot(left, right)
	if !structurallyEqualByCases(left, right) {
		t.Fatal("nonmutation control did not prove")
	}
	structuralControlUnchanged(t, before)
	limited := structuralControlLimits()
	limited.work = 20
	if newStructuralCases(limited).equal(left, right) {
		t.Fatal("nonmutation failure control unexpectedly proved")
	}
	structuralControlUnchanged(t, before)
}

func TestStructuralCasesConcurrentColdSharedDAG(t *testing.T) {
	for range 4 {
		g, x, y := structuralControlParam("g", 1), structuralControlParam("x", 32), structuralControlParam("y", 32)
		shared := structuralControlBinary("and", 32, x, structuralControlConst(255, 32))
		for range 96 {
			shared = structuralControlBinary("or", 32, shared, shared)
		}
		left, right := structuralControlDistribution(32, g, shared, x, y)
		before := structuralControlSnapshot(left, right)
		start := make(chan struct{})
		var workers sync.WaitGroup
		for range 8 {
			workers.Go(func() {
				<-start
				if !structurallyEqualByCases(left, right) {
					t.Error("concurrent cold shared-DAG proof failed")
				}
			})
		}
		close(start)
		workers.Wait()
		structuralControlUnchanged(t, before)
	}
}

func TestStructuralCasesExhaustiveSmallWidths(t *testing.T) {
	accepted, refuted := 0, 0
	for _, width := range []int{1, 2, 3, 4} {
		x, y, g := structuralControlParam("x", width), structuralControlParam("y", width), structuralControlParam("g", 1)
		constant := structuralControlConst(mask(width), width)
		guards := []*term{g, structuralControlCmp("eq", x, y), structuralControlCmp("lt", x, y)}
		for _, op := range []string{"add", "sub", "mul", "and", "or", "xor", "shl", "shr", "sar"} {
			if width == 3 && (op == "shl" || op == "shr" || op == "sar") {
				continue // rejected explicitly in the malformed-domain controls
			}
			for guardIndex, guard := range guards {
				for _, changed := range []bool{false, true} {
					name := fmt.Sprintf("width%d/%s/guard%d/changed%v", width, op, guardIndex, changed)
					t.Run(name, func(t *testing.T) {
						binary := func(a *term) *term { return structuralControlBinary(op, width, a, y) }
						left := binary(structuralControlITE(width, guard, x, constant))
						trueArm := binary(x)
						if changed {
							trueArm = structuralControlBinary("xor", width, trueArm, structuralControlConst(1, width))
						}
						right := structuralControlITE(width, guard, trueArm, binary(constant))
						proof := structurallyEqualByCases(left, right)
						if !changed && !proof {
							t.Fatal("non-vacuous distributive positive control was not accepted")
						}
						if changed && proof {
							t.Fatal("changed reachable arm was accepted")
						}
						allEqual := true
						env := map[string]uint64{}
						for xv := uint64(0); xv <= mask(width); xv++ {
							for yv := uint64(0); yv <= mask(width); yv++ {
								for gv := uint64(0); gv < 2; gv++ {
									env["x"], env["y"], env["g"] = xv, yv, gv
									if left.eval(env) != right.eval(env) {
										allEqual = false
										if proof {
											t.Fatalf("accepted proof has counterexample x=%d y=%d g=%d", xv, yv, gv)
										}
									}
								}
							}
						}
						bddEqual := structuralControlBDDEqual(t, left, right, []string{"g", "x", "y"}, map[string]int{"g": 1, "x": width, "y": width})
						if bddEqual != allEqual || proof && !bddEqual || changed && allEqual {
							t.Fatalf("oracles disagree: proof=%v BDD=%v exhaustive=%v", proof, bddEqual, allEqual)
						}
						if proof {
							accepted++
						} else {
							refuted++
						}
					})
				}
			}
		}
		// Cover all admitted flag conditions, including overflow and signed
		// comparisons, with both constant folds and symbolic case guards.
		for _, op := range []string{"eq", "ne", "hs", "cs", "lo", "cc", "hi", "ls", "ge", "lt", "gt", "le", "mi", "pl", "vs", "vc"} {
			t.Run(fmt.Sprintf("width%d/condition/%s", width, op), func(t *testing.T) {
				guard := structuralControlCmp(op, x, y)
				left, right := structuralControlDistribution(width, guard, x, y, constant)
				if !structurallyEqualByCases(left, right) || !structuralControlBDDEqual(t, left, right, []string{"x", "y"}, map[string]int{"x": width, "y": width}) {
					t.Fatal("symbolic comparison guard did not preserve equality")
				}
				for xv := uint64(0); xv <= mask(width); xv++ {
					for yv := uint64(0); yv <= mask(width); yv++ {
						env := map[string]uint64{"x": xv, "y": yv}
						if left.eval(env) != right.eval(env) {
							t.Fatal("accepted symbolic comparison case failed exhaustive evaluation")
						}
						folded := structuralControlCmp(op, structuralControlConst(xv, width), structuralControlConst(yv, width))
						value := structuralControlConst(guard.eval(env), 1)
						if !structurallyEqualByCases(folded, value) || !structuralControlBDDEqual(t, folded, value, nil, nil) {
							t.Fatalf("constant condition fold disagrees with evaluator/BDD at x=%d y=%d", xv, yv)
						}
					}
				}
			})
		}
	}
	if accepted < 90 || refuted < 90 {
		t.Fatalf("exhaustive corpus lost its positive or negative controls: accepted=%d refuted=%d", accepted, refuted)
	}
}

func TestStructuralCasesConstantFoldingDifferential(t *testing.T) {
	check := func(t *testing.T, op string, width, leftWidth, rightWidth int, leftValue, rightValue uint64) {
		t.Helper()
		left := structuralControlConst(leftValue, leftWidth)
		right := structuralControlConst(rightValue, rightWidth)
		root := structuralControlBinary(op, width, left, right)
		want := evalBinary(op, left.value&mask(width), right.value&mask(width), width)
		if got := root.eval(nil); got != want {
			t.Fatalf("raw %s at width %d with operand widths %d/%d: evaluator=%#x binary=%#x", op, width, leftWidth, rightWidth, got, want)
		}
		result := structuralControlConst(want, width)
		if !structurallyEqualByCases(root, result) {
			t.Fatalf("constant %s did not fold: result width=%d operands=%#x/%d,%#x/%d", op, width, left.value, leftWidth, right.value, rightWidth)
		}
		if !structuralControlBDDEqual(t, root, result, nil, nil) {
			t.Fatalf("accepted constant %s disagrees with actual BDD: width=%d operands=%#x/%d,%#x/%d result=%#x", op, width, left.value, leftWidth, right.value, rightWidth, want)
		}
		if structurallyEqualByCases(root, structuralControlConst(want^1, width)) {
			t.Fatal("constant folding accepted a changed result")
		}
	}
	ops := []string{"add", "sub", "mul", "and", "or", "xor", "shl", "shr", "sar"}
	for _, width := range []int{1, 2, 3, 4} {
		for _, op := range ops {
			if width == 3 && (op == "shl" || op == "shr" || op == "sar") {
				continue
			}
			t.Run(fmt.Sprintf("exhaustive/width%d/%s", width, op), func(t *testing.T) {
				for left := uint64(0); left <= mask(width); left++ {
					for right := uint64(0); right <= mask(width); right++ {
						check(t, op, width, width, width, left, right)
					}
				}
			})
		}
	}
	for _, width := range []int{1, 2, 4} {
		for _, op := range ops[:6] {
			t.Run(fmt.Sprintf("mixed/width%d/%s", width, op), func(t *testing.T) {
				for _, leftWidth := range []int{1, 2, 4} {
					for _, rightWidth := range []int{1, 2, 4} {
						for _, left := range []uint64{0, 1, uint64(1) << (leftWidth - 1), mask(leftWidth)} {
							for _, right := range []uint64{0, 1, uint64(1) << (rightWidth - 1), mask(rightWidth)} {
								check(t, op, width, leftWidth, rightWidth, left, right)
							}
						}
					}
				}
			})
		}
	}
	for _, width := range []int{32, 64} {
		sign := uint64(1) << (width - 1)
		corners := []uint64{0, 1, 2, uint64(width - 1), uint64(width), uint64(width + 1), sign - 1, sign, sign + 1, mask(width) - 1, mask(width)}
		for _, op := range ops {
			t.Run(fmt.Sprintf("corners/width%d/%s", width, op), func(t *testing.T) {
				for _, left := range corners {
					for _, right := range corners {
						check(t, op, width, width, width, left, right)
					}
				}
			})
		}
	}
}
