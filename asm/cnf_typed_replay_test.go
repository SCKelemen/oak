package asm

import (
	"context"
	"errors"
	"fmt"
	"math/rand"
	"strings"
	"sync"
	"testing"
)

func typedCNFBinary(op string, w int, a, b *term) *term {
	return &term{kind: termBinary, width: w, op: op, left: a, right: b}
}
func typedCNFCompare(op string, w int, a, b *term) *term {
	return &term{kind: termCmp, width: w, op: op, left: a, right: b}
}
func typedCNFParam(name string, w, d int) *term {
	return &term{kind: termParam, width: w, declared: d, name: name}
}
func typedCNFConst(w int, v uint64) *term { return &term{kind: termConst, width: w, value: v} }
func typedCNFRead(span string, index *term) *term {
	return &term{kind: termSelect, width: 32, name: span, left: index}
}
func typedCNFProduce(p, l, r *term, names []string, widths map[string]int) (*blaster, *term, [][]int) {
	claim := &term{kind: termIte, width: 1, cond: p, left: typedCNFCompare("eq", 1, l, r), right: typedCNFConst(1, 1)}
	bl := newCNFBlaster(names, widths)
	bits := bl.blast(claim)
	if len(bits) != 1 {
		panic("test producer failed")
	}
	clauses := append(append([][]int(nil), bl.cnf.clauses...), []int{cnfLit(bits[0] ^ 1)})
	return bl, claim, clauses
}
func typedCNFDIMACS(label string, variables int, clauses [][]int) string {
	var b strings.Builder
	fmt.Fprintf(&b, "c %s\np cnf %d %d\n", label, variables, len(clauses))
	for _, clause := range clauses {
		for _, lit := range clause {
			fmt.Fprintf(&b, "%d ", lit)
		}
		b.WriteString("0\n")
	}
	return b.String()
}

// Independent word arithmetic and total-memory evaluation for finite
// correspondence controls. This is not used by replay to accept a formula.
func typedCNFValue(t *term, env map[string]uint64, memory func(string, uint32) uint32, memo map[*term]uint64) uint64 {
	if v, ok := memo[t]; ok {
		return v
	}
	var v uint64
	child := func(t *term) uint64 { return typedCNFValue(t, env, memory, memo) }
	switch t.kind {
	case termConst:
		v = t.value
	case termParam:
		v = env[t.name] & mask(t.declaredWidth())
	case termSelect:
		v = uint64(memory(t.name, uint32(child(t.left))))
	case termIte:
		if child(t.cond) != 0 {
			v = child(t.left)
		} else {
			v = child(t.right)
		}
	case termCmp:
		a, b := child(t.left), child(t.right)
		holds := false
		switch t.op {
		case "eq":
			holds = a == b
		case "ne":
			holds = a != b
		case "lo":
			holds = a < b
		case "hs":
			holds = a >= b
		}
		if holds {
			v = 1
		}
	case termBinary:
		a, b := child(t.left)&mask(t.width), child(t.right)&mask(t.width)
		switch t.op {
		case "add":
			v = a + b
		case "sub":
			v = a - b
		case "and":
			v = a & b
		case "or":
			v = a | b
		case "xor":
			v = a ^ b
		case "shl":
			v = a << uint(b%uint64(t.width))
		case "shr":
			v = a >> uint(b%uint64(t.width))
		}
	}
	v &= mask(t.width)
	memo[t] = v
	return v
}
func typedCNFCheckValues(a typedCNFAudit, env map[string]uint64, memory func(string, uint32) uint32) error {
	bl := a.snapshot
	values := map[int]bool{}
	memo := map[*term]uint64{}
	for source, owner := range bl.owners {
		values[bl.cnf.inputs[source]] = env[owner.param]>>uint(owner.bit)&1 != 0
	}
	for _, read := range bl.selects {
		word := memory(read.span, uint32(typedCNFValue(read.index, env, memory, memo)))
		for bit, source := range read.vars {
			values[bl.cnf.inputs[source]] = word>>uint(bit)&1 != 0
		}
	}
	edge := func(e int) bool {
		if e < 2 {
			return e == 1
		}
		return values[e>>1] != (e&1 != 0)
	}
	for _, gate := range bl.cnf.gates {
		var v bool
		switch gate.op {
		case opAnd:
			v = edge(gate.x) && edge(gate.y)
		case opOr:
			v = edge(gate.x) || edge(gate.y)
		case opXor:
			v = edge(gate.x) != edge(gate.y)
		case cnfIte:
			if edge(gate.x) {
				v = edge(gate.y)
			} else {
				v = edge(gate.z)
			}
		}
		values[gate.out] = v
	}
	for term, bits := range bl.memo {
		want := typedCNFValue(term, env, memory, memo)
		for bit, root := range bits {
			if edge(root) != (want>>uint(bit)&1 != 0) {
				return fmt.Errorf("typed node kind=%d op=%s width=%d bit=%d", term.kind, term.op, term.width, bit)
			}
		}
	}
	p, l, r := a.roots[0], a.roots[1], a.roots[2]
	violation := typedCNFValue(p, env, memory, memo) != 0 && typedCNFValue(l, env, memory, memo) != typedCNFValue(r, env, memory, memo)
	if edge(a.Obligation) != violation {
		return fmt.Errorf("implication polarity")
	}
	return nil
}
func typedCNFMemory(span string, index uint32) uint32 {
	if span == "other" {
		return index ^ 0xa5a5a5a5
	}
	return index*0x9e3779b9 + 0x13579bdf
}

func TestTypedCNFArithmeticWidths(t *testing.T) {
	for _, w := range []int{1, 2, 4, 8, 16, 32, 64} {
		for _, op := range []string{"and", "or", "xor", "add", "sub", "eq", "ne", "lo", "hs"} {
			t.Run(fmt.Sprintf("%s%d", op, w), func(t *testing.T) {
				x, y, z := typedCNFParam("x", w, w), typedCNFParam("y", w, w), typedCNFParam("z", w, w)
				p := typedCNFConst(1, 1)
				left := typedCNFBinary(op, w, x, y)
				if op == "eq" || op == "ne" || op == "lo" || op == "hs" {
					left = typedCNFCompare(op, w, x, y)
				}
				bl, claim, clauses := typedCNFProduce(p, left, z, []string{"x", "y", "z"}, map[string]int{"x": w, "y": w, "z": w})
				audit, err := checkTypedCNFImplication(context.Background(), bl, p, left, z, claim, clauses, typedCNFDiagnosticLimits)
				if err != nil {
					t.Fatal(err)
				}
				rng := rand.New(rand.NewSource(1))
				for i := 0; i < 40; i++ {
					env := map[string]uint64{"x": rng.Uint64(), "y": rng.Uint64(), "z": rng.Uint64()}
					if i < 4 {
						env["x"] = []uint64{0, 1, mask(w), uint64(1) << uint(w-1)}[i]
						env["y"] = 1
					}
					if err := typedCNFCheckValues(audit, env, typedCNFMemory); err != nil {
						t.Fatal(err)
					}
				}
			})
		}
	}
}
func TestTypedCNFViewsShiftsAndGuards(t *testing.T) {
	for _, w := range []int{32, 64} {
		for _, op := range []string{"shl", "shr"} {
			for _, constant := range []bool{false, true} {
				t.Run(fmt.Sprintf("%s%d_const%t", op, w, constant), func(t *testing.T) {
					x, c, z := typedCNFParam("x", w, 32), typedCNFParam("count", w, 64), typedCNFParam("z", w, w)
					names := []string{"x", "count", "z"}
					widths := map[string]int{"x": 32, "count": 64, "z": w}
					if constant {
						c = typedCNFConst(64, 65)
						names = []string{"x", "z"}
						delete(widths, "count")
					}
					left := typedCNFBinary(op, w, x, c)
					p := typedCNFConst(1, 1)
					bl, claim, clauses := typedCNFProduce(p, left, z, names, widths)
					audit, err := checkTypedCNFImplication(context.Background(), bl, p, left, z, claim, clauses, typedCNFDiagnosticLimits)
					if err != nil {
						t.Fatal(err)
					}
					for _, count := range []uint64{0, 1, 31, 32, 33, 63, 64, 65, ^uint64(0)} {
						env := map[string]uint64{"x": 0x8123456789abcdef, "count": count, "z": 17}
						if err := typedCNFCheckValues(audit, env, typedCNFMemory); err != nil {
							t.Fatal(err)
						}
					}
				})
			}
		}
	}
	t.Run("sub32-before-widen64", func(t *testing.T) {
		x, z := typedCNFParam("x", 32, 32), typedCNFParam("z", 64, 64)
		p := typedCNFConst(1, 1)
		left := typedCNFBinary("and", 64, typedCNFBinary("sub", 32, x, typedCNFConst(32, 1)), typedCNFConst(64, 0xffffffff))
		bl, claim, clauses := typedCNFProduce(p, left, z, []string{"x", "z"}, map[string]int{"x": 32, "z": 64})
		audit, err := checkTypedCNFImplication(context.Background(), bl, p, left, z, claim, clauses, typedCNFDiagnosticLimits)
		if err != nil {
			t.Fatal(err)
		}
		if err := typedCNFCheckValues(audit, map[string]uint64{"x": 0, "z": 0xffffffff}, typedCNFMemory); err != nil {
			t.Fatal(err)
		}
	})
	for _, guardKind := range []string{"view", "compare"} {
		t.Run("wide-guard-"+guardKind, func(t *testing.T) {
			x, z := typedCNFParam("x", 32, 32), typedCNFParam("z", 32, 32)
			g := typedCNFParam("g", 64, 1)
			names := []string{"x", "z", "g"}
			widths := map[string]int{"x": 32, "z": 32, "g": 1}
			if guardKind == "compare" {
				g = typedCNFCompare("lo", 64, x, z)
				names = []string{"x", "z"}
				delete(widths, "g")
			}
			p := typedCNFConst(1, 1)
			left := &term{kind: termIte, width: 32, cond: g, left: x, right: typedCNFConst(32, 7)}
			bl, claim, clauses := typedCNFProduce(p, left, z, names, widths)
			audit, err := checkTypedCNFImplication(context.Background(), bl, p, left, z, claim, clauses, typedCNFDiagnosticLimits)
			if err != nil {
				t.Fatal(err)
			}
			for _, gv := range []uint64{0, 1, ^uint64(0)} {
				if err := typedCNFCheckValues(audit, map[string]uint64{"x": 6, "z": 8, "g": gv}, typedCNFMemory); err != nil {
					t.Fatal(err)
				}
			}
		})
	}
}
func TestTypedCNFReadEmbedding(t *testing.T) {
	typedCNFOverflowReads(t)
	s, b, q, z := typedCNFParam("s", 32, 32), typedCNFParam("b", 32, 32), typedCNFParam("q", 32, 32), typedCNFParam("z", 32, 32)
	idx := typedCNFBinary("add", 32, s, typedCNFConst(32, 9))
	first := typedCNFRead("mem", idx)
	duplicate := typedCNFRead("mem", typedCNFBinary("add", 32, typedCNFParam("s", 32, 32), typedCNFConst(32, 9)))
	dependent := typedCNFRead("mem", typedCNFBinary("add", 32, b, typedCNFBinary("shr", 32, first, typedCNFConst(32, 2))))
	left := typedCNFBinary("xor", 32, typedCNFBinary("add", 32, first, duplicate), typedCNFBinary("xor", 32, dependent, typedCNFRead("mem", q)))
	p := typedCNFConst(1, 1)
	bl, claim, clauses := typedCNFProduce(p, left, z, []string{"s", "b", "q", "z"}, map[string]int{"s": 32, "b": 32, "q": 32, "z": 32})
	audit, err := checkTypedCNFImplication(context.Background(), bl, p, left, z, claim, clauses, typedCNFDiagnosticLimits)
	if err != nil {
		t.Fatal(err)
	}
	if audit.ReadBlocks != 3 {
		t.Fatalf("read blocks=%d", audit.ReadBlocks)
	}
	for _, sv := range []uint64{0, 1, 0xfffffff7, 0xffffffff} {
		for _, qv := range []uint64{sv, uint64(uint32(sv + 9)), 17} {
			if err := typedCNFCheckValues(audit, map[string]uint64{"s": sv, "b": 0xfffffff0, "q": qv, "z": 19}, typedCNFMemory); err != nil {
				t.Fatal(err)
			}
		}
	}
	// Ownership remains isolated after producer mutation, including nested roots.
	bl.params[0] = "changed"
	bl.memo[left][0] ^= 1
	idx.op = "sub"
	bl.selects[0].vars[0] = -1
	bl.cnf.gates[0].x = -1
	if err := typedCNFCheckValues(audit, map[string]uint64{"s": 1, "b": 2, "q": 10, "z": 3}, typedCNFMemory); err != nil {
		t.Fatalf("snapshot shares mutable producer data: %v", err)
	}
}
func TestTypedCNFAdversarial(t *testing.T) {
	typedCNFReadRefusals(t)
	type fixture struct {
		bl             *blaster
		p, l, r, claim *term
		clauses        [][]int
	}
	fresh := func() fixture {
		x, y, z := typedCNFParam("x", 32, 32), typedCNFParam("y", 32, 32), typedCNFParam("z", 32, 32)
		p := typedCNFConst(1, 1)
		l := typedCNFBinary("add", 32, x, y)
		bl, c, clauses := typedCNFProduce(p, l, z, []string{"x", "y", "z"}, map[string]int{"x": 32, "y": 32, "z": 32})
		return fixture{bl, p, l, z, c, clauses}
	}
	controls := []struct {
		name, want string
		mutate     func(*fixture)
	}{
		{"term-root", "producer term memo", func(f *fixture) { f.bl.memo[f.l][0] ^= 1 }},
		{"gate-root", "gate memo", func(f *fixture) { g := f.bl.cnf.gates[0]; key, _ := cnfGateMemoKey(0, g); f.bl.cnf.memo[key]++ }},
		{"final-polarity", "final clause", func(f *fixture) { f.clauses[len(f.clauses)-1][0] *= -1 }},
		{"gate-clause", "clause", func(f *fixture) { f.bl.cnf.clauses[0][0] *= -1 }},
		{"declaration", "declared width", func(f *fixture) { f.l.left.declared = 16 }},
		{"negative-declaration", "term limit or shape", func(f *fixture) { f.l.left.declared = -1 }},
		{"missing-declaration", "declaration table shape", func(f *fixture) { delete(f.bl.widths, "x") }},
		{"constant-bits", "above its width", func(f *fixture) { f.p.value = 3 }},
		{"unsupported", "unsupported typed binary", func(f *fixture) { f.l.op = "mul" }},
		{"cycle", "cyclic graph", func(f *fixture) { f.l.left = f.l }},
		{"wrapper", "exact implication wrapper", func(f *fixture) { f.claim.left.op = "ne" }},
		{"extra-memo", "unreachable producer term", func(f *fixture) { f.bl.memo[typedCNFConst(1, 0)] = []int{0} }},
		{"owner", "invalid owner binding", func(f *fixture) { f.bl.owners[0] = variableOwner{"z", 63} }},
	}
	for _, control := range controls {
		t.Run(control.name, func(t *testing.T) {
			f := fresh()
			control.mutate(&f)
			_, err := checkTypedCNFImplication(context.Background(), f.bl, f.p, f.l, f.r, f.claim, f.clauses, typedCNFDiagnosticLimits)
			if err == nil || !strings.Contains(err.Error(), control.want) {
				t.Fatalf("got %v, want refusal %q", err, control.want)
			}
		})
	}
	t.Run("nonboolean-guard", func(t *testing.T) {
		f := fresh()
		g := typedCNFParam("x", 32, 32)
		f.l = &term{kind: termIte, width: 32, cond: g, left: f.l, right: typedCNFConst(32, 7)}
		f.bl, f.claim, f.clauses = typedCNFProduce(f.p, f.l, f.r, []string{"x", "y", "z"}, map[string]int{"x": 32, "y": 32, "z": 32})
		_, err := checkTypedCNFImplication(context.Background(), f.bl, f.p, f.l, f.r, f.claim, f.clauses, typedCNFDiagnosticLimits)
		if err == nil || !strings.Contains(err.Error(), "zero/one") {
			t.Fatal(err)
		}
	})
	t.Run("linear-only-read-merge", func(t *testing.T) {
		x, y, z := typedCNFParam("x", 32, 32), typedCNFParam("y", 32, 32), typedCNFParam("z", 32, 32)
		a := typedCNFRead("m", typedCNFBinary("add", 32, x, y))
		b := typedCNFRead("m", typedCNFBinary("add", 32, y, x))
		l := typedCNFBinary("add", 32, a, b)
		p := typedCNFConst(1, 1)
		bl, c, clauses := typedCNFProduce(p, l, z, []string{"x", "y", "z"}, map[string]int{"x": 32, "y": 32, "z": 32})
		_, err := checkTypedCNFImplication(context.Background(), bl, p, l, z, c, clauses, typedCNFDiagnosticLimits)
		if err == nil || !strings.Contains(err.Error(), "complete structural identity") {
			t.Fatal(err)
		}
	})
}
func TestTypedCNFLimitsAndConcurrentCalls(t *testing.T) {
	x, z := typedCNFParam("x", 32, 32), typedCNFParam("z", 32, 32)
	p := typedCNFConst(1, 1)
	l := typedCNFBinary("sub", 32, x, typedCNFConst(32, 1))
	bl, c, clauses := typedCNFProduce(p, l, z, []string{"x", "z"}, map[string]int{"x": 32, "z": 32})
	typedCNFExactLimits(t, bl, p, l, z, c, clauses)
	limited := typedCNFDiagnosticLimits
	limited.Visits = 1
	if _, err := checkTypedCNFImplication(context.Background(), bl, p, l, z, c, clauses, limited); !errors.Is(err, errTypedCNFResource) {
		t.Fatalf("limit: %v", err)
	}
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	if _, err := checkTypedCNFImplication(ctx, bl, p, l, z, c, clauses, typedCNFDiagnosticLimits); !errors.Is(err, context.Canceled) {
		t.Fatalf("cancel: %v", err)
	}
	var wg sync.WaitGroup
	errs := make(chan error, 4)
	for i := 0; i < 4; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			_, err := checkTypedCNFImplication(context.Background(), bl, p, l, z, c, clauses, typedCNFDiagnosticLimits)
			errs <- err
		}()
	}
	wg.Wait()
	close(errs)
	for err := range errs {
		if err != nil {
			t.Fatal(err)
		}
	}
}

type typedCNFCancelAt struct {
	context.Context
	cancel    context.CancelFunc
	at, calls int
}

func (c *typedCNFCancelAt) Err() error {
	c.calls++
	if c.at > 0 && c.calls == c.at {
		c.cancel()
	}
	return c.Context.Err()
}
func typedCNFExactLimits(t *testing.T, bl *blaster, p, l, z, c *term, clauses [][]int) {
	t.Helper()
	baseline, err := checkTypedCNFImplication(context.Background(), bl, p, l, z, c, clauses, typedCNFDiagnosticLimits)
	if err != nil {
		t.Fatal(err)
	}
	exact := typedCNFDiagnosticLimits
	exact.Visits = baseline.Visits
	if _, err := checkTypedCNFImplication(context.Background(), bl, p, l, z, c, clauses, exact); err != nil {
		t.Fatalf("exact visit budget: %v", err)
	}
	exact.Visits--
	if _, err := checkTypedCNFImplication(context.Background(), bl, p, l, z, c, clauses, exact); !errors.Is(err, errTypedCNFResource) {
		t.Fatalf("one fewer visit: %v", err)
	}
	for _, kind := range []string{"nodes", "gates", "variables"} {
		limit := typedCNFDiagnosticLimits
		switch kind {
		case "nodes":
			limit.Nodes = 1
		case "gates":
			limit.Gates = 1
		case "variables":
			limit.Variables = 1
		}
		if _, err := checkTypedCNFImplication(context.Background(), bl, p, l, z, c, clauses, limit); err == nil || !strings.Contains(err.Error(), "collection limit or shape") {
			t.Fatalf("%s limit: %v", kind, err)
		}
	}
	inner, stop := context.WithCancel(context.Background())
	counted := &typedCNFCancelAt{Context: inner, cancel: stop}
	if _, err := checkTypedCNFImplication(counted, bl, p, l, z, c, clauses, typedCNFDiagnosticLimits); err != nil {
		t.Fatal(err)
	}
	stop()
	for _, at := range []int{2, 10, 100, counted.calls} {
		inner, stop := context.WithCancel(context.Background())
		canceled := &typedCNFCancelAt{Context: inner, cancel: stop, at: at}
		_, err := checkTypedCNFImplication(canceled, bl, p, l, z, c, clauses, typedCNFDiagnosticLimits)
		stop()
		if !errors.Is(err, context.Canceled) {
			t.Fatalf("cancel at %d: %v", at, err)
		}
		if _, err := checkTypedCNFImplication(context.Background(), bl, p, l, z, c, clauses, typedCNFDiagnosticLimits); err != nil {
			t.Fatalf("after cancel %d: %v", at, err)
		}
	}
}
func typedCNFReadRefusals(t *testing.T) {
	t.Helper()
	t.Run("comparison-widths", func(t *testing.T) {
		x, y, z := typedCNFParam("x", 32, 32), typedCNFParam("y", 64, 32), typedCNFParam("z", 32, 32)
		p := typedCNFConst(1, 1)
		l := typedCNFCompare("lo", 32, x, y)
		bl, c, clauses := typedCNFProduce(p, l, z, []string{"x", "y", "z"}, map[string]int{"x": 32, "y": 32, "z": 32})
		_, err := checkTypedCNFImplication(context.Background(), bl, p, l, z, c, clauses, typedCNFDiagnosticLimits)
		if err == nil || !strings.Contains(err.Error(), "comparison operand widths differ") {
			t.Fatal(err)
		}
	})
	for _, kind := range []string{"index-root", "source-bit", "span", "index-width", "value-width", "mixed-value-width"} {
		t.Run("read-"+kind, func(t *testing.T) {
			x, z := typedCNFParam("x", 32, 32), typedCNFParam("z", 32, 32)
			read := typedCNFRead("memory", x)
			left := read
			names := []string{"x", "z"}
			widths := map[string]int{"x": 32, "z": 32}
			want := ""
			switch kind {
			case "index-width":
				read.left = typedCNFParam("x", 64, 32)
				want = "read requires exact span"
			case "value-width":
				read.width = 64
				z.width = 64
				z.declared = 64
				widths["z"] = 64
				want = "read block shape or index"
			case "mixed-value-width":
				first := typedCNFRead("memory", x)
				read.width = 16
				left = typedCNFBinary("add", 32, first, read)
				want = "read requires exact span"
			}
			premise := typedCNFConst(1, 1)
			producer, claim, clauses := typedCNFProduce(premise, left, z, names, widths)
			switch kind {
			case "index-root":
				producer.selects[0].idx = append([]int(nil), producer.selects[0].idx...)
				producer.selects[0].idx[0] ^= 1
				want = "read index roots differ"
			case "source-bit":
				producer.selects[0].vars[0]++
				want = "read source bit binding"
			case "span":
				producer.selects[0].span = "different"
				want = "complete structural identity"
			}
			_, err := checkTypedCNFImplication(context.Background(), producer, premise, left, z, claim, clauses, typedCNFDiagnosticLimits)
			if err == nil || !strings.Contains(err.Error(), want) {
				t.Fatalf("got %v want %s", err, want)
			}
		})
	}
}

func typedCNFOverflowReads(t *testing.T) {
	t.Helper()
	x, z := typedCNFParam("x", 32, 32), typedCNFParam("z", 32, 32)
	var left *term
	for slot := 0; slot < 9; slot++ {
		span := "memory"
		if slot%2 == 1 {
			span = "other"
		}
		read := typedCNFRead(span, typedCNFBinary("add", 32, x, typedCNFConst(32, uint64(slot))))
		if left == nil {
			left = read
		} else {
			left = typedCNFBinary("xor", 32, left, read)
		}
	}
	premise := typedCNFConst(1, 1)
	producer, claim, clauses := typedCNFProduce(premise, left, z, []string{"x", "z"}, map[string]int{"x": 32, "z": 32})
	audit, err := checkTypedCNFImplication(context.Background(), producer, premise, left, z, claim, clauses, typedCNFDiagnosticLimits)
	if err != nil {
		t.Fatal(err)
	}
	if audit.ReadBlocks != 9 {
		t.Fatalf("overflow read blocks=%d", audit.ReadBlocks)
	}
	for _, value := range []uint64{0, 1, 0xfffffff8, 0xffffffff} {
		if err := typedCNFCheckValues(audit, map[string]uint64{"x": value, "z": 17}, typedCNFMemory); err != nil {
			t.Fatal(err)
		}
	}
}
