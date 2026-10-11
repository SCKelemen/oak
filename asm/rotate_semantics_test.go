package asm

import (
	"fmt"
	"reflect"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
)

// rotateConsistencyReference is deliberately a bit-position permutation. It
// shares neither the scalar shift/or identity nor the staged barrel algorithm.
func rotateConsistencyReference(x, count uint64, width, dataWidth, countWidth int) uint64 {
	var data, adaptedCount uint64
	for bit := 0; bit < width; bit++ {
		if bit < dataWidth && x>>uint(bit)&1 != 0 {
			data |= uint64(1) << uint(bit)
		}
		if bit < countWidth && count>>uint(bit)&1 != 0 {
			adaptedCount |= uint64(1) << uint(bit)
		}
	}
	k := int(adaptedCount % uint64(width))
	var out uint64
	for bit := 0; bit < width; bit++ {
		if data>>uint((bit+k)%width)&1 != 0 {
			out |= uint64(1) << uint(bit)
		}
	}
	return out
}

func rotateConsistencyRaw(width int, data, count *term) *term {
	return &term{kind: termBinary, op: "ror", width: width, left: data, right: count}
}

// The ceiling is a fixture assertion, never an increase to a production budget.
const rotateConsistencyFixtureNodes = 8192

func rotateConsistencyRun(t *testing.T, name string, body func(*testing.T)) {
	t.Helper()
	if !t.Run(name, body) {
		t.FailNow()
	}
}

type rotateConsistencyCircuit struct {
	bdd, cnf         *blaster
	bddBits, cnfBits []int
	assignment       map[int]bool
	values           []bool
}

func rotateConsistencyCircuitFor(t *testing.T, root *term, names []string, widths map[string]int) *rotateConsistencyCircuit {
	t.Helper()
	seen := map[*term]bool{}
	var visit func(*term)
	visit = func(term *term) {
		if term == nil || seen[term] {
			return
		}
		seen[term] = true
		visit(term.left)
		visit(term.right)
		visit(term.cond)
		for _, arg := range term.args {
			visit(arg)
		}
	}
	visit(root)
	if len(seen) > rotateConsistencyFixtureNodes {
		t.Fatalf("fixture has %d terms", len(seen))
	}
	b, c := newBlaster(names, widths), newCNFBlaster(names, widths)
	bb, cb := b.blast(root), c.blast(root)
	if len(bb) != root.width || len(cb) != root.width || b.exceeded() || c.exceeded() {
		t.Fatalf("unexpected unknown: width=%d dataWidth=%d countWidth=%d BDDbits=%d CNFbits=%d", root.width, root.left.width, root.right.width, len(bb), len(cb))
	}
	if b.bdd.budget != blastNodeBudget || cnfClauseBudget != 50_000_000 {
		t.Fatal("production default budget changed")
	}
	if len(b.bdd.nodes) > rotateConsistencyFixtureNodes || len(c.cnf.gates) > rotateConsistencyFixtureNodes {
		t.Fatalf("unbounded fixture: BDD nodes=%d CNF gates=%d", len(b.bdd.nodes), len(c.cnf.gates))
	}
	return &rotateConsistencyCircuit{bdd: b, cnf: c, bddBits: bb, cnfBits: cb, assignment: map[int]bool{}, values: make([]bool, c.cnf.variables+1)}
}

func (c *rotateConsistencyCircuit) evaluate(t *testing.T, env map[string]uint64) (uint64, uint64) {
	t.Helper()
	bddWord, cnfWord, err := c.evaluateValues(env)
	if err != nil {
		t.Fatal(err)
	}
	return bddWord, cnfWord
}

func (c *rotateConsistencyCircuit) evaluateValues(env map[string]uint64) (uint64, uint64, error) {
	for variable, owner := range c.bdd.owners {
		c.assignment[variable] = env[owner.param]>>uint(owner.bit)&1 != 0
	}
	var bddWord uint64
	for bit, edge := range c.bddBits {
		if c.bdd.bdd.holdsUnder(edge, c.assignment) {
			bddWord |= uint64(1) << uint(bit)
		}
	}
	for variable, dimacs := range c.cnf.cnf.inputs {
		owner, ok := c.cnf.owners[variable]
		if !ok {
			return 0, 0, fmt.Errorf("unexpected abstract input %d in scalar fixture", variable)
		}
		c.values[dimacs] = env[owner.param]>>uint(owner.bit)&1 != 0
	}
	edgeValue := func(edge int) bool { return c.values[edge>>1] != (edge&1 != 0) }
	for _, gate := range c.cnf.cnf.gates {
		x, y := edgeValue(gate.x), edgeValue(gate.y)
		switch gate.op {
		case opAnd:
			c.values[gate.out] = x && y
		case opOr:
			c.values[gate.out] = x || y
		case opXor:
			c.values[gate.out] = x != y
		case cnfIte:
			if x {
				c.values[gate.out] = y
			} else {
				c.values[gate.out] = edgeValue(gate.z)
			}
		default:
			return 0, 0, fmt.Errorf("unknown CNF gate %d", gate.op)
		}
	}
	// Check every emitted definition as well as the complete output word.
	for number, clause := range c.cnf.cnf.clauses {
		satisfied := false
		for _, lit := range clause {
			v := lit
			if v < 0 {
				v = -v
			}
			if c.values[v] == (lit > 0) {
				satisfied = true
				break
			}
		}
		if !satisfied {
			return 0, 0, fmt.Errorf("CNF definition clause %d is false at %v", number, env)
		}
	}
	var cnfWord uint64
	for bit, edge := range c.cnfBits {
		if edgeValue(edge) {
			cnfWord |= uint64(1) << uint(bit)
		}
	}
	return bddWord, cnfWord, nil
}

func rotateConsistencyCheck(t *testing.T, label string, root *term, evaluator *termEvaluator, circuit *rotateConsistencyCircuit, env map[string]uint64, want uint64) {
	t.Helper()
	gotMap, gotSlot := root.eval(env), evaluator.evaluate(root, env)
	gotBDD, gotCNF := circuit.evaluate(t, env)
	if gotMap != want || gotSlot != want || gotBDD != want || gotCNF != want {
		t.Fatalf("%s W=%d childWidths=(%d,%d) declared=%v env=%v: map=%#x slot=%#x BDD=%#x CNF=%#x want=%#x", label, root.width, root.left.width, root.right.width, circuit.bdd.widths, env, gotMap, gotSlot, gotBDD, gotCNF, want)
	}
}

func TestRotateConsistencyExhaustiveWidths1Through8(t *testing.T) {
	assignments := 0
	for width := 1; width <= 8; width++ {
		rotateConsistencyRun(t, fmt.Sprintf("W%d", width), func(t *testing.T) {
			x, n := paramTerm("x", width), paramTerm("n", width)
			symbolic := binaryTerm("ror", x, n)
			widths := map[string]int{"x": width, "n": width}
			dynamic := rotateConsistencyCircuitFor(t, symbolic, []string{"x", "n"}, widths)
			slots := newTermEvaluator(symbolic)
			env := map[string]uint64{}
			limit := uint64(1) << uint(width)
			for count := uint64(0); count < limit; count++ {
				constant := binaryTerm("ror", paramTerm("x", width), constTerm(count, width))
				fixed := rotateConsistencyCircuitFor(t, constant, []string{"x"}, map[string]int{"x": width})
				fixedSlots := newTermEvaluator(constant)
				for data := uint64(0); data < limit; data++ {
					env["x"], env["n"] = data, count
					want := rotateConsistencyReference(data, count, width, width, width)
					rotateConsistencyCheck(t, "symbolic count", symbolic, slots, dynamic, env, want)
					rotateConsistencyCheck(t, "constant count", constant, fixedSlots, fixed, env, want)
					folded := binaryTerm("ror", constTerm(data, width), constTerm(count, width))
					if folded.kind != termConst || folded.value != want {
						t.Fatalf("constant fold W=%d data=%#x count=%#x got=%#x want=%#x", width, data, count, folded.value, want)
					}
					assignments++
				}
			}
		})
	}
	if assignments != 87380 {
		t.Fatalf("exhaustive coverage=%d, want 87380", assignments)
	}
}

func rotateConsistencyData(width int) []uint64 {
	values := []uint64{0, mask(width), 0xaaaaaaaaaaaaaaaa & mask(width), 0x5555555555555555 & mask(width)}
	for bit := 0; bit < width; bit++ {
		values = append(values, uint64(1)<<uint(bit))
	}
	return values
}

func TestRotateConsistencyBoundedWidths9Through64(t *testing.T) {
	for width := 9; width <= 64; width++ {
		rotateConsistencyRun(t, fmt.Sprintf("W%d", width), func(t *testing.T) {
			counts := []uint64{0, 1, uint64(width - 1), uint64(width), uint64(width + 1), mask(width)}
			for bit := 0; bit < width; bit++ {
				counts = append(counts, uint64(1)<<uint(bit))
			}
			for _, count := range counts {
				root := binaryTerm("ror", paramTerm("x", width), constTerm(count, width))
				circuit := rotateConsistencyCircuitFor(t, root, []string{"x"}, map[string]int{"x": width})
				slots := newTermEvaluator(root)
				for _, data := range rotateConsistencyData(width) {
					want := rotateConsistencyReference(data, count, width, width, width)
					rotateConsistencyCheck(t, fmt.Sprintf("literal count=%#x", count), root, slots, circuit, map[string]uint64{"x": data}, want)
					folded := binaryTerm("ror", constTerm(data, width), constTerm(count, width))
					if folded.kind != termConst || folded.value != want {
						t.Fatalf("fold W=%d x=%#x count=%#x got=%#x want=%#x", width, data, count, folded.value, want)
					}
				}
			}
			// Exactly one variable count bit per diagram, including W33/bit32
			// and W63/bit62. Never build an unrestricted 63-bit rotate.
			for bit := 0; bit < width; bit++ {
				count := binaryTerm("and", paramTerm("n", width), constTerm(uint64(1)<<uint(bit), width))
				root := binaryTerm("ror", paramTerm("x", width), count)
				circuit := rotateConsistencyCircuitFor(t, root, []string{"x", "n"}, map[string]int{"x": width, "n": width})
				slots := newTermEvaluator(root)
				for _, data := range rotateConsistencyData(width) {
					for _, n := range []uint64{0, uint64(1) << uint(bit)} {
						want := rotateConsistencyReference(data, n, width, width, width)
						rotateConsistencyCheck(t, fmt.Sprintf("symbolic bit%d", bit), root, slots, circuit, map[string]uint64{"x": data, "n": n}, want)
					}
				}
			}
		})
	}
}

func TestRotateConsistencyRawConstantsAndMixedWidths(t *testing.T) {
	for _, tc := range []struct {
		name                         string
		width, dataWidth, countWidth int
		data, count                  uint64
	}{
		{"recorded_ROR8_1_7", 8, 8, 8, 1, 7},
		{"W3_high_count4", 3, 3, 3, 1, 4},
		{"W5_high_count8", 5, 5, 5, 1, 8},
		{"W63_count64", 63, 63, 63, 1, 64},
		{"W64_zero", 64, 64, 64, 0x8123456789abcdef, 0},
		{"op_masks_before_modulo", 3, 3, 8, 1, 8},
		{"raw_narrow_count", 5, 5, 2, 1, 8},
		{"raw_narrow_data", 16, 3, 8, 0x101, 1},
		{"raw_both_payloads", 3, 8, 2, 0x101, 12},
		{"wide_data_narrow_count", 8, 16, 3, 0x180, 7},
		{"narrow_data_wide_count", 16, 8, 32, 0x81, 0x10001},
	} {
		rotateConsistencyRun(t, tc.name, func(t *testing.T) {
			left := &term{kind: termConst, width: tc.dataWidth, value: tc.data}
			right := &term{kind: termConst, width: tc.countWidth, value: tc.count}
			root := rotateConsistencyRaw(tc.width, left, right)
			if reason := nativeCertificateTermReason(root, nil); reason != "" {
				t.Fatalf("raw fixture refused: %s", reason)
			}
			want := rotateConsistencyReference(tc.data, tc.count, tc.width, tc.dataWidth, tc.countWidth)
			rotateConsistencyCheck(t, tc.name, root, newTermEvaluator(root), rotateConsistencyCircuitFor(t, root, nil, nil), nil, want)
			// Constructor width is the left child's own width; raw constant
			// child payloads must be masked before operation-width adaptation.
			fold := binaryTerm("ror", left, right)
			constructorWant := rotateConsistencyReference(tc.data, tc.count, tc.dataWidth, tc.dataWidth, tc.countWidth)
			if fold.kind != termConst || fold.width != tc.dataWidth || fold.value != constructorWant {
				t.Fatalf("raw constructor got=(kind%d,W%d,%#x) want=(constant,W%d,%#x)", fold.kind, fold.width, fold.value, tc.dataWidth, constructorWant)
			}
		})
	}
	for _, tc := range []struct{ width, dataView, dataDeclared, countView, countDeclared int }{
		{3, 8, 8, 8, 8}, {5, 3, 3, 8, 8}, {16, 32, 8, 32, 3}, {8, 3, 16, 2, 16}, {33, 64, 3, 64, 33}, {63, 8, 8, 64, 63},
	} {
		rotateConsistencyRun(t, fmt.Sprintf("W%d_views%d_%d_declared%d_%d", tc.width, tc.dataView, tc.countView, tc.dataDeclared, tc.countDeclared), func(t *testing.T) {
			x := &term{kind: termParam, name: "x", width: tc.dataView, declared: tc.dataDeclared}
			n := &term{kind: termParam, name: "n", width: tc.countView, declared: tc.countDeclared}
			// A single selected count bit keeps high-width diagrams bounded.
			selectedBit := min(tc.width, tc.countView, tc.countDeclared) - 1
			count := binaryTerm("and", n, constTerm(uint64(1)<<uint(selectedBit), tc.countView))
			root := rotateConsistencyRaw(tc.width, x, count)
			widths := map[string]int{"x": tc.dataDeclared, "n": tc.countDeclared}
			circuit := rotateConsistencyCircuitFor(t, root, []string{"x", "n"}, widths)
			slots := newTermEvaluator(root)
			for _, data := range rotateConsistencyData(tc.dataDeclared) {
				for _, countValue := range []uint64{0, uint64(1) << uint(selectedBit)} {
					env := map[string]uint64{"x": data, "n": countValue}
					want := rotateConsistencyReference(data, countValue, tc.width, tc.dataView, tc.countView)
					rotateConsistencyCheck(t, "mixed declared binding", root, slots, circuit, env, want)
				}
			}
		})
	}
}

func TestRotateConsistencyChangedChildRebuilds(t *testing.T) {
	for _, route := range []string{"canonicalMemo", "canonicalLinear", "respell"} {
		for _, constant := range []bool{false, true} {
			rotateConsistencyRun(t, fmt.Sprintf("%s_constant%v", route, constant), func(t *testing.T) {
				leaf := paramTerm("x", 8)
				if constant {
					leaf = constTerm(0x81, 8)
				}
				child := &term{kind: termBinary, width: 8, op: "and", left: leaf, right: constTerm(255, 8)}
				count := &term{kind: termBinary, width: 3, op: "and", left: constTerm(1, 3), right: constTerm(7, 3)}
				original := rotateConsistencyRaw(16, child, count)
				var got *term
				switch route {
				case "canonicalMemo":
					got = canonical(original)
				case "canonicalLinear":
					got = canonicalLinear(original, map[*term]*term{})
				case "respell":
					got = respell(original)
				}
				if got == original {
					t.Fatal("fixture did not exercise changed-child rebuilding")
				}
				if got.width != 16 || original.width != 16 || original.left != child || original.right != count {
					t.Fatal("rebuild changed original operation identity or width")
				}
				if constant && got.kind != termConst {
					t.Fatal("changed constant children did not fold")
				}
				if !constant && (got.kind != termBinary || got.op != "ror" || got.left.width != 8 || got.right.width != 3) {
					t.Fatalf("lost child boundaries: %s", got)
				}
				for _, x := range []uint64{0, 1, 0x81, 0xff} {
					data := x
					if constant {
						data = 0x81
					}
					want := rotateConsistencyReference(data, 1, 16, 8, 3)
					if value := got.eval(map[string]uint64{"x": x}); value != want {
						t.Fatalf("x=%#x got=%#x want=%#x", x, value, want)
					}
				}
			})
		}
	}
	// A raw add-zero child must really change under linear respelling.
	add := &term{kind: termBinary, width: 8, op: "add", left: paramTerm("x", 8), right: constTerm(0, 8)}
	root := rotateConsistencyRaw(16, add, constTerm(1, 3))
	if got := respell(root); got == root || got.width != 16 || got.eval(map[string]uint64{"x": 1}) != 0x8000 {
		t.Fatalf("raw add-zero rebuild failed: %s", got)
	}

	// Replacement views may be wider while retaining the same low bits. This
	// directly checks the original boundary before canonicalBitwise can expand.
	narrow := &term{kind: termParam, name: "x", width: 8, declared: 32}
	wide := &term{kind: termParam, name: "x", width: 32, declared: 32}
	original := rotateConsistencyRaw(32, narrow, constTerm(1, 32))
	memo := newCanonicalTable()
	memo.done[narrow] = wide
	got := canonicalMemo(original, memo, map[*term]bool{})
	if got.kind != termBinary || got.op != "ror" || got.width != 32 || got.left.width != 8 {
		t.Fatalf("widened canonical child bypassed ROR boundary: %s", got)
	}
	if value, want := got.eval(map[string]uint64{"x": 0x101}), rotateConsistencyReference(0x101, 1, 32, 8, 32); value != want {
		t.Fatalf("restored child got=%#x want=%#x", value, want)
	}
	if rebuildROR(original, original.left, original.right) != original {
		t.Fatal("unchanged ROR lost sharing")
	}
	original.id, original.sigBits = 91, 7
	fresh := rebuildROR(original, wide, original.right)
	if fresh == original || fresh.id != 0 || fresh.sigBits != 0 || original.id != 91 || original.sigBits != 7 {
		t.Fatal("rebuilt ROR retained stale metadata or mutated input")
	}
}

func TestRotateConsistencyConditionalBoundaries(t *testing.T) {
	for _, side := range []string{"data", "count"} {
		for _, route := range []string{"settleBySpelling", "hoistIte"} {
			rotateConsistencyRun(t, side+"_"+route, func(t *testing.T) {
				condition := paramTerm("c", 1)
				conditional := &term{kind: termIte, width: 8, cond: condition, left: paramTerm("a", 32), right: paramTerm("b", 32)}
				root := rotateConsistencyRaw(16, conditional, constTerm(1, 16))
				if side == "count" {
					root = rotateConsistencyRaw(16, constTerm(1, 16), conditional)
				}
				for _, chosen := range []uint64{0, 1} {
					var got *term
					if route == "settleBySpelling" {
						fact := condition
						if chosen == 0 {
							fact = binaryTerm("xor", condition, constTerm(1, 1))
						}
						got = settleBySpelling(root, []*term{fact})
					} else {
						c, yes, no, ok := hoistIte(root)
						if !ok || c != condition {
							t.Fatal("conditional fixture was not hoisted")
						}
						got = no
						if chosen == 1 {
							got = yes
						}
					}
					if got == root || got.width != 16 {
						t.Fatal("conditional rebuild was not exercised at original operation width")
					}
					for _, a := range []uint64{1, 0x101, 0x10000, 0xdeadbeef} {
						env := map[string]uint64{"c": chosen, "a": a, "b": 0x102}
						arm := uint64(0x102)
						if chosen != 0 {
							arm = a
						}
						want := rotateConsistencyReference(arm, 1, 16, 8, 16)
						if side == "count" {
							want = rotateConsistencyReference(1, arm, 16, 16, 8)
						}
						if before, after := root.eval(env), got.eval(env); before != want || after != want {
							t.Fatalf("arm32/conditional8/ROR16 %v: before=%#x after=%#x want=%#x", env, before, after, want)
						}
					}
				}
			})
		}
	}
}

// Frozen 8137f0c5 barrel behavior, used only for ordinary 32/64 compatibility.
// The output permutation above remains the independent semantics oracle.
func rotateConsistencyOriginalBarrel(bl *blaster, data, count []int) []int {
	out := data
	for stage := 0; 1<<uint(stage) < len(data); stage++ {
		distance := 1 << uint(stage)
		next := make([]int, len(data))
		for bit := range next {
			next[bit] = bl.ite(count[stage], out[(bit+distance)%len(data)], out[bit])
		}
		out = next
	}
	return out
}

func TestRotateConsistencyPowerOfTwoOriginalTraceParity(t *testing.T) {
	for _, width := range []int{32, 64} {
		for _, symbolicData := range []bool{false, true} {
			rotateConsistencyRun(t, fmt.Sprintf("W%d_symbolicData%v", width, symbolicData), func(t *testing.T) {
				data := constTerm(0xa531a531a531a531, width)
				if symbolicData {
					data = zeroExtend(paramTerm("x", 1), width)
				}
				count := paramTerm("n", width)
				root := binaryTerm("ror", data, count)
				names, widths := []string{"x", "n"}, map[string]int{"x": 1, "n": width}
				for _, cnf := range []bool{false, true} {
					current, baseline := newBlaster(names, widths), newBlaster(names, widths)
					if cnf {
						current, baseline = newCNFBlaster(names, widths), newCNFBlaster(names, widths)
					}
					got := current.blast(root)
					a, b := baseline.blast(data), baseline.blast(count)
					want := rotateConsistencyOriginalBarrel(baseline, a, b)
					if current.exceeded() || baseline.exceeded() || !reflect.DeepEqual(got, want) {
						t.Fatalf("CNF=%v unexpected unknown or edge-order drift", cnf)
					}
					if !reflect.DeepEqual(current.owners, baseline.owners) {
						t.Fatal("operand registration changed")
					}
					if cnf {
						if len(current.cnf.gates) > rotateConsistencyFixtureNodes || !reflect.DeepEqual(current.cnf, baseline.cnf) {
							t.Fatal("CNF allocation, gate, memo, or clause sequence changed")
						}
					} else if len(current.bdd.nodes) > rotateConsistencyFixtureNodes || !reflect.DeepEqual(current.bdd.nodes, baseline.bdd.nodes) {
						t.Fatal("BDD node creation order or count changed")
					}
					p, q := serializeProblem(current, root, nil, NodeBudget, "interleaved"), serializeProblem(baseline, root, nil, NodeBudget, "interleaved")
					if !reflect.DeepEqual(p.Words, q.Words) || !reflect.DeepEqual(p.Owners, q.Owners) {
						t.Fatal("serialized operation/operand identities changed")
					}
				}
			})
		}
	}
}

func TestRotateConsistencyCertificatesWitnessesAndMutations(t *testing.T) {
	widths := map[string]int{"x": 8}
	x := paramTerm("x", 8)
	root := rotateConsistencyRaw(8, x, constTerm(7, 8))
	if reason := nativeCertificateTermReason(root, widths); reason != "" {
		t.Fatalf("native ROR admission changed: %s", reason)
	}
	if reason := nativeBitwiseTermReason(root, widths); !strings.Contains(reason, `operation "ror" outside`) {
		t.Fatalf("narrow certificate admitted ROR or wrong refusal: %q", reason)
	}
	for _, op := range []string{"and", "or", "xor"} {
		pointwise := &term{kind: termBinary, width: 8, op: op, left: x, right: constTerm(7, 8)}
		if reason := nativeBitwiseTermReason(pointwise, widths); reason != "" {
			t.Fatalf("existing %s grammar refused: %s", op, reason)
		}
	}
	// No constant/structural identity is used to establish these controls.
	for _, tc := range []struct {
		name     string
		value    *term
		expected uint64
	}{
		{"correct", root, 2},
		{"count_mutation", rotateConsistencyRaw(8, x, constTerm(6, 8)), 2},
		{"direction_mutation", rotateConsistencyRaw(8, x, constTerm(1, 8)), 2},
		{"operation_width_mutation", rotateConsistencyRaw(7, x, constTerm(7, 8)), 2},
		{"outer_truncation_correct", truncate(rotateConsistencyRaw(16, x, constTerm(1, 8)), 8), 0},
		{"outer_truncation_moved_inside", rotateConsistencyRaw(8, x, constTerm(1, 8)), 0},
	} {
		rotateConsistencyRun(t, tc.name, func(t *testing.T) {
			operandWidth := tc.value.width
			expected := constTerm(tc.expected, operandWidth)
			claim := truncate(cmpTerm("eq", tc.value, expected), 1)
			if claim.kind != termCmp || claim.width != 1 || claim.left != tc.value || claim.right != expected || claim.left.width != operandWidth || claim.right.width != operandWidth {
				t.Fatal("Boolean claim adaptation changed comparison operands or their widths")
			}
			cnf, reason, ok := exportTermCNF("ROR witness control", []string{"x"}, widths, claim, nil)
			if !ok {
				t.Fatalf("unexpected CNF refusal: %s", reason)
			}
			env := map[string]uint64{"x": 1}
			wantFailure := tc.name != "correct" && tc.name != "outer_truncation_correct"
			if cnf.Settled != nil {
				t.Fatal("mutation fixture settled structurally")
			}
			if cnf.Evaluate(env) != wantFailure || cnf.Confirms(env) != wantFailure {
				t.Fatalf("CNF gate/witness mismatch; want counterexample=%v", wantFailure)
			}
			bl := newBlaster([]string{"x"}, widths)
			if bl.blast(claim) == nil || bl.exceeded() {
				t.Fatal("unexpected BDD unknown")
			}
			p := serializeProblem(bl, claim, nil, NodeBudget, "interleaved")
			var set []uint32
			for variable, owner := range p.Owners {
				if env[owner.Param]>>uint(owner.Bit)&1 != 0 {
					set = append(set, variable)
				}
			}
			if p.Confirms(set) != wantFailure {
				t.Fatalf("serialized witness confirmation want=%v", wantFailure)
			}
		})
	}
	// A correct ROR result cannot erase an independently firing original trap.
	rootWidth, trapOperandWidth := root.width, x.width
	claim := &term{kind: termCmp, width: 1, op: "eq", left: root, right: root}
	trapExpected := constTerm(1, trapOperandWidth)
	trap := truncate(cmpTerm("eq", x, trapExpected), 1)
	if claim.kind != termCmp || claim.width != 1 || claim.left != root || claim.right != root || claim.left.width != rootWidth || claim.right.width != rootWidth {
		t.Fatal("trap-bearing claim changed comparison operands or their widths")
	}
	if trap.kind != termCmp || trap.width != 1 || trap.left != x || trap.right != trapExpected || trap.left.width != trapOperandWidth || trap.right.width != trapOperandWidth {
		t.Fatal("Boolean trap adaptation changed comparison operands or their widths")
	}
	cnf, reason, ok := exportTermCNF("ROR trap control", []string{"x"}, widths, claim, []*term{trap})
	if !ok || !cnf.Evaluate(map[string]uint64{"x": 1}) || !cnf.Confirms(map[string]uint64{"x": 1}) {
		t.Fatalf("ROR trap obligation lost: ok=%v reason=%s", ok, reason)
	}
	lowered := &loweredTheorem{claim: claim, traps: []*term{trap}, names: []string{"x"}, widths: widths}
	if decision, found := lowered.witnessRefutation(); !found || decision.Kind != DecisionRefuted || !strings.Contains(decision.Message, "traps") {
		t.Fatalf("trap witness not retained: found=%v decision=%v", found, decision)
	}
	if decision, exceeded := decideBlasted(newBlaster([]string{"x"}, widths), []*term{trap}, claim, []string{"x"}, newTermEvaluator(claim, trap)); exceeded || decision.Kind != DecisionRefuted {
		t.Fatalf("trap-bearing theorem unexpectedly undecided or proven: %v exceeded=%v", decision, exceeded)
	}
}

func TestRotateConsistencyRaceColdSharedDAG(t *testing.T) {
	x, n := paramTerm("x", 5), paramTerm("n", 5)
	inner := binaryTerm("ror", x, n)
	root := binaryTerm("ror", binaryTerm("xor", inner, constTerm(0x15, 5)), n)
	// Number once before workers start. Each worker owns its fork's stamps,
	// value slots, BDD store, CNF store, and all blast memoization.
	template := newTermEvaluator(root)
	ids := make([]int32, len(template.terms))
	for i, term := range template.terms {
		ids[i] = term.id
	}
	const workers = 8
	errors := make(chan string, workers)
	var wait sync.WaitGroup
	for worker := 0; worker < workers; worker++ {
		wait.Add(1)
		go func(worker int) {
			defer wait.Done()
			bl := newBlaster([]string{"x", "n"}, map[string]int{"x": 5, "n": 5})
			cnf := newCNFBlaster([]string{"x", "n"}, map[string]int{"x": 5, "n": 5})
			bb, cb := bl.blast(root), cnf.blast(root)
			if len(bb) != 5 || len(cb) != 5 || bl.exceeded() || cnf.exceeded() || len(bl.bdd.nodes) > rotateConsistencyFixtureNodes || len(cnf.cnf.gates) > rotateConsistencyFixtureNodes {
				errors <- fmt.Sprintf("worker%d unexpected unknown/unbounded fixture", worker)
				return
			}
			slots := template.fork()
			circuit := &rotateConsistencyCircuit{bdd: bl, cnf: cnf, bddBits: bb, cnfBits: cb, assignment: map[int]bool{}, values: make([]bool, cnf.cnf.variables+1)}
			for data := uint64(worker); data < 32; data += workers {
				for count := uint64(0); count < 32; count++ {
					env := map[string]uint64{"x": data, "n": count}
					first := rotateConsistencyReference(data, count, 5, 5, 5)
					want := rotateConsistencyReference(first^0x15, count, 5, 5, 5)
					if root.eval(env) != want || slots.evaluate(root, env) != want {
						errors <- fmt.Sprintf("worker%d x=%d n=%d slot/map mismatch", worker, data, count)
						return
					}
					gotBDD, gotCNF, err := circuit.evaluateValues(env)
					if err != nil {
						errors <- fmt.Sprintf("worker%d: %v", worker, err)
						return
					}
					if gotBDD != want || gotCNF != want {
						errors <- fmt.Sprintf("worker%d x=%d n=%d BDD=%#x CNF=%#x want=%#x", worker, data, count, gotBDD, gotCNF, want)
						return
					}
				}
			}
		}(worker)
	}
	wait.Wait()
	close(errors)
	for err := range errors {
		t.Error(err)
	}
	for i, term := range template.terms {
		if term.id != ids[i] {
			t.Fatal("worker changed shared term numbering")
		}
	}
}

func TestRotateConsistencyRaceCancellationAndExhaustion(t *testing.T) {
	for _, shape := range []string{"constant", "zero", "symbolic", "cached"} {
		rotateConsistencyRun(t, "cancel_before_"+shape, func(t *testing.T) {
			x, n := paramTerm("x", 5), paramTerm("n", 5)
			root := rotateConsistencyRaw(5, x, n)
			if shape == "constant" {
				root = rotateConsistencyRaw(5, constTerm(1, 5), constTerm(8, 5))
			}
			if shape == "zero" {
				root = rotateConsistencyRaw(5, x, constTerm(0, 5))
			}
			bl := newBlaster([]string{"x", "n"}, map[string]int{"x": 5, "n": 5})
			if shape == "cached" && bl.blast(root) == nil {
				t.Fatal("could not prime fixture")
			}
			before := len(bl.memo)
			var stop atomic.Bool
			stop.Store(true)
			bl.bdd.stop = &stop
			if bl.blast(root) != nil || !bl.exceeded() || len(bl.memo) != before {
				t.Fatal("cancelled blast published a result or changed memo")
			}
			claim := cmpTerm("eq", root, root)
			evaluator := newTermEvaluator(claim)
			if _, exceeded := decideBlasted(bl, nil, claim, []string{"x", "n"}, evaluator); !exceeded {
				t.Fatal("stopped output did not report its expected non-decision")
			}
			// Decision{} has the same zero Kind as DecisionProven; the
			// exhaustion bit is authoritative. Check its actual consumer.
			if _, decided := testRaceBDDOrders([]*blaster{bl}, func(attempt *blaster) (Decision, bool) {
				return decideBlasted(attempt, nil, claim, []string{"x", "n"}, evaluator.fork())
			}); decided {
				t.Fatal("the decision consumer accepted stopped placeholder output")
			}
		})
	}
	for _, mode := range []string{"stage_cancellation", "stage_node_exhaustion", "cnf_stopped"} {
		rotateConsistencyRun(t, mode, func(t *testing.T) {
			x, n := paramTerm("x", 5), paramTerm("n", 5)
			root := rotateConsistencyRaw(5, x, n)
			bl := newBlaster([]string{"x", "n"}, map[string]int{"x": 5, "n": 5})
			if mode == "cnf_stopped" {
				bl = newCNFBlaster([]string{"x", "n"}, map[string]int{"x": 5, "n": 5})
			}
			a, b := bl.blast(x), bl.blast(n)
			if len(a) != 5 || len(b) != 5 || bl.exceeded() {
				t.Fatal("could not prime both operands")
			}
			before := len(bl.memo)
			switch mode {
			case "stage_cancellation":
				// Call the stage engine itself: its first mux observes an
				// already requested stop, independent of blast's entry guard.
				var stop atomic.Bool
				stop.Store(true)
				bl.bdd.stop = &stop
				if bl.rotateBarrel(a, b) != nil {
					t.Fatal("stage cancellation returned placeholder bits")
				}
			case "stage_node_exhaustion":
				// Permit inputs but not the first nontrivial stage node.
				bl.bdd.budget = len(bl.bdd.nodes)
				if bl.blast(root) != nil {
					t.Fatal("stage exhaustion returned placeholder bits")
				}
			case "cnf_stopped":
				bl.cnf.exceeded = true
				if bl.blast(root) != nil {
					t.Fatal("exhausted CNF returned bits")
				}
			}
			if !bl.exceeded() || len(bl.memo) != before || bl.memo[root] != nil {
				t.Fatal("partial ROR result entered the memo")
			}
			if bl.blast(root) != nil {
				t.Fatal("a second read returned a partial cached result")
			}
		})
	}
}

func TestRotateConsistencyRaceReadRegistrationAndAliasIdentity(t *testing.T) {
	for _, width := range []int{1, 5, 64} {
		for _, cnf := range []bool{false, true} {
			rotateConsistencyRun(t, fmt.Sprintf("W%d_CNF%v", width, cnf), func(t *testing.T) {
				index := paramTerm("index", 3)
				data := &term{kind: termSelect, width: width, name: "data", left: index}
				read := &term{kind: termSelect, width: width, name: "count", left: index}
				// Keep a symbolic read underneath a count that blasts to zero.
				count := &term{kind: termBinary, width: width, op: "and", left: read, right: constTerm(0, width)}
				root := rotateConsistencyRaw(width, data, count)
				bl := newBlaster([]string{"index"}, map[string]int{"index": 3})
				if cnf {
					bl = newCNFBlaster([]string{"index"}, map[string]int{"index": 3})
				}
				bits := bl.blast(root)
				if len(bits) != width || bl.exceeded() || len(bl.selects) != 2 || bl.memo[data] == nil || bl.memo[read] == nil || bl.memo[count] == nil {
					t.Fatal("zero-count shortcut lost operand/read registration")
				}
				if !reflect.DeepEqual(bits, bl.memo[data]) {
					t.Fatal("zero count changed data bits")
				}
				if bl.selects[0].span != "data" || bl.selects[1].span != "count" {
					t.Fatal("operand registration order changed")
				}
				if reflect.DeepEqual(bl.selects[0].vars, bl.selects[1].vars) {
					t.Fatal("distinct memory identities aliased")
				}
				alias := &term{kind: termSelect, width: width, name: "data", left: index}
				if !reflect.DeepEqual(bl.blast(alias), bl.memo[data]) || len(bl.selects) != 2 {
					t.Fatal("equivalent read failed to reuse its identity")
				}
				other := &term{kind: termSelect, width: width, name: "data", left: binaryTerm("xor", index, constTerm(1, 3))}
				if bl.blast(other) == nil || bl.exceeded() || len(bl.selects) != 3 || reflect.DeepEqual(bl.selects[0].vars, bl.selects[2].vars) {
					t.Fatal("distinct same-span indices aliased")
				}
			})
		}
	}
}
