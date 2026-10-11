package asm

import (
	"fmt"
	"testing"
)

type structuralOrderFixture struct {
	left, right, tag, opposite, hit, old, index, writeIndex *term
	kindName                                                string
	names                                                   []string
	widths                                                  map[string]int
}

// A discriminator-first split closes this pair at depth one. Splitting the
// outer write hit first leaves the discriminator for a second level.
func newStructuralOrderFixture(name, comparison string, constantFirst bool) structuralOrderFixture {
	kind := structuralControlParam(name, 4)
	index, writeIndex := structuralControlParam("read.index", 2), structuralControlParam("write.index", 2)
	zero := structuralControlConst(0, 4)
	a, b := kind, zero
	if constantFirst {
		a, b = b, a
	}
	opposite := "ne"
	if comparison == "ne" {
		opposite = "eq"
	}
	tag, notTag := structuralControlCmp(comparison, a, b), structuralControlCmp(opposite, a, b)
	hit := structuralControlCmp("eq", index, writeIndex)
	old := structuralControlRead("words", index, 4)
	f := structuralOrderFixture{tag: tag, opposite: notTag, hit: hit, old: old, index: index, writeIndex: writeIndex,
		kindName: name, names: []string{name, "read.index", "write.index"},
		widths: map[string]int{name: 4, "read.index": 2, "write.index": 2}}
	f.left, f.right = structuralOrderRoots(f, old, structuralControlConst(5, 4), structuralControlConst(9, 4))
	return f
}

func structuralOrderRoots(f structuralOrderFixture, old, first, second *term) (*term, *term) {
	and := func(a, b *term) *term { return structuralControlBinary("and", 1, a, b) }
	return structuralControlITE(4, f.hit, structuralControlITE(4, f.tag, first, second), old),
		structuralControlITE(4, and(f.hit, f.tag), first,
			structuralControlITE(4, and(f.hit, f.opposite), second, old))
}

// Compare the predicate partition rather than allocation-order-specific IDs.
// Equality and inequality, and swapped operands, define the same partition.
func structuralOrderGuardIdentity(t *testing.T, s *structuralCases, guard int) string {
	t.Helper()
	if guard < 0 || guard >= len(s.nodes) {
		t.Fatal("guard selection did not return a node")
	}
	n := s.nodes[guard]
	if n.kind != termCmp || n.width != 1 || n.op != "eq" && n.op != "ne" || n.left < 0 || n.right < 0 {
		t.Fatal("guard selection did not choose a scalar equality discriminator")
	}
	parameter, constant := s.nodes[n.left], s.nodes[n.right]
	if parameter.kind == termConst {
		parameter, constant = constant, parameter
	}
	if parameter.kind != termParam || constant.kind != termConst {
		t.Fatal("a memory/compound comparison displaced the shared scalar discriminator")
	}
	return fmt.Sprintf("%q/%d/%d=%d/%d/%d", parameter.name, parameter.width, parameter.declared,
		constant.value, constant.width, constant.declared)
}

func structuralOrderSelected(t *testing.T, a, b *term) string {
	t.Helper()
	s := newStructuralCases(structuralControlLimits())
	roots, ok := s.importTerms(a, b)
	if !ok {
		t.Fatal("could not import the admitted guard-order control")
	}
	return structuralOrderGuardIdentity(t, s, s.split(roots[0], roots[1]))
}

func structuralOrderEvaluate(t *testing.T, f structuralOrderFixture, a, b *term, wantEqual bool) {
	t.Helper()
	equal := true
	env := map[string]uint64{}
	for kind := uint64(0); kind < 16; kind++ {
		for index := uint64(0); index < 4; index++ {
			for write := uint64(0); write < 4; write++ {
				for pattern := uint64(0); pattern < 4; pattern++ {
					env[f.kindName], env["read.index"], env["write.index"] = kind, index, write
					for k := uint64(0); k < 4; k++ {
						env[spanElemName("words", int64(k))] = (k*5 + pattern*3) & 15
						env[spanElemName("other.words", int64(k))] = (k*7 + pattern*3 + 1) & 15
					}
					if a.eval(env) != b.eval(env) {
						equal = false
						if wantEqual {
							t.Fatalf("accepted ordering control differs at kind=%d index=%d write=%d pattern=%d", kind, index, write, pattern)
						}
					}
				}
			}
		}
	}
	if equal != wantEqual {
		t.Fatal("ordering control did not have the expected exhaustive-evaluation result")
	}
	if structuralControlBDDEqual(t, a, b, f.names, f.widths) != wantEqual {
		t.Fatal("independent BDD disagrees with the guard-order control")
	}
}

func TestStructuralCasesOrderPrefersSharedScalarDiscriminator(t *testing.T) {
	for _, name := range []string{"mode", "event.class", "renamed_selector_47"} {
		for _, comparison := range []string{"eq", "ne"} {
			for _, constantFirst := range []bool{false, true} {
				t.Run(fmt.Sprintf("%s/%s/constant-first-%v", name, comparison, constantFirst), func(t *testing.T) {
					f := newStructuralOrderFixture(name, comparison, constantFirst)
					before := structuralControlSnapshot(f.left, f.right)
					wantGuard := fmt.Sprintf("%q/4/4=0/4/0", name)
					for _, swapped := range []bool{false, true} {
						for _, reverse := range []bool{false, true} {
							a, b := f.left, f.right
							if swapped {
								a, b = b, a
							}
							if guard := structuralOrderSelected(t, a, b); guard != wantGuard {
								t.Fatalf("chosen partition=%s, want %s", guard, wantGuard)
							}
							limits := structuralControlLimits()
							limits.depth = 1
							s := newStructuralCases(limits)
							s.reverse = reverse
							if !s.equal(a, b) || s.leaves != 2 {
								t.Fatalf("preferred guard must close exactly two depth-one leaves: swapped=%v reverse=%v leaves=%d", swapped, reverse, s.leaves)
							}
						}
					}
					structuralControlUnchanged(t, before)
					structuralOrderEvaluate(t, f, f.left, f.right, true)
				})
			}
		}
	}
}

func TestStructuralCasesOrderSkipsMemoryDiscriminator(t *testing.T) {
	f := newStructuralOrderFixture("mode", "eq", false)
	f.hit = structuralControlCmp("eq", structuralControlRead("flags", f.index, 4), structuralControlConst(0, 4))
	f.left, f.right = structuralOrderRoots(f, f.old, structuralControlConst(5, 4), structuralControlConst(9, 4))
	for _, pair := range [][2]*term{{f.left, f.right}, {f.right, f.left}} {
		if got := structuralOrderSelected(t, pair[0], pair[1]); got != `"mode"/4/4=0/4/0` {
			t.Fatalf("a memory comparison displaced the scalar guard: %s", got)
		}
		limits := structuralControlLimits()
		limits.depth = 1
		if !newStructuralCases(limits).equal(pair[0], pair[1]) {
			t.Fatal("scalar guard did not close both memory-hit cases at depth one")
		}
	}
	structuralOrderEvaluate(t, f, f.left, f.right, true)
}

func TestStructuralCasesOrderReorderedDisjointStores(t *testing.T) {
	for _, name := range []string{"variant", "different_name"} {
		f := newStructuralOrderFixture(name, "eq", false)
		kind := structuralControlParam(name, 4)
		and := func(a, b *term) *term { return structuralControlBinary("and", 1, a, b) }
		guard := func(op string, value uint64) *term {
			return structuralControlCmp(op, kind, structuralControlConst(value, 4))
		}
		conditions := []*term{
			and(f.hit, and(guard("eq", 0), guard("ne", 1))),
			and(f.hit, and(guard("eq", 1), guard("ne", 0))),
		}
		values := []*term{structuralControlConst(5, 4), structuralControlConst(9, 4)}
		write := func(first, second int) *term {
			return structuralControlITE(4, conditions[first], values[first], structuralControlITE(4, conditions[second], values[second], f.old))
		}
		a, b := write(0, 1), write(1, 0)
		for _, swapped := range []bool{false, true} {
			for _, reverse := range []bool{false, true} {
				left, right := a, b
				if swapped {
					left, right = right, left
				}
				// Traversal is deterministic for an ordered pair. Swapping
				// roots can legitimately choose the other shared predicate.
				guard := structuralOrderSelected(t, left, right)
				if again := structuralOrderSelected(t, left, right); again != guard {
					t.Fatalf("identical ordered roots chose different partitions: %s versus %s", guard, again)
				}
				s := newStructuralCases(structuralControlLimits())
				s.reverse = reverse
				if !s.equal(left, right) || s.leaves != 2 {
					t.Fatalf("reordered explicitly disjoint stores failed: swapped=%v reverse=%v leaves=%d", swapped, reverse, s.leaves)
				}
			}
		}
		structuralOrderEvaluate(t, f, a, b, true)
	}
}

func TestStructuralCasesOrderPreservesNegativeControls(t *testing.T) {
	f := newStructuralOrderFixture("variant", "eq", false)
	first, second := structuralControlConst(5, 4), structuralControlConst(9, 4)
	changedOld := func(old *term) *term {
		_, right := structuralOrderRoots(f, old, first, second)
		return right
	}
	rare := structuralControlCmp("eq", structuralControlParam(f.kindName, 4), structuralControlConst(15, 4))
	xorOne := structuralControlBinary("xor", 4, f.old, structuralControlConst(1, 4))
	_, changedArm := structuralOrderRoots(f, f.old, structuralControlBinary("xor", 4, first, structuralControlConst(1, 4)), second)
	tests := map[string]*term{
		"span alias is not identity": changedOld(structuralControlRead("other.words", f.index, 4)),
		"potentially aliasing index": changedOld(structuralControlRead("words", f.writeIndex, 4)),
		"adjacent overlapping index": changedOld(structuralControlRead("words", structuralControlBinary("add", 2, f.index, structuralControlConst(1, 2)), 4)),
		"element width":              changedOld(structuralControlBinary("or", 4, structuralControlRead("words", f.index, 2), structuralControlConst(0, 4))),
		"rare symbolic value":        changedOld(structuralControlITE(4, rare, xorOne, f.old)),
		"XOR-one selected arm":       changedArm,
		"XOR-one whole result":       structuralControlBinary("xor", 4, f.right, structuralControlConst(1, 4)),
	}
	for name, wrong := range tests {
		t.Run(name, func(t *testing.T) {
			for _, swapped := range []bool{false, true} {
				for _, reverse := range []bool{false, true} {
					left, right := f.left, wrong
					if swapped {
						left, right = right, left
					}
					s := newStructuralCases(structuralControlLimits())
					s.reverse = reverse
					if s.equal(left, right) {
						t.Fatalf("preferred ordering proved a reachable difference: swapped=%v reverse=%v", swapped, reverse)
					}
				}
			}
			structuralOrderEvaluate(t, f, f.left, wrong, false)
		})
	}
}

func TestStructuralCasesOrderUndeclaredParameterFallsBack(t *testing.T) {
	f := newStructuralOrderFixture("mode", "eq", false)
	f.tag.left.declared = 0 // the opposite comparison shares this parameter
	s := newStructuralCases(structuralControlLimits())
	roots, ok := s.importTerms(f.left, f.right)
	if !ok {
		t.Fatal("declared=0 is an admitted term, even though it is not a preferred discriminator")
	}
	if guard := s.discriminator(roots[0], roots[1]); guard != -1 || s.exhausted {
		t.Fatal("a parameter without an explicit declaration became a preferred discriminator")
	}
	guard := s.split(roots[0], roots[1])
	if guard < 0 || s.nodes[guard].kind != termCmp || s.nodes[s.nodes[guard].left].name != "read.index" || s.nodes[s.nodes[guard].right].name != "write.index" {
		t.Fatal("undeclared parameter did not preserve the legacy structural guard choice")
	}
	limits := structuralControlLimits()
	limits.depth = 1
	if newStructuralCases(limits).equal(f.left, f.right) {
		t.Fatal("legacy fallback unexpectedly bypassed the depth-one bound")
	}
	if !structurallyEqualByCases(f.left, f.right) {
		t.Fatal("legacy guard selection no longer proves the admitted undeclared-parameter control")
	}
	structuralOrderEvaluate(t, f, f.left, f.right, true)
}

func TestStructuralCasesOrderIgnoresUnsharedAndStaleGuards(t *testing.T) {
	f := newStructuralOrderFixture("mode", "eq", false)
	h, x := structuralControlParam("h", 1), structuralControlParam("x", 1)
	left := structuralControlITE(1, h, f.tag, structuralControlConst(0, 1))
	right := structuralControlITE(1, h, x, structuralControlConst(0, 1))
	for _, pair := range [][2]*term{{left, right}, {right, left}} {
		s := newStructuralCases(structuralControlLimits())
		roots, ok := s.importTerms(pair[0], pair[1])
		if !ok || s.discriminator(roots[0], roots[1]) != -1 || s.exhausted {
			t.Fatal("a comparison reachable in only one root was treated as shared")
		}
		if s.equal(pair[0], pair[1]) {
			t.Fatal("an unshared discriminator erased a real difference")
		}
	}
	s := newStructuralCases(structuralControlLimits())
	if !s.equal(f.left, f.right) {
		t.Fatal("could not prime the interner with an earlier discriminator")
	}
	a, b := structuralControlDistribution(4, h, structuralControlParam("a", 4), structuralControlParam("b", 4), structuralControlParam("c", 4))
	roots, ok := s.importTerms(a, b)
	if !ok || s.discriminator(roots[0], roots[1]) != -1 || s.exhausted {
		t.Fatal("an unreachable discriminator from a previous query affected current selection")
	}
	if !s.equal(a, b) {
		t.Fatal("a previous query prevented normal fallback on the current roots")
	}
}

func TestStructuralCasesOrderIrrelevantSharedGuardRespectsDepth(t *testing.T) {
	f := newStructuralOrderFixture("mode", "eq", false)
	irrelevant := structuralControlCmp("eq", structuralControlParam("irrelevant", 4), structuralControlConst(0, 4))
	common := structuralControlITE(4, irrelevant, structuralControlConst(2, 4), structuralControlConst(3, 4))
	left := structuralControlBinary("add", 4, common, f.left)
	right := structuralControlBinary("add", 4, common, f.right)
	for _, reverse := range []bool{false, true} {
		if got := structuralOrderSelected(t, left, right); got != `"irrelevant"/4/4=0/4/0` {
			t.Fatalf("the control must first encounter the shared irrelevant guard, got %s", got)
		}
		limits := structuralControlLimits()
		limits.depth = 1
		bounded := newStructuralCases(limits)
		bounded.reverse = reverse
		if bounded.equal(left, right) {
			t.Fatal("an irrelevant preferred guard bypassed the remaining depth bound")
		}
		complete := newStructuralCases(structuralControlLimits())
		complete.reverse = reverse
		if !complete.equal(left, right) || complete.leaves != 4 {
			t.Fatalf("a fresh proof must retain both outcomes of both guards, got %d leaves", complete.leaves)
		}
	}
	f.names = append(f.names, "irrelevant")
	f.widths["irrelevant"] = 4
	if !structuralControlBDDEqual(t, left, right, f.names, f.widths) {
		t.Fatal("independent BDD disagrees with the irrelevant-guard positive control")
	}
	for kind := uint64(0); kind < 16; kind++ {
		for nuisance := uint64(0); nuisance < 16; nuisance++ {
			for index := uint64(0); index < 4; index++ {
				for write := uint64(0); write < 4; write++ {
					env := map[string]uint64{"mode": kind, "irrelevant": nuisance, "read.index": index, "write.index": write}
					if left.eval(env) != right.eval(env) {
						t.Fatal("accepted irrelevant-guard proof failed exhaustive scalar evaluation")
					}
				}
			}
		}
	}
}

func TestStructuralCasesOrderBudgetsAndQueryIsolation(t *testing.T) {
	f := newStructuralOrderFixture("selector", "eq", false)
	baseline := newStructuralCases(structuralControlLimits())
	if !baseline.equal(f.left, f.right) || baseline.leaves != 2 {
		t.Fatal("budget control requires a completed discriminator-first proof")
	}
	admission := newStructuralCases(structuralControlLimits())
	if _, ok := admission.importTerms(f.left, f.right); !ok {
		t.Fatal("could not measure source admission independently")
	}
	for _, resource := range []string{"inputs", "nodes", "selection work", "work after first leaf", "depth"} {
		t.Run(resource, func(t *testing.T) {
			limits := structuralControlLimits()
			switch resource {
			case "inputs":
				limits.inputs = len(structuralControlSnapshot(f.left, f.right)) - 1
			case "nodes":
				limits.nodes = len(baseline.nodes) - 1
			case "selection work":
				limits.work = admission.work + 1 // the next visit belongs to guard selection
			case "work after first leaf":
				limits.work = baseline.work - 1
			case "depth":
				limits.depth = 0
			}
			s := newStructuralCases(limits)
			if s.equal(f.left, f.right) {
				t.Fatal("preferred guard bypassed an existing resource bound")
			}
			if resource == "work after first leaf" && s.leaves != 1 {
				t.Fatalf("work exhaustion must occur after one completed leaf, got %d", s.leaves)
			}
			if s.work > limits.work || len(s.nodes) > limits.nodes {
				t.Fatal("guard discovery exceeded its shared work/node cap")
			}
			if s.equal(structuralControlConst(0, 4), structuralControlConst(1, 4)) {
				t.Fatal("failed guard selection contaminated a later unequal query")
			}
			if !structurallyEqualByCases(f.left, f.right) {
				t.Fatal("resource failure contaminated a fresh valid query")
			}
		})
	}
}
