package asm

import (
	"strings"
	"testing"
)

const loopTrapCountSource = "{\n i: u32 = u32(0)\n while i < n {\n  i = i + u32(1)\n }\n i\n}"

const loopTrapCountMachine = "  bind w0 = n\n  clobber w9\n  mov w9, #0\nloop:\n  cmp w9, w0\n  b.hs done\n  cmp w9, #1234\n  b.eq trap\n  add w9, w9, #1\n  b loop\ndone:\n  mov w0, w9\n  ret\ntrap:\n  brk #1"

func TestVerifyLoopTrapOutsideWitnesses(t *testing.T) {
	v := verifyCase(t, "count: (n: u32) -> u32", loopTrapCountSource, loopTrapCountMachine)
	if v.Kind != VerdictWitnessed || !strings.Contains(v.Message, "body trap-domain obligation") {
		t.Fatalf("a trap on iteration 1234 must not disappear from the loop proof: %s", v.Message)
	}
}

func TestVerifyLoopHeaderTrapDomain(t *testing.T) {
	old := "  cmp w9, w0\n  b.hs done\n  cmp w9, #1234\n  b.eq trap\n"
	header := strings.Replace(loopTrapCountMachine, old, "  cmp w9, #1234\n  b.eq trap\n  cmp w9, w0\n  b.hs done\n", 1)
	bodyAssert := strings.Replace(loopTrapCountSource, "  i =", "  assert(i != u32(1234))\n  i =", 1)
	headerAssert := strings.Replace(loopTrapCountSource, "while i < n", "while (true ? {\n assert(i != u32(1234))\n i\n} | u32(0)) < n", 1)
	for _, test := range []struct {
		name, source string
		want         VerdictKind
	}{{"no_source_trap", loopTrapCountSource, VerdictWitnessed}, {"body_cannot_justify_exiting_header", bodyAssert, VerdictWitnessed}, {"matching_header", headerAssert, VerdictProven}} {
		t.Run(test.name, func(t *testing.T) {
			v := verifyCase(t, "count: (n: u32) -> u32", test.source, header)
			if v.Kind != test.want {
				t.Fatalf("want %s, got %s: %s", test.want, v.Kind, v.Message)
			}
		})
	}
}

func TestVerifyLoopRootTrapDomain(t *testing.T) {
	machine := strings.Replace(loopTrapCountMachine, "loop:\n", "  cmp w0, #1234\n  b.eq trap\nloop:\n", 1)
	machine = strings.Replace(machine, "  cmp w9, #1234\n  b.eq trap\n", "", 1)
	bodyAssert := strings.Replace(loopTrapCountSource, "  i =", "  assert(i != u32(1234))\n  i =", 1)
	for _, source := range []string{loopTrapCountSource, bodyAssert} {
		v := verifyCase(t, "count: (n: u32) -> u32", source, machine)
		if v.Kind != VerdictWitnessed || !strings.Contains(v.Message, "root trap-domain obligation") {
			t.Fatalf("a loop-body trap cannot justify the early n=1234 trap: %s: %s", v.Kind, v.Message)
		}
	}
	rootAssert := strings.Replace(loopTrapCountSource, "{\n", "{\n assert(n != u32(1234))\n", 1)
	if v := verifyCase(t, "count: (n: u32) -> u32", rootAssert, machine); v.Kind != VerdictProven {
		t.Fatalf("matching root guards must still prove: %s: %s", v.Kind, v.Message)
	}
}

func TestVerifyLoopRootGuardHoist(t *testing.T) {
	source := strings.Replace(loopTrapCountSource, "  i =", "  assert(b != u32(1234))\n  i =", 1)
	machine := strings.Replace(loopTrapCountMachine, "  bind w0 = n\n", "  bind w0 = n\n  bind w1 = b\n", 1)
	machine = strings.Replace(machine, "  cmp w9, #1234\n  b.eq trap\n", "", 1)
	machine = strings.Replace(machine, "loop:\n", "  cbz w0, done\n  cmp w1, #1234\n  b.eq trap\nloop:\n", 1)
	if v := verifyCase(t, "count: (n, b: u32) -> u32", source, machine); v.Kind != VerdictProven {
		t.Fatalf("a first-iteration assertion may justify a guarded hoist: %s: %s", v.Kind, v.Message)
	}
	wrong := strings.Replace(machine, "  cbz w0, done\n", "", 1)
	if v := verifyCase(t, "count: (n, b: u32) -> u32", source, wrong); v.Kind != VerdictWitnessed || !strings.Contains(v.Message, "root trap-domain obligation") {
		t.Fatalf("a zero-trip source has no body assertion: %s: %s", v.Kind, v.Message)
	}
}

func TestFirstIterationTrapRequiresEntryState(t *testing.T) {
	i := paramTerm("loop1.i", 32)
	ev := &loopEvent{index: 1, cond: constTerm(1, 1), fresh: map[string]*term{"i": i}, header: map[string]*term{"i": constTerm(0, 32)}, entry: map[string][]*spanWrite{"p": nil}}
	ev.bodyTrap = cmpTerm("eq", selectTerm("loop1.p", i, 32), constTerm(7, 32))
	projected, known := firstIterationTrap(ev, 2)
	if !known {
		t.Fatalf("the first trap must read exact entry memory: %s, known=%v", projected, known)
	}
	for _, value := range []uint64{0, 7, 8} {
		want := uint64(0)
		if value == 7 {
			want = 1
		}
		if got := projected.eval(map[string]uint64{"p[0]": value, "p[1]": 7}); got != want {
			t.Fatalf("entry-memory trap at p[0]=%d: got %d, want %d (%s)", value, got, want, projected)
		}
	}
	for _, unknown := range []*term{paramTerm("loop2.j", 32), selectTerm("loop2.p", i, 32), paramTerm("loop2[0].p", 32), paramTerm("loop1.orphan", 32)} {
		ev.bodyTrap = cmpTerm("eq", unknown, constTerm(7, 32))
		if projected, known := firstIterationTrap(ev, 2); known {
			t.Fatalf("a hypothetical state %s escaped to the outer scope: %s", unknown, projected)
		}
	}
}

func TestVerifyNestedLoopTrapScopes(t *testing.T) {
	source := "{\n i: u32 = u32(0)\n while i < n {\n  j: u32 = u32(0)\n  while j < m {\n   assert(j != u32(1234))\n   j = j + u32(1)\n  }\n  i = i + u32(1)\n }\n i\n}"
	machine := "  bind w0 = n\n  bind w1 = m\n  clobber w9, w10\n  mov w9, #0\nouter:\n  cmp w9, w0\n  b.hs done\n  cmp w9, #1234\n  b.eq trap\n  mov w10, #0\ninner:\n  cmp w10, w1\n  b.hs next\n  cmp w10, #1234\n  b.eq trap\n  add w10, w10, #1\n  b inner\nnext:\n  add w9, w9, #1\n  b outer\ndone:\n  mov w0, w9\n  ret\ntrap:\n  brk #1"
	v := verifyCase(t, "nested: (n, m: u32) -> u32", source, machine)
	if v.Kind != VerdictWitnessed || !strings.Contains(v.Message, "loop 1 body trap-domain obligation") {
		t.Fatalf("an inner iteration's trap must not justify the outer guard: %s: %s", v.Kind, v.Message)
	}
	matching := strings.Replace(source, "  j: u32", "  assert(i != u32(1234))\n  j: u32", 1)
	if v := verifyCase(t, "nested: (n, m: u32) -> u32", matching, machine); v.Kind != VerdictProven {
		t.Fatalf("each loop's own matching trap must prove: %s: %s", v.Kind, v.Message)
	}
}

func TestVerifyLoopTrapBranchAndMemory(t *testing.T) {
	source := "{\n i: u32 = u32(0)\n while i < n {\n  b == u32(0) ? { assert(i != u32(1234)) } | { }\n  i = i + u32(1)\n }\n i\n}"
	machine := strings.Replace(loopTrapCountMachine, "  bind w0 = n\n", "  bind w0 = n\n  bind w1 = b\n", 1)
	if v := verifyCase(t, "count: (n, b: u32) -> u32", source, machine); v.Kind != VerdictWitnessed {
		t.Fatalf("an assertion on only one arm cannot justify both: %s: %s", v.Kind, v.Message)
	}
	machine = strings.Replace(machine, "  cmp w9, #1234", "  cbnz w1, next\n  cmp w9, #1234", 1)
	machine = strings.Replace(machine, "  add w9, w9, #1", "next:\n  add w9, w9, #1", 1)
	if v := verifyCase(t, "count: (n, b: u32) -> u32", source, machine); v.Kind != VerdictProven {
		t.Fatalf("the correctly guarded trap must prove: %s: %s", v.Kind, v.Message)
	}
	writer := "  bind x0, w1 = v\n  bind w2 = n\n  clobber w9\n  mov w9, #0\nloop:\n  cmp w9, w2\n  b.hs done\n  cmp w9, #1234\n  b.eq trap\n  cmp w9, w1\n  b.hs trap\n  str wzr, [x0, w9, uxtw #2]\n  add w9, w9, #1\n  b loop\ndone:\n  ret\ntrap:\n  brk #1"
	writeSource := "{\n i: u32 = u32(0)\n while i < n {\n  v[i] = u32(0)\n  i = i + u32(1)\n }\n}"
	v := verifyCase(t, "fill: (v: [*]u32, n: u32) -> ()", writeSource, writer)
	if v.Kind != VerdictWitnessed || !strings.Contains(v.Message, "trap-domain obligation") {
		t.Fatalf("a memory-only loop must not bypass trap admission: %s: %s", v.Kind, v.Message)
	}
	writer = strings.Replace(writer, "  cmp w9, #1234\n  b.eq trap\n", "", 1)
	if v := verifyCase(t, "fill: (v: [*]u32, n: u32) -> ()", writeSource, writer); v.Kind != VerdictProven {
		t.Fatalf("matching span bounds must still prove: %s: %s", v.Kind, v.Message)
	}
}

func TestVerifyLoopTrapMatchingAssert(t *testing.T) {
	source := strings.Replace(loopTrapCountSource, "  i =", "  assert(i != u32(1234))\n  i =", 1)
	v := verifyCase(t, "count: (n: u32) -> u32", source, loopTrapCountMachine)
	if v.Kind != VerdictProven {
		t.Fatalf("a matching per-iteration assertion must prove: %s: %s", v.Kind, v.Message)
	}
}

func TestLoopTrapMetadataSurvivesMergeAndSubstitution(t *testing.T) {
	event := func(header, body *term) *loopEvent {
		return &loopEvent{index: 1, cond: constTerm(1, 1), header: map[string]*term{}, next: map[string]*term{}, headerTrap: header, bodyTrap: body}
	}
	header, body := paramTerm("header", 1), paramTerm("body", 1)
	merged, reason, ok := mergeLoopEvents(paramTerm("path", 1), event(header, nil), event(nil, body))
	if !ok {
		t.Fatal(reason)
	}
	for path := uint64(0); path <= 1; path++ {
		for h := uint64(0); h <= 1; h++ {
			for b := uint64(0); b <= 1; b++ {
				env := map[string]uint64{"path": path, "header": h, "body": b}
				memo := mapMemo{}
				if got := memo.eval(merged.headerTrap, env); got != path&h {
					t.Fatalf("one-sided header trap lost its path: env %v, got %d", env, got)
				}
				if got := memo.eval(merged.bodyTrap, env); got != (1-path)&b {
					t.Fatalf("one-sided body trap lost its path: env %v, got %d", env, got)
				}
			}
		}
	}
	merged.substituteAll(map[string]*term{"header": constTerm(0, 1), "body": constTerm(1, 1)}, map[*term]*term{})
	for path := uint64(0); path <= 1; path++ {
		memo := mapMemo{}
		env := map[string]uint64{"path": path}
		if memo.eval(merged.headerTrap, env) != 0 || memo.eval(merged.bodyTrap, env) != 1-path {
			t.Fatalf("loop coupling did not substitute trap metadata: %s, %s", merged.headerTrap, merged.bodyTrap)
		}
	}
}

func TestVerifyLoopRecordArrayTrapDomain(t *testing.T) {
	const decl = "fill: (p: [*]Page, dom: u32, n: u32) -> ()"
	const source = "{\n i: u32 = u32(0)\n while i < n {\n  p[dom].words[i] = u64(0)\n  i = i + u32(1)\n }\n}"
	const machine = "  bind x0, w1 = p\n  bind w2 = dom\n  bind w3 = n\n  clobber x9, x10, x11\n  mov w9, #0\nloop:\n  cmp w9, w3\n  b.hs done\n  cmp w2, w1\n  b.hs trap\n  cmp w9, #2048\n  b.hs trap\n  mov w10, #16384\n  umaddl x11, w2, w10, x0\n  str xzr, [x11, w9, uxtw #3]\n  add w9, w9, #1\n  b loop\ndone:\n  ret\ntrap:\n  brk #1"
	for _, extra := range []bool{false, true} {
		body := machine
		if extra {
			body = strings.Replace(body, "  cmp w9, #2048", "  cmp w9, #1234\n  b.eq trap\n  cmp w9, #2048", 1)
		}
		unit, errs := ParseUnit("record_loop.oakasm", decl+" = {\n"+body+"\n}\n")
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		fn := unit.Functions[0]
		fn.Composites = map[string]Composite{"Page": {Size: 16384, Fields: []CompositeField{{Name: "words", Size: 16384, Elem: "u64", Length: 2048}}}}
		sig, err := parseSignatureWithBody(decl + " = " + source)
		if err != nil {
			t.Fatal(err)
		}
		if findings := Check(fn, sig, nil); len(findings) != 0 {
			t.Fatal(findings)
		}
		want := VerdictProven
		if extra {
			want = VerdictWitnessed
		}
		if v := Verify(fn, sig, sig.Body); v.Kind != want {
			t.Fatalf("record array loop (extra trap %v): want %s, got %s: %s", extra, want, v.Kind, v.Message)
		}
	}
}
