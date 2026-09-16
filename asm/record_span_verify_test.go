package asm

import (
	"strings"
	"testing"
)

// A record span's layout is indexed once even when an array field has the
// OS stage2 arena's full size. Machine and Oak field accesses then use exact
// offset/name lookups; the per-memory metadata stays proportional to fields,
// not to the array's enumerated scalar leaves.
func TestRecordSpanIndexesLargeArray(t *testing.T) {
	const pages int64 = 49152
	const pagesBytes = pages * 8
	composites := map[string]Composite{"Regime": {
		Size: pagesBytes + 8,
		Fields: []CompositeField{
			{Name: "pages", Offset: 0, Size: pagesBytes, Elem: "u64", Length: pages},
			{Name: "ready", Offset: pagesBytes, Size: 4, Scalar: "Bool"},
			{Name: "count", Offset: pagesBytes + 4, Size: 4, Scalar: "u32"},
		},
	}}
	sig, err := parseSignature("indexed: (s: [*]Regime) -> ()")
	if err != nil {
		t.Fatal(err)
	}
	arg, reason, isRecord, ok := recordSpanOf(composites, sig.Parameters[0].Type)
	if !isRecord || !ok {
		t.Fatalf("record span: isRecord=%v ok=%v reason=%q", isRecord, ok, reason)
	}
	if got, want := len(arg.leaves), int(pages+2); got != want {
		t.Fatalf("enumerated leaves = %d, want %d", got, want)
	}
	if got := len(arg.memoryFields); got != 3 {
		t.Fatalf("indexed memories = %d, want 3 (one per field, not one per array element)", got)
	}

	prefix, length, stride, found := arg.arrayFieldAt(0)
	if !found || prefix != ".pages" || length != pages || stride != 8 {
		t.Fatalf("pages array = (%q, %d, %d, %v), want (.pages, %d, 8, true)", prefix, length, stride, found, pages)
	}
	if _, _, _, found := arg.arrayFieldAt(8); found {
		t.Fatal("an interior array offset must not be accepted as the field's start")
	}
	field, found := arg.arrayNamed(".pages")
	if !found || field.length != pages || field.first.name != ".pages[0]" {
		t.Fatalf("pages field index = %+v, found=%v", field, found)
	}
	if _, found := arg.arrayNamed(".missing"); found {
		t.Fatal("an unknown array field must not resolve")
	}

	last, found := arg.leafAt((pages-1)*8, 8)
	if !found || last.name != ".pages[49151]" {
		t.Fatalf("last page leaf = %+v, found=%v", last, found)
	}
	if prefix, k, length, found := arg.arrayElementLeaf(last); !found || prefix != ".pages" || k != pages-1 || length != pages {
		t.Fatalf("last page element = (%q, %d, %d, %v)", prefix, k, length, found)
	}
	ready, found := arg.leafAt(pagesBytes, 4)
	if !found || ready.name != ".ready" || ready.width != 1 {
		t.Fatalf("Bool cell = %+v, found=%v", ready, found)
	}
	if _, found := arg.leafAt(pagesBytes, 1); found {
		t.Fatal("a Bool leaf must retain its four-byte storage contract")
	}
	if _, found := arg.leafNamed(".missing"); found {
		t.Fatal("an unknown scalar leaf must not resolve")
	}

	memories := arg.memories("s")
	wantMemories := []string{"s.pages", "s.ready", "s.count"}
	if len(memories) != len(wantMemories) {
		t.Fatalf("memories = %v, want %v", memories, wantMemories)
	}
	for i := range memories {
		if memories[i] != wantMemories[i] {
			t.Fatalf("memories = %v, want %v", memories, wantMemories)
		}
	}
	widths := arg.memoryWidths("s")
	if widths["s.pages"] != 64 || widths["s.ready"] != 1 || widths["s.count"] != 32 {
		t.Fatalf("memory widths = %v", widths)
	}
	if _, found := arg.memoryWidth(".missing"); found {
		t.Fatal("an unknown leaf memory must not resolve")
	}
}

// Spans of records are verified (docs/spec/94-assembler.md §9): a field
// read through an element address is the leaf's select term on both
// sides, so a reader is proven — and a lowering that reads the wrong
// field, or the wrong element, is a mismatch.
func TestVerifyRecordSpanReads(t *testing.T) {
	composites := map[string]Composite{"Node": {Size: 8, Fields: []CompositeField{
		{Name: "value", Offset: 0, Size: 4, Scalar: "u32"},
		{Name: "next", Offset: 4, Size: 4, Scalar: "u32"},
	}}}
	run := func(decl, oakBody, asmBody string) Verdict {
		t.Helper()
		unit, errs := ParseUnit("rs.oakasm", decl+" = {\n"+asmBody+"\n}\n")
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		unit.Functions[0].Composites = composites
		sig, err := parseSignature(decl)
		if err != nil {
			t.Fatal(err)
		}
		if findings := Check(unit.Functions[0], sig, nil); len(findings) != 0 {
			t.Fatalf("checker: %v", findings)
		}
		spec, err := parseSignatureWithBody(decl + " = " + oakBody)
		if err != nil {
			t.Fatal(err)
		}
		return Verify(unit.Functions[0], sig, spec.Body)
	}
	decl := "peek: (pool: []Node, i: u32) -> u32"
	prologue := "  bind x0, w1 = pool\n  bind w2 = i\n  clobber x9\n  cmp w2, w1\n  b.hs trap\n  add x9, x0, w2, uxtw #3\n"
	epilogue := "\n  ret\ntrap:\n  mov w0, wzr\n  ret"
	body := "{\n  i < len(pool) ? { pool[i].value } | { u32(0) }\n}"
	if v := run(decl, body, prologue+"  ldr w0, [x9]"+epilogue); v.Kind != VerdictProven {
		t.Fatalf("a field read through a record span element must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := run(decl, body, prologue+"  ldr w0, [x9, #4]"+epilogue); v.Kind != VerdictMismatch || !strings.Contains(v.Message, "disagrees") {
		t.Fatalf("reading the next field for the value must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	sum := "{\n  i < len(pool) ? { pool[i].value + pool[i].next } | { u32(0) }\n}"
	if v := run(decl, sum, prologue+"  ldr w0, [x9]\n  ldr w9, [x9, #4]\n  add w0, w0, w9"+epilogue); v.Kind != VerdictProven {
		t.Fatalf("two fields of one element must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := run(decl, sum, prologue+"  ldr w0, [x9]\n  add w0, w0, w0"+epilogue); v.Kind != VerdictMismatch {
		t.Fatalf("doubling the value for value + next must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	// Writers: the store lands in the leaf's memory and the final memories
	// are compared; storing into the wrong field is a mismatch.
	wdecl := "bump: (pool: [*]Node, i: u32) -> ()"
	wprologue := "  bind x0, w1 = pool\n  bind w2 = i\n  clobber x9, x10\n  cmp w2, w1\n  b.hs trap\n  add x9, x0, w2, uxtw #3\n"
	wbody := "{\n  i < len(pool) ? { pool[i].value = pool[i].next + u32(1) } | { }\n}"
	if v := run(wdecl, wbody, wprologue+"  ldr w10, [x9, #4]\n  add w10, w10, #1\n  str w10, [x9]"+epilogue); v.Kind != VerdictProven || !strings.Contains(v.Message, "span memory it writes (pool.value)") {
		t.Fatalf("a store into a record span's field must be proven in its memory, got %s: %s", v.Kind, v.Message)
	}
	if v := run(wdecl, wbody, wprologue+"  ldr w10, [x9, #4]\n  add w10, w10, #1\n  str w10, [x9, #4]"+epilogue); v.Kind != VerdictMismatch {
		t.Fatalf("storing into next for value must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
}

// The aligned-writes fast path only proves: two stores to one element
// under complementary conditions, logged in opposite orders by the two
// sides (the asm forks taken-first, the Oak body reads top-down), and a
// value read back through a guarded earlier store, decide by the memories
// rather than refuting on a pair (the false mismatches the final gate of
// #453 found).
func TestVerifyGuardedWritesDecideByMemory(t *testing.T) {
	decl := "pick: (out: [*]u32, k: u32) -> ()"
	oakBody := "{\n  u32(0) < len(out) ? {\n    k == u32(17) ? { out[u32(0)] = u32(1) } | { out[u32(0)] = u32(2) }\n  } | { }\n}"
	// The asm stores the else value on the taken (k != 17) path first.
	asmBody := "  bind x0, w1 = out\n  bind w2 = k\n  clobber x9\n  cmp w1, #1\n  b.lo done\n  cmp w2, #17\n  b.ne other\n  mov w9, #1\n  str w9, [x0]\n  b done\nother:\n  mov w9, #2\n  str w9, [x0]\ndone:\n  ret"
	unit, errs := ParseUnit("gw.oakasm", decl+" = {\n"+asmBody+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(unit.Functions[0], sig, nil); len(findings) != 0 {
		t.Fatalf("checker: %v", findings)
	}
	spec, err := parseSignatureWithBody(decl + " = " + oakBody)
	if err != nil {
		t.Fatal(err)
	}
	v := Verify(unit.Functions[0], sig, spec.Body)
	if v.Kind == VerdictMismatch {
		t.Fatalf("stores under complementary guards must not refute: %s", v.Message)
	}
	if v.Kind != VerdictProven {
		t.Fatalf("stores under complementary guards must be proven by the memories, got %s: %s", v.Kind, v.Message)
	}
}
