package borrowchecker

import "testing"

// Region-indexed borrowed returns, increment 1 (docs/spec/50-borrowing.md
// section 8c): a `[]T` return with exactly one `[]T` parameter borrows from
// that parameter; the body's result must trace to it (OAK-B0113 otherwise);
// the caller's binding is a reborrow of the argument.

func checkSource(t *testing.T, src string) *BorrowChecker {
	t.Helper()
	bc, program, tc := setupBorrowCheckerForTest(src)
	if program == nil {
		t.Fatalf("failed to parse:\n%s", src)
	}
	bc.CheckProgram(program, tc.Env())
	return bc
}

func TestRegionReturnFromParameterIsAccepted(t *testing.T) {
	for name, src := range map[string]string{
		"subslice":     "fn frame(buf: []u8, at: u32) -> []u8 { subslice(buf, at, 2) }",
		"parameter":    "fn same(buf: []u8) -> []u8 { buf }",
		"local":        "fn viaLocal(buf: []u8) -> []u8 { t: []u8 = subslice(buf, 1, 2)\nt }",
		"slice":        "fn head(buf: []u8, n: u32) -> []u8 { buf[0:n] }",
		"conditional":  "fn pick(buf: []u8, first: Bool) -> []u8 { first ? { subslice(buf, 0, 1) } | { subslice(buf, 1, 1) } }",
		"nested-call":  "fn frame(buf: []u8, at: u32) -> []u8 { subslice(buf, at, 2) }\nfn twice(buf: []u8) -> []u8 { frame(frame(buf, 1), 0) }",
		"other-params": "fn frame(buf: []u8, at: u32, limit: [4]u32, flag: Bool) -> []u8 { subslice(buf, at, 1) }",
	} {
		bc := checkSource(t, src)
		if len(bc.Diagnostics()) != 0 {
			t.Fatalf("%s: expected clean, got %#v", name, bc.Diagnostics())
		}
	}
}

func TestRegionReturnOfLocalOwnerIsRejected(t *testing.T) {
	src := "fn dangle(buf: []u8) -> []u8 { local: [4]u8 = [4]u8{ 1, 2, 3, 4 }\nview(&local) }"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeReturnedBorrowRegion)); got != 1 {
		t.Fatalf("local owner escape produced %d OAK-B0113, want 1: %#v", got, bc.Diagnostics())
	}
	if got := countDiagnosticsWithCode(bc, string(CodeBorrowEscape)); got != 0 {
		t.Fatalf("region-indexed signature must not also report OAK-B0109: %#v", bc.Diagnostics())
	}
}

func TestRegionReturnOfLocalSliceIsRejected(t *testing.T) {
	src := "fn dangle(buf: []u8) -> []u8 { local: [4]u8 = [4]u8{ 1, 2, 3, 4 }\nlocal[0:2] }"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeReturnedBorrowRegion)); got != 1 {
		t.Fatalf("local slice escape produced %d OAK-B0113, want 1: %#v", got, bc.Diagnostics())
	}
}

func TestRegionReturnMixedConditionalIsRejected(t *testing.T) {
	src := "fn mixed(buf: []u8, first: Bool) -> []u8 { local: [4]u8 = [4]u8{ 1, 2, 3, 4 }\nfirst ? { subslice(buf, 0, 1) } | { view(&local) } }"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeReturnedBorrowRegion)); got != 1 {
		t.Fatalf("mixed conditional produced %d OAK-B0113, want 1: %#v", got, bc.Diagnostics())
	}
}

func TestTwoCandidateParametersStayRejected(t *testing.T) {
	// Two view parameters of the return's element type: no elision; the
	// conservative rule applies until explicit regions land.
	src := "fn split(a: []u8, b: []u8) -> []u8 { a }"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeBorrowEscape)); got != 1 {
		t.Fatalf("two candidates produced %d OAK-B0109, want 1: %#v", got, bc.Diagnostics())
	}
}

func TestOwnedArrayParameterIsNotACandidate(t *testing.T) {
	// A by-value array parameter is a local owner; a view of it dangles.
	src := "fn dangle(buf: [16]u8) -> []u8 { buf[0:8] }"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeBorrowEscape)); got != 1 {
		t.Fatalf("owned parameter produced %d OAK-B0109, want 1: %#v", got, bc.Diagnostics())
	}
}

func TestElementTypeMustMatch(t *testing.T) {
	src := "fn reinterpret(buf: []u8) -> []u32 { view_as[u32](buf) }"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeBorrowEscape)); got != 1 {
		t.Fatalf("element mismatch produced %d OAK-B0109, want 1: %#v", got, bc.Diagnostics())
	}
}

func TestCallerBindingReborrowsTheArgument(t *testing.T) {
	// The result keeps the owner read-only while it lives.
	src := "fn frame(buf: []u8, at: u32) -> []u8 { subslice(buf, at, 2) }\n" +
		"fn use() -> u8 { data: [4]u8 = [4]u8{ 1, 2, 3, 4 }\nv: []u8 = view(&data)\nf: []u8 = frame(v, 1)\ndata[0] = 9\nf[0] }"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeOwnerWrittenDuringView)); got != 1 {
		t.Fatalf("owner write while the returned view lives produced %d OAK-B0103, want 1: %#v", got, bc.Diagnostics())
	}
	if got := countDiagnosticsWithCode(bc, string(CodeReturnedBorrowRegion)); got != 0 {
		t.Fatalf("unexpected OAK-B0113: %#v", bc.Diagnostics())
	}
}

func TestCallerBindingFromInlineViewAndBlockScope(t *testing.T) {
	// view(&owner) inline in the region position; the borrow ends with the
	// block, so the owner is writable afterwards.
	src := "fn frame(buf: []u8, at: u32) -> []u8 { subslice(buf, at, 2) }\n" +
		"fn use() -> u8 { data: [4]u8 = [4]u8{ 1, 2, 3, 4 }\ni: u32 = 0\nwhile i < 1 { f: []u8 = frame(view(&data), 1)\ndata[1] = f[0]\ni = i + 1 }\ndata[0] = 9\ndata[0] }"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeOwnerWrittenDuringView)); got != 1 {
		t.Fatalf("expected exactly the in-block write to be rejected, got %d: %#v", got, bc.Diagnostics())
	}
}

func TestCallerBindingFromSpanArgumentFailsClosed(t *testing.T) {
	// A span cannot be the region source of a read-only result in this
	// increment: the result would be a view coexisting with a writable span.
	src := "fn frame(buf: []u8, at: u32) -> []u8 { subslice(buf, at, 2) }\n" +
		"fn use() -> u8 { data: [4]u8 = [4]u8{ 1, 2, 3, 4 }\ns: [*]u8 = span(&data)\nf: []u8 = frame(s, 1)\nf[0] }"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeReturnedBorrowRegion)); got != 1 {
		t.Fatalf("span argument produced %d OAK-B0113, want 1: %#v", got, bc.Diagnostics())
	}
}
