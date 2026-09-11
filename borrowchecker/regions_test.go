package borrowchecker

import (
	"strings"
	"testing"
)

// Region-indexed borrowed returns, increment 1 (docs/spec/50-borrowing.md
// section 8c): a `[]T` return with exactly one `[]T` parameter borrows from
// that parameter; the body's result must trace to it (OAK-B0113 otherwise);
// the caller's binding is a reborrow of the argument.

func diagText(bc *BorrowChecker) string {
	var out []string
	for _, d := range bc.Diagnostics() {
		out = append(out, d.PlainText())
	}
	return strings.Join(out, "\n")
}

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

// Increment 2: explicit region parameters and span returns.

func TestExplicitRegionSelectsAmongCandidates(t *testing.T) {
	src := "pick[R]: (a: View[u8, R], b: []u8): View[u8, R] = subslice(a, 0, 1)"
	bc := checkSource(t, src)
	if len(bc.Diagnostics()) != 0 {
		t.Fatalf("explicit region must admit two view parameters, got %#v", bc.Diagnostics())
	}
	wrong := "pick[R]: (a: View[u8, R], b: []u8): View[u8, R] = subslice(b, 0, 1)"
	bc = checkSource(t, wrong)
	if got := countDiagnosticsWithCode(bc, string(CodeReturnedBorrowRegion)); got != 1 {
		t.Fatalf("returning the other parameter produced %d OAK-B0113, want 1: %#v", got, bc.Diagnostics())
	}
}

func TestExplicitRegionSignatureValidation(t *testing.T) {
	cases := map[string]string{
		"names no parameter":   "orphan[R]: (a: []u8): View[u8, R] = a",
		"names two parameters": "both[R]: (a: View[u8, R], b: View[u8, R]): View[u8, R] = a",
		"view from span":       "narrow[R]: (a: Span[u8, R]): View[u8, R] = a",
	}
	for name, src := range cases {
		bc := checkSource(t, src)
		if got := countDiagnosticsWithCode(bc, string(CodeReturnedBorrowRegion)); got != 1 {
			t.Fatalf("%s: produced %d OAK-B0113, want 1: %#v", name, got, bc.Diagnostics())
		}
		if got := countDiagnosticsWithCode(bc, string(CodeBorrowEscape)); got != 0 {
			t.Fatalf("%s: an invalid region signature must not also report OAK-B0109: %#v", name, bc.Diagnostics())
		}
	}
}

func TestSpanReturnIsAReborrow(t *testing.T) {
	// Elided: one span parameter, span return. The result suspends the
	// argument span while it lives (OAK-B0107), and ends with the block.
	src := "fn tail(buf: [*]u8, from: u32) -> [*]u8 { subslice(buf, from, 1) }\n" +
		"fn use() -> u8 { data: [4]u8 = [4]u8{ 1, 2, 3, 4 }\ns: [*]u8 = span(&data)\nt: [*]u8 = tail(s, 2)\nt[0] = 9\ns[0] = 1\nt[0] }"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeBorrowSuspended)); got != 1 {
		t.Fatalf("parent span use while the returned span lives produced %d OAK-B0107, want 1: %#v", got, bc.Diagnostics())
	}
	if got := countDiagnosticsWithCode(bc, string(CodeReturnedBorrowRegion)); got != 0 {
		t.Fatalf("unexpected OAK-B0113: %#v", bc.Diagnostics())
	}
	clean := "fn tail(buf: [*]u8, from: u32) -> [*]u8 { subslice(buf, from, 1) }\n" +
		"fn use() -> u8 { data: [4]u8 = [4]u8{ 1, 2, 3, 4 }\nt: [*]u8 = tail(span(&data), 2)\nt[0] = 9\nt[0] }"
	bc = checkSource(t, clean)
	if len(bc.Diagnostics()) != 0 {
		t.Fatalf("span from an inline span(&owner) must be clean, got %#v", bc.Diagnostics())
	}
}

func TestSpanReturnFromLocalIsRejected(t *testing.T) {
	src := "fn dangle(buf: [*]u8) -> [*]u8 { local: [4]u8 = [4]u8{ 1, 2, 3, 4 }\nspan(&local) }"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeReturnedBorrowRegion)); got != 1 {
		t.Fatalf("span of a local produced %d OAK-B0113, want 1: %#v", got, bc.Diagnostics())
	}
}

// Increment 3: records carrying a region cross calls.

const cursorPrelude = "Cursor[R]: type = struct { data: View[u8, R], pos: u32 }\n" +
	"open[R]: (buf: View[u8, R]): Cursor[R] = Cursor { data: buf, pos: 0 }\n" +
	"advance[R]: (c: Cursor[R], n: u32): Cursor[R] = Cursor { data: c.data, pos: c.pos + n }\n" +
	"rest[R]: (c: Cursor[R]): View[u8, R] = subslice(c.data, c.pos, 1)\n"

func TestRegionRecordCrossesCalls(t *testing.T) {
	src := cursorPrelude +
		"fn use() -> u8 { data: [4]u8 = [4]u8{ 1, 2, 3, 4 }\nv: []u8 = view(&data)\nc: Cursor = open(v)\nd: Cursor = advance(c, 2)\nr: []u8 = rest(d)\ndata[0] = 9\nr[0] }"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeOwnerWrittenDuringView)); got != 1 {
		t.Fatalf("owner write while the cursor chain lives produced %d OAK-B0103, want 1: %#v", got, bc.Diagnostics())
	}
	for _, code := range []string{string(CodeReturnedBorrowRegion), string(CodeBorrowEscape)} {
		if got := countDiagnosticsWithCode(bc, code); got != 0 {
			t.Fatalf("unexpected %s: %#v", code, bc.Diagnostics())
		}
	}
}

func TestRegionRecordLocalMayBePassed(t *testing.T) {
	// A section 8b local record whose borrows are tracked passes to a
	// region-declared parameter; a plain record parameter still refuses.
	src := cursorPrelude +
		"fn use() -> u8 { data: [4]u8 = [4]u8{ 1, 2, 3, 4 }\nc: Cursor = Cursor { data: view(&data), pos: 1 }\nr: []u8 = rest(c)\nr[0] }"
	bc := checkSource(t, src)
	if len(bc.Diagnostics()) != 0 {
		t.Fatalf("passing a tracked local record to a region parameter must be clean, got %#v", bc.Diagnostics())
	}
	plain := "Cursor: type = struct { data: []u8, pos: u32 }\n" +
		"fn peek(c: Cursor) -> u8 { c.data[0] }\n" +
		"fn use() -> u8 { data: [4]u8 = [4]u8{ 1, 2, 3, 4 }\nc: Cursor = Cursor { data: view(&data), pos: 1 }\npeek(c) }"
	bc = checkSource(t, plain)
	if got := countDiagnosticsWithCode(bc, string(CodeBorrowEscape)); got == 0 {
		t.Fatalf("a record parameter without a region must still fail closed: %#v", bc.Diagnostics())
	}
}

func TestRegionRecordReturnOfLocalIsRejected(t *testing.T) {
	src := "Cursor[R]: type = struct { data: View[u8, R], pos: u32 }\n" +
		"bad[R]: (buf: View[u8, R]): Cursor[R] {\n  local: [4]u8 = [4]u8{ 1, 2, 3, 4 }\n  Cursor { data: view(&local), pos: 0 }\n}"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeReturnedBorrowRegion)); got != 1 {
		t.Fatalf("record of a local produced %d OAK-B0113, want 1: %#v", got, bc.Diagnostics())
	}
}

// Increment 4: ADT payloads carry regions, and a match arm's payload binding
// reborrows what the scrutinee carries under that variant.

const framePrelude = "Frame[R]: type = struct { kind: u32, payload: View[u8, R] }\n" +
	"FrameError: type = | Short | Bad\n" +
	"Result[T, E]: type = Ok: T | Err: E\n" +
	"Option[T]: type = Some: T | None\n" +
	"parse[R]: (src: View[u8, R]): Result[Frame[R], FrameError] = len(src) < u32(2) ? { .Err(.Short) } | { .Ok(Frame { kind: u32(src[0]), payload: subslice(src, u32(1), len(src) - u32(1)) }) }\n" +
	"first[R]: (src: View[u8, R]): Option[View[u8, R]] = len(src) == u32(0) ? { .None } | { .Some(subslice(src, u32(0), u32(1))) }\n" +
	"body[R]: (f: Frame[R]): View[u8, R] = f.payload\n"

func TestRegionADTPayloadsCrossCalls(t *testing.T) {
	src := framePrelude +
		"use: (data: []u8): u32 {\n  r: Result[Frame, FrameError] = parse(data)\n  r ? | .Ok(f) => { b: []u8 = body(f)\n u32(b[0]) + f.kind } | .Err(e) => u32(0)\n}"
	bc := checkSource(t, src)
	if len(bc.Diagnostics()) != 0 {
		t.Fatalf("ADT payload crossing calls must be clean, got %s", diagText(bc))
	}
}

func TestRegionADTPayloadKeepsOwnerBorrowed(t *testing.T) {
	src := framePrelude +
		"use: (): u32 {\n  data: [4]u8 = [4]u8{ 1, 2, 3, 4 }\n  r: Result[Frame, FrameError] = parse(view(&data))\n  data[0] = 9\n  r ? | .Ok(f) => f.kind | .Err(e) => u32(0)\n}"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeOwnerWrittenDuringView)); got != 1 {
		t.Fatalf("owner write while the Result lives produced %d OAK-B0103, want 1: %s", got, diagText(bc))
	}
}

func TestRegionOptionViewPayload(t *testing.T) {
	src := framePrelude +
		"use: (): u32 {\n  data: [4]u8 = [4]u8{ 1, 2, 3, 4 }\n  o: Option[[]u8] = first(view(&data))\n  o ? | .Some(v) => { data[1] = 7\n u32(v[0]) } | .None => u32(0)\n}"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeOwnerWrittenDuringView)); got != 1 {
		t.Fatalf("owner write inside the Some arm produced %d OAK-B0103, want 1: %s", got, diagText(bc))
	}
	// The Option binding itself is lexical: hold it in a helper so the owner
	// is free again after the call.
	clean := framePrelude +
		"pick: (data: []u8): u32 {\n  o: Option[[]u8] = first(data)\n  o ? | .Some(v) => u32(v[0]) | .None => u32(0)\n}\n" +
		"use: (): u32 {\n  data: [4]u8 = [4]u8{ 1, 2, 3, 4 }\n  n: u32 = pick(view(&data))\n  data[1] = 7\n  n\n}"
	bc = checkSource(t, clean)
	if len(bc.Diagnostics()) != 0 {
		t.Fatalf("a payload borrow held in a helper ends with the helper; writing after the call must be clean: %s", diagText(bc))
	}
}

func TestRegionADTReturnOfLocalIsRejected(t *testing.T) {
	src := framePrelude +
		"bad[R]: (src: View[u8, R]): Result[Frame[R], FrameError] {\n  local: [4]u8 = [4]u8{ 1, 2, 3, 4 }\n  .Ok(Frame { kind: u32(0), payload: view(&local) })\n}"
	bc := checkSource(t, src)
	if got := countDiagnosticsWithCode(bc, string(CodeReturnedBorrowRegion)); got != 1 {
		t.Fatalf("ADT payload of a local produced %d OAK-B0113, want 1: %s", got, diagText(bc))
	}
}
