package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/typechecker"
)

// The wrapping-guard report (docs/spec/20-types.md §11.1a, OAK-T0701): an
// unsigned `+` or `*` inside an ordering comparison is listed by
// `oak vet` at information severity. It is a report, not a rejection: the
// operators' wrapping contract is frozen, and a rule that rejected every
// `i + 1 < n` would fire on every loop.
const guardWrapProgram = `
fits(off: u32, len: u32, cap: u32): Bool = off + len <= cap

room(off: u32, len: u32, cap: u32): Bool = len <= cap && off <= cap - len

count(n: u32): u32 {
  i: u32 = u32(0)
  total: u32 = u32(0)
  while i < n {
    total = total + i
    i = i + u32(1)
  }
  total
}

signed_guard(a: i32, b: i32, c: i32): Bool = a + b < c

main: (): i32 {
  fits(u32(1), u32(2), u32(4)) && room(u32(1), u32(2), u32(4)) && !signed_guard(1, 2, 3) ? { i32_bits_u32(count(u32(3)) - u32(3)) } | { 1 }
}
`

func guardWrapReports(t *testing.T, source string) []*diagnostic.Diagnostic {
	t.Helper()
	model, err := New().WithSource("guard.oak", source).SemanticModel().Get()
	if err != nil {
		t.Fatalf("semantic model failed: %v", err)
	}
	var reports []*diagnostic.Diagnostic
	for _, d := range model.Diagnostics {
		if d != nil && string(d.Code) == typechecker.CodeGuardWrap {
			reports = append(reports, d)
		}
	}
	return reports
}

func TestE2EGuardWrapReportedNotRejected(t *testing.T) {
	reports := guardWrapReports(t, guardWrapProgram)
	if len(reports) != 1 {
		t.Fatalf("got %d OAK-T0701 reports, want exactly one (the `off + len <= cap` guard): %v", len(reports), reports)
	}
	d := reports[0]
	if d.Severity != diagnostic.SeverityInformation {
		t.Fatalf("severity = %v, want information", d.Severity)
	}
	if !strings.Contains(d.Message, "unsigned `+` on u32") {
		t.Fatalf("message = %q", d.Message)
	}
	if len(d.Advice) == 0 || !strings.Contains(d.Advice[0].Message, "u32_checked_add") {
		t.Fatalf("advice = %v, want the checked spelling", d.Advice)
	}
	if d.Range.Start.Line != 1 {
		t.Fatalf("report at line %d, want line 1 (0-based) — the `fits` guard", d.Range.Start.Line)
	}

	// Information never rejects, in either profile.
	for _, profile := range []string{"default", "strict"} {
		if _, err := New().WithProfile(profile).WithSource("guard.oak", guardWrapProgram).EmitC().Get(); err != nil {
			t.Fatalf("%s profile rejected the program: %v", profile, err)
		}
	}
	code, abnormal := buildAndRun(t, "guardwrap", guardWrapProgram)
	if abnormal || code != 0 {
		t.Fatalf("exit = (%d, abnormal=%v), want 0", code, abnormal)
	}
}

func TestE2EGuardWrapShapes(t *testing.T) {
	cases := []struct {
		name string
		body string
		want int
	}{
		{"sub is not reported (the remaining-room idiom)", "f(a: u32, b: u32, c: u32): Bool = a - b < c", 0},
		{"mul on the right", "f(a: u32, b: u32, c: u32): Bool = c >= a * b", 1},
		{"both sides", "f(a: u32, b: u32, c: u32): Bool = a + b > c * a", 2},
		{"literal peer", "f(a: u32, n: u32): Bool = a + u32(1) < n", 1},
		{"literals only", "f(n: u32): Bool = u32(1) + u32(2) < n", 0},
		{"division", "f(a: u32, b: u32, c: u32): Bool = a / b < c", 0},
		{"equality", "f(a: u32, b: u32, c: u32): Bool = a + b == c", 0},
		{"signed", "f(a: i64, b: i64, c: i64): Bool = a + b <= c", 0},
		{"u64 platform uint", "f(a: uint, b: uint, c: uint): Bool = a + b <= c", 1},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			got := len(guardWrapReports(t, tc.body+"\n\nmain: (): i32 = 0\n"))
			if got != tc.want {
				t.Fatalf("%s: got %d reports, want %d", tc.body, got, tc.want)
			}
		})
	}
}
