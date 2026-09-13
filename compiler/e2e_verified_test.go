package compiler

import (
	"strings"
	"testing"
)

// The verified build (docs/spec/94-assembler.md §9, the verified gate):
// every function must be lowered natively and proven, and a proven caller
// stands only on accepted callees. The program mixes proven functions, a
// proven caller resting on a proven callee, a body outside the verifier's
// subset (a division by a variable), and a caller whose summary fails in
// that body: the report accepts four and rejects three with the reasons
// counted. The closure over callees is TestAcceptedClosure.
const verifiedProgram = `
inc: (x: u32) -> u32 = x + u32(1)

// A counted loop keeps the call as a call (the helper inliner leaves loops);
// proven, resting on inc.
twice_inc: (x: u32) -> u32 {
  r: u32 = x
  i: u32 = u32(0)
  while i < u32(2) {
    r = inc(r)
    i = i + u32(1)
  }
  r
}

// Division by a non-constant stays outside the verifier's subset on both
// sides: trusted, and a caller's summary fails inside its body too.
ratio: (a: u32, b: u32) -> u32 = b == u32(0) ? u32(0) | a / b

scaled: (a: u32, b: u32) -> u32 {
  r: u32 = u32(0)
  i: u32 = u32(0)
  while i < u32(2) {
    r = r + ratio(a, b)
    i = i + u32(1)
  }
  r
}

// A byte store to an owned array, proven; sum_low is proven resting on it.
low_byte: (x: u32) -> u32 {
  buf: [4]u8
  buf[0] = u8_trunc_u32(x)
  u32(buf[0])
}

sum_low: (x: u32) -> u32 {
  r: u32 = u32(0)
  i: u32 = u32(0)
  while i < u32(2) {
    r = r + low_byte(x)
    i = i + u32(1)
  }
  r
}

main: (): i32 {
  assert(twice_inc(u32(3)) == u32(5))
  assert(scaled(u32(8), u32(2)) == u32(8))
  assert(sum_low(u32(0x1FF)) == u32(510))
  0
}
`

func TestE2EVerifiedGate(t *testing.T) {
	requireArm64Host(t)
	report, err := New().WithSource("verified.oak", verifiedProgram).Verified().Get()
	if err != nil {
		t.Fatal(err)
	}
	text := report.String()
	accepted := " " + strings.Join(report.Accepted, " ") + " "
	for _, name := range []string{"inc", "twice_inc", "low_byte", "sum_low"} {
		if !strings.Contains(accepted, " "+name+" ") {
			t.Errorf("%s must be accepted; report:\n%s", name, text)
		}
	}
	rejected := map[string]string{}
	for _, outcome := range report.Rejected {
		rejected[outcome.Name] = outcome.Reason
	}
	if reason, ok := rejected["ratio"]; !ok || !strings.HasPrefix(reason, "trusted: ") {
		t.Errorf("ratio must be rejected as trusted; report:\n%s", text)
	}
	if reason, ok := rejected["scaled"]; !ok || !strings.Contains(reason, "a call to ratio whose body contains") {
		t.Errorf("scaled must be rejected (its summary fails in ratio's body); report:\n%s", text)
	}
	if _, ok := rejected["main"]; !ok {
		t.Errorf("main (asserts, no integer result) must be rejected; report:\n%s", text)
	}
	if report.Total != 7 || len(report.Accepted) != 4 || len(report.Rejected) != 3 {
		t.Errorf("counts: total %d accepted %d rejected %d; report:\n%s", report.Total, len(report.Accepted), len(report.Rejected), text)
	}
	if !strings.Contains(text, "what stands between the program and a proof:") || !strings.Contains(text, "verified: 7 functions: 4 accepted, 3 rejected") || !strings.Contains(text, "a call to F whose body") {
		t.Errorf("report text:\n%s", text)
	}
	// The gate stands on the same lowering as the build: the program runs.
	if _, code, abnormal := buildAndRunFrom(t, "verified_gate", New().WithSource("verified.oak", verifiedProgram).WithNativeBodies().WithNativeAsm()); abnormal || code != 0 {
		t.Fatalf("exit = (%d, abnormal=%v), want 0", code, abnormal)
	}
}
