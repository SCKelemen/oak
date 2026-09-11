package lean

import (
	"strings"
	"testing"
)

// A span rebound only through a call — inside a while body, an if arm, a
// variant-match arm, and a call inside an if inside a while — is a write
// of that loop or conditional, so the helper returns it and the caller
// rebinds it (oak #186: the heap sort's heapify loop lost its array).
func TestExtractionWriteSetThroughCalls(t *testing.T) {
	src := `
Step: type = Twice | Once
bump: (items: [*]u32, at: u32): u32 {
  items[at] = items[at] + u32(1)
  items[at]
}
loop_call: (items: [*]u32, n: u32): u32 {
  i: u32 = 0
  while i < n {
    r: u32 = bump(items, i)
    i = i + u32(1)
  }
  i
}
arm_call: (items: [*]u32, flag: Bool): u32 {
  flag ? { r: u32 = bump(items, u32(0)) } | { s: u32 = bump(items, u32(1)) }
  items[0]
}
match_call: (items: [*]u32, step: Step): u32 {
  step ? | .Twice => { a: u32 = bump(items, u32(0))
                        b: u32 = bump(items, u32(0)) }
         | .Once => { c: u32 = bump(items, u32(0)) }
  items[0]
}
nested_call: (items: [*]u32, n: u32): u32 {
  i: u32 = 0
  while i < n {
    i < u32(2) ? { r: u32 = bump(items, i) }
    i = i + u32(1)
  }
  items[0]
}
`
	out, err := extract(t, src)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"def loop_call.loop1 (items : Array UInt32) (n : UInt32) (i : UInt32) : Nat → Option (Array UInt32 × UInt32)",
		"let (items, i) ← loop_call.loop1 items n i fuel",
		"def nested_call.loop1 (items : Array UInt32) (n : UInt32) (i : UInt32) : Nat → Option (Array UInt32 × UInt32)",
		"let (items, i) ← nested_call.loop1 items n i fuel",
	} {
		if !strings.Contains(out, want) {
			t.Fatalf("write set lacks %q in:\n%s", want, out)
		}
	}
	// The if arm and the match arm rebind the span from the chosen arm.
	for _, want := range []string{"items ← (if flag then (do", "items ← (match step with"} {
		if !strings.Contains(out, want) && !strings.Contains(out, "("+want) {
			t.Fatalf("arm write set lacks %q in:\n%s", want, out)
		}
	}
}

// A writable span declared as a window of another array aliases it in Oak;
// the extraction writes the window back into its owner after every
// statement that rebinds it, and the owner joins the write set of the
// enclosing arm or loop (oak #186: pdqsort sorted `items[a:b]` windows
// that never reached `items`).
func TestExtractionSpanWindowsWriteBack(t *testing.T) {
	src := `
bump: (items: [*]u32, at: u32): u32 {
  items[at] = items[at] + u32(1)
  items[at]
}
window_arm: (items: [*]u32): u32 {
  true ? { short: [*]u32 = items[1:3]
    short[0] = u32(9)
    r: u32 = bump(short, u32(1)) }
  items[1]
}
window_loop: (items: [*]u32, n: u32): u32 {
  i: u32 = 0
  while i < n {
    true ? { tail: [*]u32 = items[i:n]
      r: u32 = bump(tail, u32(0)) }
    i = i + u32(1)
  }
  items[0]
}
whole_alias: (n: u32): u32 {
  buf: [4]u32
  s: [*]u32 = span(&buf)
  s[0] = n
  buf[0]
}
`
	out, err := extract(t, src)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"let short : Array UInt32 := (items.extract 1 3)",
		"let short_lo : Nat := 1",
		"let items := ((items.extract 0 short_lo) ++ short ++ (items.extract (short_lo + short.size) items.size))",
		"def window_loop.loop1 (items : Array UInt32) (n : UInt32) (i : UInt32) : Nat → Option (Array UInt32 × UInt32)",
		"let s : Array UInt32 := buf",
		"let buf := s",
	} {
		if !strings.Contains(out, want) {
			t.Fatalf("window write-back lacks %q in:\n%s", want, out)
		}
	}
	if !strings.Contains(out, "items ← (if") && !strings.Contains(out, "(items) ← (if") {
		t.Fatalf("arm write set lacks the window's owner in:\n%s", out)
	}
}
