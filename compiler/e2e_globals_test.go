package compiler

import "testing"

// Static globals (docs/spec/60-effects-allocation.md): top-level bindings
// are file-scope statics with constant initializers — kernel state. Read
// and written across functions; owned-array globals borrow like any owner.
func TestE2EStaticGlobals(t *testing.T) {
	code, abnormal := buildAndRun(t, "globals", `
Point: type = struct {
  x: i32
  y: i32
}

counter: i32 = 8
origin: Point = Point { x: 3, y: 4 }
pool: [4]u8

bump: (): i32 {
  counter = counter + 1
  counter
}

fill_pool: (): i32 {
  s: [*]u8 = span(&pool)
  i: u32 = 0
  while i < len(s) {
    s[i] = u8(5)
    i = i + 1
  }
  i32(s[0]) + i32(s[3])
}

main: (): i32 {
  bump()
  bump()
  counter + origin.x + origin.y + fill_pool() + 15
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42 (10 + 3 + 4 + 10 + 15)", code, abnormal)
	}
}

// Non-constant global initializers fail closed at C emission as an Oak
// error naming the global (OAK-T0501; ml finding F19 found the earlier
// C-compiler failure). Check-only pipelines still warn, so scripts may
// interpret them; the strict profile rejects them; the generated C never
// runs a hidden global constructor.
func TestGlobalRuntimeInitializerFailsClosed(t *testing.T) {
	src := `
compute: (): i32 = 41

bad: i32 = compute()

main: (): i32 = bad
`
	_, err := New().WithSource("g.oak", src).EmitC().Get()
	if err == nil {
		t.Fatalf("non-constant global must fail C emission")
	}
	if !containsStr(err.Error(), "OAK-T0501") || !containsStr(err.Error(), "global bad") || !containsStr(err.Error(), "4:1") {
		t.Fatalf("emission error should name OAK-T0501, the global, and its position: %v", err)
	}
	if _, err := New().WithSource("g.oak", src).Check().Get(); err != nil {
		t.Fatalf("check should warn, not error: %v", err)
	}
}

func containsStr(haystack, needle string) bool {
	return len(haystack) >= len(needle) && (func() bool {
		for i := 0; i+len(needle) <= len(haystack); i++ {
			if haystack[i:i+len(needle)] == needle {
				return true
			}
		}
		return false
	})()
}
