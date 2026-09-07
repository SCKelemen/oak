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

// Non-constant global initializers fail closed in the C backend (OAK-T0501
// warns; the strict profile rejects; the generated C never runs a hidden
// global constructor).
func TestGlobalRuntimeInitializerFailsClosed(t *testing.T) {
	output, err := New().WithSource("g.oak", `
compute: (): i32 = 41

bad: i32 = compute()

main: (): i32 = bad
`).EmitC().Get()
	if err != nil {
		t.Fatalf("pipeline should warn, not error: %v", err)
	}
	if !containsStr(output, "OAK_GLOBAL_INITIALIZER_NOT_CONSTANT") {
		t.Fatalf("non-constant global must fail closed in C:\n%s", output)
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
