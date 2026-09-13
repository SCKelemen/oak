package typechecker

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// The dispatch clause (docs/spec/93-simd.md section 6): a slot names a
// catalog feature once and a top-level function of the identical
// signature that is not itself dispatched.
func TestDispatchClauseChecks(t *testing.T) {
	check := func(src string) []string {
		p := parser.New(scanner.New(src))
		program := p.ParseProgram()
		if len(p.Errors()) != 0 {
			t.Fatalf("parse: %v", p.Errors())
		}
		tc := New(object.NewEnvironment())
		tc.CheckProgram(program)
		return tc.Errors()
	}
	good := `
count: (xs: []u8) -> u32 dispatch { sve: count_sve, rvv: count_rvv } = u32(len(xs))
count_sve: (xs: []u8) -> u32 = u32(len(xs))
count_rvv: (xs: []u8) -> u32 = u32(len(xs))
`
	if errs := check(good); len(errs) != 0 {
		t.Fatalf("a well-formed clause must check: %v", errs)
	}
	for _, bad := range []struct{ src, want string }{
		{"count: (xs: []u8) -> u32 dispatch { neon: count_x } = u32(len(xs))\ncount_x: (xs: []u8) -> u32 = u32(len(xs))\n", "unknown processor feature"},
		{"count: (xs: []u8) -> u32 dispatch { sve: count_x, sve: count_x } = u32(len(xs))\ncount_x: (xs: []u8) -> u32 = u32(len(xs))\n", "appears twice"},
		{"count: (xs: []u8) -> u32 dispatch { sve: count } = u32(len(xs))\n", "its own realization"},
		{"count: (xs: []u8) -> u32 dispatch { sve: missing } = u32(len(xs))\n", "not a top-level function"},
		{"count: (xs: []u8) -> u32 dispatch { sve: count_x } = u32(len(xs))\ncount_x: (xs: []u8) -> u64 = u64(len(xs))\n", "identical signature"},
		{"count: (xs: []u8) -> u32 dispatch { sve: count_x } = u32(len(xs))\ncount_x: (xs: []u8) -> u32 dispatch { rvv: count_y } = u32(len(xs))\ncount_y: (xs: []u8) -> u32 = u32(len(xs))\n", "itself dispatched"},
	} {
		errs := check(bad.src)
		found := false
		for _, e := range errs {
			if strings.Contains(e, bad.want) {
				found = true
			}
		}
		if !found {
			t.Errorf("expected an error containing %q, got %v", bad.want, errs)
		}
	}
}
