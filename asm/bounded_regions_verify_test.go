package asm

import "testing"

// Exercise owner and subslice lowering all the way through the verifier. A
// second name for an overlapping view must still observe the same memory.
func TestVerifyBoundedRegions(t *testing.T) {
	const decl = "regions: (i: u32, j: u32) -> u32"
	const arm = "  bind w0 = i\n  bind w1 = j\n  movz w0, #7\n  ret"
	const rv = "  bind a0 = i\n  bind a1 = j\n  li a0, 7\n  ret"
	cases := []struct {
		name, body string
		want       VerdictKind
	}{
		{"separate owners", `{
  a: [512]u32
  b: [512]u32
  a[i & u32(255)] = u32(7)
  b[j & u32(255)] = u32(9)
  a[i & u32(255)]
}`, VerdictProven},
		{"disjoint slices", `{
  a: [512]u32
  all: [*]u32 = span(&a)
  low: []u32 = subslice(all, u32(0), u32(256))
  high: []u32 = subslice(all, u32(256), u32(256))
  low[i & u32(255)] = u32(7)
  high[j & u32(255)] = u32(9)
  low[i & u32(255)]
}`, VerdictProven},
		{"overlapping slices", `{
  a: [512]u32
  all: [*]u32 = span(&a)
  low: []u32 = subslice(all, u32(0), u32(256))
  high: []u32 = subslice(all, u32(255), u32(256))
  low[u32(255)] = u32(7)
  high[u32(0)] = u32(9)
  low[u32(255)]
}`, VerdictMismatch},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			if v := verifyCase(t, decl, c.body, arm); v.Kind != c.want {
				t.Fatalf("arm64: got %s: %s", v.Kind, v.Message)
			}
			if v := rv64Verify(t, decl, c.body, rv); v.Kind != c.want {
				t.Fatalf("rv64: got %s: %s", v.Kind, v.Message)
			}
		})
	}
}
