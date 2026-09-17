package nativegen

import "testing"

func TestAnalyzeLoopRewriteEligibilityUsesExactMatchersWithoutMutation(t *testing.T) {
	const source = `
sum: (v: []u32): u32 {
  acc: u32 = 0
  i: u32 = 0
  while i < len(v) {
    acc = acc + v[i]
    i = i + u32(1)
  }
  acc
}
map: (dst: [*]u32, src: []u32): () {
  len(dst) == len(src) ? {
    i: u32 = 0
    while i < len(src) {
      dst[i] = src[i] + u32(1)
      i = i + u32(1)
    }
  } | { }
}
dot: (a: []f32, b: []f32): f32 {
  total: f32 = 0.0
  len(a) == len(b) ? {
    i: u32 = 0
    while i < len(a) {
      total = total + a[i] * b[i]
      i = i + u32(1)
    }
  }
  total
}
rounds: (x: u32): u32 {
  i: u32 = 0
  while i < u32(3) {
    x = x + i
    i = i + u32(1)
  }
  x
}
plain: (x: u32): u32 = x + u32(1)
`
	_, functions, _, tc := checkedFillFunction(t, source, "sum")
	cases := []struct {
		name string
		want LoopRewriteEligibility
	}{
		{"sum", LoopRewriteEligibility{Reduction: true, VectorReduction: true}},
		{"map", LoopRewriteEligibility{VectorMap: true}},
		{"dot", LoopRewriteEligibility{VectorFold: true}},
		{"rounds", LoopRewriteEligibility{Constant: true}},
		{"plain", LoopRewriteEligibility{}},
	}
	for _, test := range cases {
		fn := functions[test.name]
		before := fn.Body.String()
		if got := AnalyzeLoopRewriteEligibility(fn, functions, tc); got != test.want {
			t.Errorf("%s eligibility = %+v, want %+v", test.name, got, test.want)
		}
		if after := fn.Body.String(); after != before {
			t.Fatalf("%s eligibility scan mutated checked source:\nbefore: %s\nafter: %s", test.name, before, after)
		}
	}
}

func TestAnalyzeLoopRewriteEligibilityIncludesNativeHelperExpansion(t *testing.T) {
	const source = `
reduce: (seed: simd.U32x4, values: []u32): simd.U32x4 {
  total: u32 = 0
  i: u32 = 0
  while i < len(values) {
    total = total + values[i]
    i = i + u32(1)
  }
  seed
}
caller: (seed: simd.U32x4, values: []u32): simd.U32x4 {
  reduce(seed, values)
}
`
	caller, functions, _, tc := checkedFillFunction(t, source, "caller")
	before := caller.Body.String()
	want := LoopRewriteEligibility{Reduction: true, VectorReduction: true}
	if got := AnalyzeLoopRewriteEligibility(caller, functions, tc); got != want {
		t.Fatalf("expanded helper eligibility = %+v, want %+v", got, want)
	}
	if after := caller.Body.String(); after != before {
		t.Fatalf("helper eligibility scan mutated checked caller:\nbefore: %s\nafter: %s", before, after)
	}
}
