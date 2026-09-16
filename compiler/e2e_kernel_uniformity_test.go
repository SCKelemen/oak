package compiler

import (
	"strings"
	"testing"
)

// F32: a group-wide output may be written by lane 0 only when doing so
// preserves which lanes reach the store and the value they would write.
// These programs used to compile for the host and silently lose stores
// in Metal. Check the ordinary C build too: rejection is a language rule.
func TestKernelGroupStoreUniformityRejections(t *testing.T) {
	cases := map[string]string{
		"nonzero lane": `
  lane(4) == 1 && gid < len(out) ? { out[gid] = 7 }
`,
		"guard alias": `
  selected: Bool = lane(4) == 1
  selected && gid < len(out) ? { out[gid] = 7 }
`,
		"nested guard": `
  lane(4) != 0 ? {
    gid < len(out) ? { out[gid] = 7 }
  }
`,
		"else arm": `
  lane(4) == 0 ? {} | {
    gid < len(out) ? { out[gid] = 7 }
  }
`,
		"disjunction does not select lane zero": `
  lane(4) == 0 || gid < len(out) ? { out[gid] = 7 }
`,
		"reassigned guard": `
  selected: Bool = false
  selected = lane(4) == 1
  selected && gid < len(out) ? { out[gid] = 7 }
`,
		"control dependent guard": `
  selected: Bool = false
  lane(4) == 1 ? { selected = true }
  selected && gid < len(out) ? { out[gid] = 7 }
`,
		"lane dependent value": `
  value: u32 = lane(4)
  gid < len(out) ? { out[gid] = value }
`,
		"control dependent value": `
  value: u32 = 0
  lane(4) == 1 ? { value = 7 }
  gid < len(out) ? { out[gid] = value }
`,
		"loop carried guard": `
  a: u32 = 0
  b: u32 = 0
  i: u32 = 0
  while i < 4 {
    a = b
    a != 0 && gid < len(out) ? { out[gid] = 7 }
    b = lane(4)
    i = i + 1
  }
`,
		"divergent break": `
  i: u32 = 0
  while i < 4 {
    lane(4) == 0 ? { break }
    gid < len(out) ? { out[gid] = 7 }
    i = i + 1
  }
`,
		"lane dependent loop bound": `
  n: u32 = lane(4)
  i: u32 = 0
  while i < n {
    gid < len(out) ? { out[gid] = 7 }
    i = i + 1
  }
`,
		"array guard": `
  selected: [1]u32
  selected[0] = lane(4)
  selected[0] != 0 && gid < len(out) ? { out[gid] = 7 }
`,
		"record guard": `
  selected: Selection = Selection { value: lane(4) }
  selected.value != 0 && gid < len(out) ? { out[gid] = 7 }
`,
		"helper state isolation": `
  value: u32 = lane(4)
  next: u32 = helper(value)
  value != 0 && gid < len(out) ? { out[gid] = next }
`,
		"mutable output value": `
  unused: u32 = lane(4)
  gid < len(out) ? { out[gid] = out[gid] + 1 }
`,
	}
	for name, body := range cases {
		t.Run(name, func(t *testing.T) {
			src := `
Selection: type = struct { value: u32 }
helper: (value: u32): u32 = {
  gid: u32 = value + 1
  gid
}
kernel k: (gid: u32, out: [*]u32): () = {
` + body + `
}
main: (): i32 = 0
`
			_, err := New().WithSource("lane_store.oak", src).EmitC().Get()
			if err == nil || !strings.Contains(err.Error(), CodeKernelSubset) || !strings.Contains(err.Error(), "lane-independent store") {
				t.Fatalf("want a lane-independent store diagnostic (%s), got %v", CodeKernelSubset, err)
			}
		})
	}
}

const kernelUniformStoresProgram = `
helper: (x: u32): u32 = x + 7
kernel uniform: (gid: u32, out: [*]u32): () = {
  unused: u32 = lane(4)
  gid < len(out) ? { out[gid] = helper(gid) }
}
kernel selected: (gid: u32, out: [*]u32): () = {
  value: u32 = lane(4) + 3
  lane(4) == 0 && gid < len(out) ? { out[gid] = value }
}
kernel reversed: (gid: u32, out: [*]u32): () = {
  value: u32 = lane(4) + 5
  gid < len(out) ? {
    0 == lane(4) ? { out[gid] = value }
  }
}
kernel otherwise: (gid: u32, out: [*]u32): () = {
  value: u32 = lane(4) + 9
  lane(4) != 0 ? {} | {
    gid < len(out) ? { out[gid] = value }
  }
}
main: (): i32 = {
  a: [1]u32
  b: [1]u32
  c: [1]u32
  d: [1]u32
  uniform(0, span(&a))
  selected(0, span(&b))
  reversed(0, span(&c))
  otherwise(0, span(&d))
  a[0] == 7 && b[0] == 3 && c[0] == 5 && d[0] == 9 ? 42 | 1
}
`

func TestE2EKernelUniformStores(t *testing.T) {
	code, abnormal := buildAndRun(t, "uniform_stores", kernelUniformStoresProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if got := interpretChecked(t, kernelUniformStoresProgram); got != 42 {
		t.Fatalf("interpreted: %d", got)
	}
	if _, err := New().WithSource("uniform_stores.oak", kernelUniformStoresProgram).EmitMetal().Get(); err != nil {
		t.Fatal(err)
	}
}
