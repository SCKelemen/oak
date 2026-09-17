package asm

import (
	"strings"
	"testing"
)

// The carried index and endpoint use the source's modular u32 addition.
// A wrapping base is not permission to omit or move a bounds trap.
func TestVerifyAffineIndexLoop(t *testing.T) {
	decl := "fill: (v: [*]u64, base: u32): ()"
	body := `{ i: u32 = 0
  while i < u32(2048) {
    v[base + i] = u64(0)
    i = i + u32(1)
  }
}`
	walk := `  bind x0, w1 = v
  bind w2 = base
  clobber w9, w10
  mov w9, w2
  add w10, w2, #2048
  cmp w9, w10
  b.eq done
loop:
  cmp w9, w1
  b.hs trap
  str xzr, [x0, w9, uxtw #3]
  add w9, w9, #1
  cmp w9, w10
  b.ne loop
done:
  ret
trap:
  brk #1`
	if v := verifyCase(t, decl, body, walk); v.Kind != VerdictProven {
		t.Fatalf("carried affine index: %s: %s", v.Kind, v.Message)
	}
	for name, changed := range map[string]string{
		"wrong endpoint": strings.Replace(walk, "#2048", "#2047", 1),
		"wrong stride":   strings.Replace(walk, "w9, w9, #1", "w9, w9, #2", 1),
		"wrong value":    strings.Replace(walk, "str xzr", "str x2", 1),
	} {
		t.Run(name, func(t *testing.T) {
			if v := verifyCase(t, decl, body, changed); v.Kind == VerdictProven {
				t.Fatalf("incorrect loop was proven: %s", v.Message)
			}
		})
	}
}
