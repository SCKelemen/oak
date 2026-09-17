package asm

import (
	"fmt"
	"strings"
	"testing"
)

// The loop condition alone bounds the indexed store. The array must
// become loop-carried memory, including when initialized in wider slots;
// the neighboring tag must survive, and a zero-iteration loop writes nothing.
func TestVerifyLoopConditionFrameStore(t *testing.T) {
	decl := "fill: (n, tag: u32) -> u32"
	oak := `{
  tail: [16]u8 = [u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0)]
  i: u32 = u32(0)
  while i < n && i < u32(16) {
    tail[i] = u8(i + u32(1))
    i = i + u32(1)
  }
  u32(tail[3]) + tag
}`
	const tests = "  cmp w9, w0\n  b.hs done\n  cmp w9, #16\n  b.hs done\n"
	var bytes strings.Builder
	for k := 0; k < 16; k++ {
		fmt.Fprintf(&bytes, "  strb wzr, [sp, #%d]\n", k)
	}
	for initName, init := range map[string]string{"bytes": bytes.String(), "words": "  stp xzr, xzr, [sp]\n"} {
		top := "  bind w0 = n\n  bind w1 = tag\n  clobber w9, w10, x12\n  frame 32\n  sub sp, sp, #32\n" + init + `  str w1, [sp, #16]
  mov w9, #0
loop:
` + tests + `  add x12, sp, #0
  add w10, w9, #1
  strb w10, [x12, w9, uxtw]
  add w9, w9, #1
  b loop
done:
  ldrb w0, [sp, #3]
  ldr w10, [sp, #16]
  add w0, w0, w10
  add sp, sp, #32
  ret`
		rotated := strings.Replace(top, "loop:\n"+tests, tests+"loop:\n", 1)
		rotated = strings.Replace(rotated, "  b loop\n", "  cmp w9, w0\n  b.hs done\n  cmp w9, #16\n  b.lo loop\n", 1)
		for form, body := range map[string]string{"top": top, "rotated": rotated} {
			t.Run(initName+"/"+form, func(t *testing.T) {
				if v := verifyCase(t, decl, oak, body); v.Kind != VerdictProven {
					t.Fatalf("bounded loop store: %s: %s", v.Kind, v.Message)
				}
				wrongIndex := strings.Replace(body, "strb w10, [x12, w9, uxtw]", "strb w10, [x12]", 1)
				if v := verifyCase(t, decl, oak, wrongIndex); v.Kind != VerdictMismatch {
					t.Fatalf("wrong index: %s: %s", v.Kind, v.Message)
				}
				wrongTag := strings.Replace(body, "  ldr w10, [sp, #16]", "  mov w10, #0", 1)
				if v := verifyCase(t, decl, oak, wrongTag); v.Kind != VerdictMismatch {
					t.Fatalf("lost neighboring field: %s: %s", v.Kind, v.Message)
				}
			})
		}
	}
}

func TestLoopBodyBoundsStayPrivate(t *testing.T) {
	for _, setup := range []string{
		"cmp w9, #16\nb.hs done",
		"cmp w9, #16\nb.hs done\nmov w10, #0",
		"cmp w9, #16\nb.hs done\nb.lo internal",
	} {
		t.Run(setup, func(t *testing.T) {
			var items []Item
			for _, instr := range boundInstructions(t, setup) {
				items = append(items, instr)
			}
			x := &pathExecutor{items: items, labels: map[string]int{"done": len(items), "internal": 0}}
			shape := loopShape{testEnd: len(items), exitLabel: len(items)}
			entry := &symbolicState{regs: map[int]*term{9: zeroExtend(paramTerm("i", 32), 64)}, bounds: map[int]uint64{8: 4}}
			body := entry.clone()
			x.noteLoopBodyBounds(shape, body)
			bound, known := body.bounds[9]
			if known != (len(items) == 2) || known && bound != 16 {
				t.Fatalf("unsupported headers must not publish partial facts: (%d, %v)", bound, known)
			}
			if len(entry.bounds) != 1 || entry.bounds[8] != 4 || entry.flags != nil || body.flags != nil || len(body.regs) != 1 {
				t.Fatal("the replay changed entry facts, flags or registers")
			}
		})
	}
}
