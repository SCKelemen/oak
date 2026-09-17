package asm

import (
	"fmt"
	"strings"
	"testing"
)

// A join intersects known bytes, not the stores' widths. Result-area
// copies use doublewords where a callee summary writes individual fields.
func TestMergeFrameBytesAcrossStoreWidths(t *testing.T) {
	for _, base := range []int64{-32, resultAreaBase} {
		for _, pieces := range [][]int64{{8}, {4, 4}, {2, 2, 2, 2}, {1, 1, 1, 1, 1, 1, 1, 1}} {
			for _, offset := range []int64{0, 1, 4, 8} {
				t.Run(fmt.Sprintf("base%d_pieces%v_offset%d", base, pieces, offset), func(t *testing.T) {
					a := &symbolicState{frame: map[int64]frameSlot{}}
					b := &symbolicState{frame: map[int64]frameSlot{}}
					a.storeSlot(base, paramTerm("a", 64), 8)
					at := base + offset
					for k, size := range pieces {
						b.storeSlot(at, paramTerm(fmt.Sprintf("b%d", k), int(size)*8), size)
						at += size
					}
					for _, reverse := range []bool{false, true} {
						left, right := a, b
						if reverse {
							left, right = b, a
						}
						merged, ok := (&pathExecutor{}).mergeTwo(paramTerm("cond", 1), left, right)
						if !ok {
							t.Fatal("valid frame layouts must merge")
						}
						for delta := int64(-1); delta <= 16; delta++ {
							addr := base + delta
							lv, lk := left.loadSlot(addr, 1)
							rv, rk := right.loadSlot(addr, 1)
							value, known := merged.loadSlot(addr, 1)
							if known != (lk && rk) {
								t.Fatalf("reverse=%v byte %d: known=%v, left=%v right=%v", reverse, delta, known, lk, rk)
							}
							if !known {
								continue
							}
							for cond := uint64(0); cond <= 1; cond++ {
								env := map[string]uint64{"cond": cond, "a": 0xFEDCBA9876543210}
								for k, size := range pieces {
									env[fmt.Sprintf("b%d", k)] = (0x0123456789ABCDEF + uint64(k)) & mask(int(size)*8)
								}
								want := rv.eval(env)
								if cond == 1 {
									want = lv.eval(env)
								}
								if got := value.eval(env); got != want {
									t.Fatalf("reverse=%v byte %d cond=%d: got %x, want %x", reverse, delta, cond, got, want)
								}
							}
						}
					}
					if len(a.frame) != 1 || len(b.frame) != len(pieces) {
						t.Fatal("merging changed an input frame")
					}
				})
			}
		}
	}
}

func TestMergeFrameKeepsGapsUnknown(t *testing.T) {
	a := &symbolicState{frame: map[int64]frameSlot{}}
	b := &symbolicState{frame: map[int64]frameSlot{}}
	a.storeSlot(-16, constTerm(0x0807060504030201, 64), 8)
	b.storeSlot(-16, constTerm(0x1211, 16), 2)
	b.storeSlot(-12, constTerm(0x18171615, 32), 4)
	merged, ok := (&pathExecutor{}).mergeTwo(paramTerm("cond", 1), a, b)
	if !ok {
		t.Fatal("gapped frames must merge")
	}
	for k := int64(0); k < 8; k++ {
		_, known := merged.loadSlot(-16+k, 1)
		if known != (k != 2 && k != 3) {
			t.Fatalf("byte %d: known=%v", k, known)
		}
	}
	if _, known := merged.loadSlot(-16, 8); known {
		t.Fatal("a wider load must not fill a gap with an old value")
	}
}

func TestLoopEndDoesNotRestoreLostFrameSlot(t *testing.T) {
	header := &symbolicState{frame: map[int64]frameSlot{-16: {value: paramTerm("loop1.slot", 64), width: 8}}}
	end := bodyEnd{state: &symbolicState{frame: map[int64]frameSlot{}}}
	if value := end.valueOfVar("s-16:8", header); value != nil {
		t.Fatalf("a lost slot cannot be treated as unchanged: %s", value)
	}
}

func TestMergeFrameRefusesInvalidLayouts(t *testing.T) {
	word := paramTerm("word", 64)
	for _, frame := range []map[int64]frameSlot{
		{-16: {value: word, width: 8}, -12: {value: word, width: 4}},
		{-16: {value: word, width: 0}},
		{-16: {value: word, width: 16}},
		{-16: {width: 8}},
		{int64(^uint64(0) >> 1): {value: word, width: 8}},
	} {
		for _, reverse := range []bool{false, true} {
			a, b := &symbolicState{frame: frame}, &symbolicState{frame: map[int64]frameSlot{}}
			if reverse {
				a, b = b, a
			}
			if _, ok := (&pathExecutor{}).mergeTwo(paramTerm("cond", 1), a, b); ok {
				t.Fatalf("reverse=%v: invalid frame merged: %v", reverse, frame)
			}
		}
	}
}

func TestVerifyLoopMixedFrameStoreWidths(t *testing.T) {
	decl := "count: (seed: u64, n: u32) -> u64"
	oak := `{
  lo: u32 = u32_trunc_u64(seed)
  hi: u32 = u32_trunc_u64(seed >> u64(32))
  i: u32 = u32(0)
  while i < n {
    lo = lo + u32(1)
    (i & u32(1)) != u32(0) ? { hi = hi + u32(2) } | { hi = hi + u32(3) }
    i = i + u32(1)
  }
  u64(lo) | (u64(hi) << u64(32))
}`
	body := `  bind x0 = seed
  bind w1 = n
  clobber w9, x10, x11, x12, x15
  frame 16
  sub sp, sp, #16
  str x0, [sp]
  add x15, sp, #0
  mov w9, #0
loop:
  cmp w9, w1
  b.hs done
  ldr w10, [sp]
  ldr w11, [sp, #4]
  add w10, w10, #1
  tst w9, #1
  b.eq narrow
  add w11, w11, #2
  lsl x12, x11, #32
  orr x12, x12, x10
  str x12, [x15]
  b join
narrow:
  add w11, w11, #3
  str w10, [sp]
  str w11, [sp, #4]
join:
  add w9, w9, #1
  b loop
done:
  ldr x0, [sp]
  add sp, sp, #16
  ret`
	if got := verifyCase(t, decl, oak, body); got.Kind != VerdictProven {
		t.Fatalf("mixed-width loop stores: %s: %s", got.Kind, got.Message)
	}
	wrong := strings.Replace(body, "str w11, [sp, #4]", "str w10, [sp, #4]", 1)
	if got := verifyCase(t, decl, oak, wrong); got.Kind != VerdictMismatch {
		t.Fatalf("wrong narrow arm: %s: %s", got.Kind, got.Message)
	}
}
