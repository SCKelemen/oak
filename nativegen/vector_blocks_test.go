package nativegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func vectorBlockText(t *testing.T, body string) (string, int) {
	t.Helper()
	unit, errs := asm.ParseUnit("v.oakasm", "f: (v: []u32, i: u32) -> u32 = {\n  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10, x19, v8, v9, v16, v17\n"+body+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	items, n := blockVectorLoads(unit.Functions[0].Items)
	fn := *unit.Functions[0]
	fn.Items = items
	return Describe(&fn), n
}

// Vector block loads (nativegen/vector_blocks.go): the vector loads of one
// basic block read off the first load's element address at immediate
// offsets, and the address and index instructions the later loads owned
// are dropped. A load whose index is not the same root, whose offset is
// not a multiple of sixteen, or whose address outlives the load keeps its
// own address.
func TestVectorBlockLoads(t *testing.T) {
	// Two loads four u32 elements apart: the second reads [x9, #16].
	out, n := vectorBlockText(t, "  add x9, x0, w2, uxtw #2\n  ldr q16, [x9]\n  add v8.4s, v8.4s, v16.4s\n  add w10, w2, #4\n  add x10, x0, w10, uxtw #2\n  ldr q17, [x10]\n  add v9.4s, v9.4s, v17.4s\n  mov w0, wzr\n  ret")
	if n != 1 || !strings.Contains(out, "ldr q17, [x9, #16]") || strings.Contains(out, "add x10, x0, w10") || strings.Contains(out, "add w10, w2, #4") {
		t.Fatalf("the second load must read the first's address at #16 (%d fused):\n%s", n, out)
	}
	// The index reached through a copy is the same root.
	out, n = vectorBlockText(t, "  mov w9, w2\n  add x9, x0, w9, uxtw #2\n  ldr q16, [x9]\n  add v8.4s, v8.4s, v16.4s\n  add w10, w2, #4\n  add x10, x0, w10, uxtw #2\n  ldr q17, [x10]\n  add v9.4s, v9.4s, v17.4s\n  mov w0, wzr\n  ret")
	if n != 1 || !strings.Contains(out, "ldr q17, [x9, #16]") {
		t.Fatalf("an index through a copy must resolve to its root (%d fused):\n%s", n, out)
	}
	// A different base is not the same block.
	out, n = vectorBlockText(t, "  add x9, x0, w2, uxtw #2\n  ldr q16, [x9]\n  add w10, w2, #4\n  add x10, x19, w10, uxtw #2\n  ldr q17, [x10]\n  mov w0, wzr\n  ret")
	if n != 0 {
		t.Fatalf("a load off another base must keep its address (%d fused):\n%s", n, out)
	}
	// An offset that is not a multiple of sixteen has no immediate form.
	out, n = vectorBlockText(t, "  add x9, x0, w2, uxtw #2\n  ldr q16, [x9]\n  add w10, w2, #1\n  add x10, x0, w10, uxtw #2\n  ldr q17, [x10]\n  mov w0, wzr\n  ret")
	if n != 0 {
		t.Fatalf("a four-byte offset has no q immediate form (%d fused):\n%s", n, out)
	}
	// The address the second load formed is read after it: it stays.
	out, n = vectorBlockText(t, "  add x9, x0, w2, uxtw #2\n  ldr q16, [x9]\n  add w10, w2, #4\n  add x10, x0, w10, uxtw #2\n  ldr q17, [x10]\n  ldr q16, [x10, #16]\n  mov w0, wzr\n  ret")
	if strings.Contains(out, "add x10") == false {
		t.Fatalf("an address read again must stay (%d fused):\n%s", n, out)
	}
	// A write of the base between the loads stops the fusion.
	out, n = vectorBlockText(t, "  add x9, x0, w2, uxtw #2\n  ldr q16, [x9]\n  mov x0, x19\n  add w10, w2, #4\n  add x10, x0, w10, uxtw #2\n  ldr q17, [x10]\n  mov w0, wzr\n  ret")
	if n != 0 {
		t.Fatalf("a write of the base must stop the fusion (%d fused):\n%s", n, out)
	}
}
