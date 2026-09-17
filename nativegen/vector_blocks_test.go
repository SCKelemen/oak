package nativegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func vectorBlockText(t *testing.T, body string) (string, int) {
	return vectorAccessText(t, body, blockVectorLoads)
}

func vectorAccessText(t *testing.T, body string, rewrite func([]asm.Item) ([]asm.Item, int)) (string, int) {
	t.Helper()
	unit, errs := asm.ParseUnit("v.oakasm", "f: (v: []u32, i: u32) -> u32 = {\n  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10, x19, v8, v9, v16, v17\n"+body+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	items, n := rewrite(unit.Functions[0].Items)
	fn := *unit.Functions[0]
	fn.Items = items
	return Describe(&fn), n
}

func TestShareVectorAddressesPreservesAccessOrder(t *testing.T) {
	body := `
  add x10, x0, w2, uxtw #2
  ldr q16, [x10]
  add x9, x19, w2, uxtw #2
  str q16, [x9]
  add w10, w2, #4
  add x10, x0, w10, uxtw #2
  ldr q17, [x10]
  add w9, w2, #4
  add x9, x19, w9, uxtw #2
  str q17, [x9]
  mov w0, wzr
  ret`
	out, n := vectorAccessText(t, body, shareVectorAddresses)
	if n != 2 {
		t.Fatalf("want shared load and store addresses, got %d:\n%s", n, out)
	}
	var accesses []string
	for _, line := range strings.Split(out, "\n") {
		line = strings.TrimSpace(line)
		if strings.HasPrefix(line, "ldr q") || strings.HasPrefix(line, "str q") {
			accesses = append(accesses, line)
		}
	}
	want := "ldr q16, [x10]\nstr q16, [x9]\nldr q17, [x10, #16]\nstr q17, [x9, #16]"
	if strings.Join(accesses, "\n") != want || strings.Contains(out, "add w10") || strings.Contains(out, "add w9") {
		t.Fatalf("accesses must retain their order and values:\n%s", out)
	}
	// The old, earlier pass must not acquire store-rewriting authority.
	early, _ := vectorBlockText(t, body)
	if strings.Contains(early, "str q17, [x9, #16]") {
		t.Fatalf("early load-only pass rewrote a store:\n%s", early)
	}
}

func TestShareVectorAddressesAfterCleanup(t *testing.T) {
	body := `
  add x9, x0, w2, uxtw #2
  ldr q16, [x9]
  mov w10, w2
  add w10, w10, #4
  add x10, x0, w10, uxtw #2
  ldr q17, [x10]
  mov w0, wzr
  ret`
	if out, n := vectorAccessText(t, body, shareVectorAddresses); n != 0 {
		t.Fatalf("unresolved self-increment must not be shared: %d\n%s", n, out)
	}
	out, n := vectorAccessText(t, body, func(items []asm.Item) ([]asm.Item, int) {
		items, _ = cleanupItems(items)
		return shareVectorAddresses(items)
	})
	if n != 1 || !strings.Contains(out, "ldr q17, [x9, #16]") {
		t.Fatalf("cleanup must expose sharing: %d\n%s", n, out)
	}
}

func TestVectorAddressSharingRefusals(t *testing.T) {
	first := "add x9, x0, w2, uxtw #2\nldr q16, [x9]\n"
	second := "add w10, w2, #4\nadd x10, x0, w10, uxtw #2\nldr q17, [x10]\n"
	for _, test := range []struct{ name, body string }{
		{"consumed base", "add x0, x0, w2, uxtw #2\nldr q16, [x0]\n" + second},
		{"consumed index", "add x2, x0, w2, uxtw #2\nldr q16, [x2]\n" + second},
		{"stale root", "mov w10, w2\nadd w2, w2, #1\nadd x9, x0, w10, uxtw #2\nldr q16, [x9]\n" + second},
		{"temporary observation", first + "add w10, w2, #4\nstr w10, [x19]\nadd x10, x0, w10, uxtw #2\nldr q17, [x10]\n"},
		{"shared index", first + "add w10, w2, #4\nadd x11, x19, w10, uxtw #2\nldr q16, [x11]\nadd x10, x0, w10, uxtw #2\nldr q17, [x10]\n"},
		{"temporary overwrites base", first + "add w0, w2, #4\nadd x10, x0, w0, uxtw #2\nldr q17, [x10]\n"},
		{"kept address clobber", first + "mov w9, w3\n" + second},
		{"root clobber", first + "mov w2, w3\n" + second},
		{"store writeback", first + "str q16, [x0], #16\n" + second},
		{"load writeback", first + "ldr q16, [x0, #16]!\n" + second},
		{"zero root", "add x9, x0, wzr, uxtw #2\nldr q16, [x9]\nadd w10, wzr, #4\nadd x10, x0, w10, uxtw #2\nldr q17, [x10]\n"},
		{"live temporary", first + second + "str x10, [x19]\n"},
		{"label", first + "other:\n" + second},
		{"call", first + "bl helper\n" + second},
		{"atomic status", first + "stxr w9, x3, [x19]\n" + second},
		{"system barrier", first + "dmb ish\n" + second},
		{"unencodable offset", first + "add w10, w2, #16384\nadd x10, x0, w10, uxtw #2\nldr q17, [x10]\n"},
		{"overflowing offset", first + "add w10, w2, #4611686018427387908\nadd x10, x0, w10, uxtw #2\nldr q17, [x10]\n"},
	} {
		t.Run(test.name, func(t *testing.T) {
			for _, stores := range []bool{false, true} {
				out, n := vectorAccessText(t, test.body+"mov w0, wzr\nret", func(items []asm.Item) ([]asm.Item, int) {
					return blockVectorAccesses(items, stores)
				})
				if n != 0 {
					t.Fatalf("stores=%v: unsafe address sharing (%d):\n%s", stores, n, out)
				}
			}
		})
	}
}

func TestVectorAddressSharingUsesCurrentRootValue(t *testing.T) {
	body := `
  add w2, w2, #4
  add x9, x0, w2, uxtw #2
  ldr q16, [x9]
  add w10, w2, #8
  add x10, x0, w10, uxtw #2
  ldr q17, [x10]
  str w2, [x19]
  mov w0, wzr
  ret`
	out, n := vectorAccessText(t, body, shareVectorAddresses)
	if n != 1 || !strings.Contains(out, "ldr q17, [x9, #32]") || !strings.Contains(out, "add w2, w2, #4") {
		t.Fatalf("self-incremented root must denote its current value: %d\n%s", n, out)
	}
}

func TestVectorAddressUnknownInstructionIsBarrier(t *testing.T) {
	if !vectorAddressBarrier(asm.Instruction{Mnemonic: "unknown_instruction"}) {
		t.Fatal("an unknown instruction must not be assumed register-transparent")
	}
}

func TestVectorAddressSharingDistinguishesRegisterClasses(t *testing.T) {
	body := `
  add x9, x0, w2, uxtw #2
  ldr q16, [x9]
  add w10, w2, #4
  add v10.4s, v10.4s, v16.4s
  str q10, [x19]
  add x10, x0, w10, uxtw #2
  ldr q17, [x10]
  mov w0, wzr
  ret`
	out, n := vectorAccessText(t, body, shareVectorAddresses)
	if n != 1 || !strings.Contains(out, "ldr q17, [x9, #16]") || !strings.Contains(out, "add v10.4s, v10.4s, v16.4s") {
		t.Fatalf("vector use must neither prevent GPR sharing nor be removed: %d\n%s", n, out)
	}
}

func TestVectorBlockSharesFourAddresses(t *testing.T) {
	body := `
  mov w9, w2
  add x10, x0, w9, uxtw #2
  ldr q16, [x10]
  add v8.4s, v8.4s, v16.4s
  add w10, w2, #4
  add x9, x0, w10, uxtw #2
  ldr q17, [x9]
  add v9.4s, v9.4s, v17.4s
  add w9, w2, #8
  add x10, x0, w9, uxtw #2
  ldr q16, [x10]
  add v10.4s, v10.4s, v16.4s
  add w10, w2, #12
  add x9, x0, w10, uxtw #2
  ldr q17, [x9]
  add v11.4s, v11.4s, v17.4s
  mov w0, wzr
  ret`
	out, n := vectorAccessText(t, body, func(items []asm.Item) ([]asm.Item, int) {
		return blockVectorLoads(items)
	})
	if n != 3 || !strings.Contains(out, "ldr q17, [x10, #48]") {
		t.Fatalf("four loads must retain one address: %d\n%s", n, out)
	}
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
