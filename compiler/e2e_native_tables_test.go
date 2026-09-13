package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// Constant tables (docs/spec/94-assembler.md §9): a top-level array of
// fixed-width integers with a literal initializer that nothing writes lives
// in the object's read-only data, and a native body reads it through the
// symbol's address — an element by a guarded index, or the whole table as
// a view. Every function lowers natively on both lanes, the program agrees
// with the C build, and a natively linked executable carries the bytes.
const nativeTablesProgram = `TABLE: [8]u8 = [8]u8{3, 1, 4, 1, 5, 9, 2, 6}
WORDS: [4]u32 = [4]u32{100, 200, 300, 400}
SIGNED: [3]i16 = [3]i16{-1, -2, 30}

digit_at: (i: u32) -> u8 = TABLE[i]

sum_view: (v: []u8) -> u32 {
  total: u32 = u32(0)
  i: u32 = u32(0)
  while i < len(v) {
    total = total + u32(v[i])
    i = i + u32(1)
  }
  total
}

table_sum: () -> u32 = sum_view(view(&TABLE))

word: (i: u32) -> u32 = WORDS[i]

third: () -> i16 = SIGNED[2]

main: (): i32 {
  // 3 + 4 + 31 + 300 - 338 = 0, and the signed table's third entry is 30.
  n: u32 = u32(digit_at(u32(0))) + u32(digit_at(u32(2))) + table_sum() + word(u32(2)) - u32(338)
  i32(third()) - i32(30) + i32_bits_u32(n)
}
`

func TestE2ENativeConstantTables(t *testing.T) {
	for _, tname := range []string{"freestanding/arm64", "linux/riscv64"} {
		tgt, err := target.Parse(tname)
		if err != nil {
			t.Fatal(err)
		}
		var native []string
		sink := func(d *diagnostic.Diagnostic) {
			if strings.HasPrefix(d.Message, "native backend: ") {
				native = append(native, d.Message)
			}
		}
		comp := New().WithSource("tables.oak", nativeTablesProgram).WithTarget(tgt).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(sink)
		if _, err := comp.EmitC().Get(); err != nil {
			t.Fatalf("%s: native build: %v", tname, err)
		}
		for _, fn := range []string{"digit_at", "sum_view", "table_sum", "word", "third"} {
			for _, m := range native {
				if strings.Contains(m, "native backend: "+fn+" left to the C backend") {
					t.Errorf("%s: %s", tname, m)
				}
			}
			found := false
			for _, m := range native {
				if strings.Contains(m, "asm unit "+fn+":") || strings.Contains(m, "asm unit "+fn+" ") {
					found = true
				}
			}
			if !found {
				t.Errorf("%s: %s: no native verdict:\n%s", tname, fn, strings.Join(native, "\n"))
			}
		}
	}
	if _, exit, abnormal := buildAndRunFrom(t, "native_tables", New().WithSource("tables.oak", nativeTablesProgram)); abnormal || exit != 0 {
		t.Fatalf("program: exit = (%d, abnormal=%v), want 0", exit, abnormal)
	}
}

// The natively linked executable carries the tables in its read-only data
// and runs to the same exit under QEMU.
func TestE2ENativeConstantTablesExecutable(t *testing.T) {
	skipInShort(t)
	for _, arch := range []string{target.ArchRiscv64, target.ArchArm64} {
		tgt := target.Target{OS: target.OSFreestanding, Arch: arch}
		t.Run(tgt.String(), func(t *testing.T) {
			image, err := New().WithSource("tables.oak", nativeTablesProgram).WithTarget(tgt).EmitExecutable().Get()
			if err != nil {
				t.Fatalf("link: %v", err)
			}
			if !strings.Contains(string(image), "oak_data_TABLE") {
				t.Fatalf("the executable names no data symbol for TABLE")
			}
			if code := runImage(t, tgt, image); code != 0 {
				t.Fatalf("the executable exited %d, want 0", code)
			}
		})
	}
}
