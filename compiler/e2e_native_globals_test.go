package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Package-global scratch through the native backend (the OS pilot's N3:
// `st`, `walk_null`, `trans_pa`). A mutable top-level scalar is addressed
// storage: `adrp`/`add :lo12:` name its cell, the checker admits one
// access at its width, the C emitter gives it external linkage under the
// label the companion object references. Readers are proven against the
// Oak body (the cell's entry value is a parameter of the proof), and
// writers are proven cell by cell: the value each side leaves in a cell
// must agree, a cell one side never writes keeping its entry value. The functions lower natively
// and agree with the C backend.
const nativeGlobalsProgram = `
st: u32 = u32(0)
walk_null: Bool = false
trans_pa: u64 = u64(0)
level: u8 = u8(0)

set_state: (s: u32, pa: u64): () {
  st = s
  trans_pa = pa + u64(st)
  level = u8_trunc_u32(s)
  walk_null = s == u32(0)
}

// A pure reader: proven equal to its Oak body over the cells' values.
sum_state: (): u64 {
  trans_pa + u64(st) + u64(level)
}

read_state: (): u64 {
  walk_null ? { u64(1000) } | { sum_state() }
}

bump: (): u32 {
  st = st + u32(1)
  st
}

main: (): i32 {
  set_state(u32(7), u64(100))
  a: u64 = read_state()   // 107 + 7 + 7 = 121
  b: u32 = bump()         // 8
  set_state(u32(0), u64(5))
  c: u64 = read_state()   // walk_null: 1000
  // 121 + 8 + 1000 = 1129; the exit code carries the low byte, 105.
  i32_bits_u32(u32_trunc_u64(a) + b + u32_trunc_u64(c))
}
`

func TestE2ENativeGlobals(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("globals.oak", nativeGlobalsProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_globals", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 1129%256 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want %d\n%s", code, abnormal, 1129%256, joined)
	}
	for _, fn := range []string{"set_state", "sum_state", "read_state", "bump"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s must lower natively over package globals; diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "asm unit sum_state: proven") {
		t.Errorf("a pure reader of globals must be proven against its Oak body; diagnostics:\n%s", joined)
	}
	// Writers are proven in the cells they write, not trusted: the unit
	// writer in every cell, the writer with a result in both.
	if !strings.Contains(joined, "asm unit set_state: proven equal to its Oak body in the package state it writes (level, st, trans_pa, walk_null)") {
		t.Errorf("set_state must be proven in the cells it writes; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit bump: proven") || !strings.Contains(joined, "package state it writes (st)") {
		t.Errorf("bump must be proven in its result and the cell it writes; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_globals_c", New().WithSource("globals.oak", nativeGlobalsProgram)); abnormal || code != 1129%256 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want %d", code, abnormal, 1129%256)
	}
}
