package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// subslice and local spans through the native backend
// (docs/spec/94-assembler.md §9, ninth increment): `subslice(v, start, n)`
// is the C helper's check (`start > len || n > len - start` traps) followed
// by the derived pair {base + start·elem, n}; a local span or view holds
// its pair in callee-saved registers, so it survives calls and is walked,
// forwarded, and re-sliced like a parameter. The C backend's realization
// of the same program is the oracle.
const nativeSubsliceProgram = `
sum: (v: []u8) -> u32 {
  acc: u32 = u32(0)
  i: u32 = u32(0)
  while i < len(v) {
    acc = acc + u32(v[i])
    i = i + u32(1)
  }
  acc
}

// A tokenizer-like walk: fields separated by zero bytes, each field summed
// through a local view derived by subslice and handed to a leaf.
fields: (v: []u8) -> u32 {
  total: u32 = u32(0)
  start: u32 = u32(0)
  i: u32 = u32(0)
  while i < len(v) {
    v[i] == u8(0) ? {
      field: []u8 = subslice(v, start, i - start)
      total = total * u32(10) + sum(field)
      start = i + u32(1)
    } | { }
    i = i + u32(1)
  }
  tail: []u8 = subslice(v, start, len(v) - start)
  total * u32(10) + sum(tail)
}

// A span re-sliced twice and written through, then read back by the caller.
clear_middle: (s: [*]u16) -> () {
  inner: [*]u16 = subslice(s, u32(1), len(s) - u32(2))
  core: [*]u16 = subslice(inner, u32(1), len(inner) - u32(1))
  i: u32 = u32(0)
  while i < len(core) {
    core[i] = u16(0)
    i = i + u32(1)
  }
}

// An empty subslice at the end, and a local view copied from a parameter.
edge: (v: []u8) -> u32 {
  w: []u8 = v
  empty: []u8 = subslice(w, len(w), u32(0))
  u32(len(empty)) * u32(100) + sum(subslice(w, u32(1), u32(2)))
}

main: (): i32 {
  buf: [8]u8 = [u8(1), u8(2), u8(0), u8(3), u8(0), u8(4), u8(5), u8(6)]
  assert(fields(view(&buf)) == u32(345))
  s: [6]u16 = [u16(9), u16(9), u16(9), u16(9), u16(9), u16(9)]
  clear_middle(span(&s))
  assert(s[0] == u16(9))
  assert(s[1] == u16(9))
  assert(s[2] == u16(0))
  assert(s[4] == u16(0))
  assert(s[5] == u16(9))
  assert(edge(view(&buf)) == u32(2))
  42
}
`

// A subslice past the end traps in both realizations.
const nativeSubsliceOutOfRangeProgram = `
peek: (v: []u8, start: u32) -> u32 {
  w: []u8 = subslice(v, start, u32(2))
  u32(len(w))
}

main: (): i32 {
  buf: [3]u8
  peek(view(&buf), u32(2))
  0
}
`

func TestE2ENativeSubslice(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("subslice.oak", nativeSubsliceProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_subslice", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native subslice: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"sum", "fields", "clear_middle", "edge", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_subslice_c", New().WithSource("subslice.oak", nativeSubsliceProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_subslice_portable", New().WithSource("subslice.oak", nativeSubsliceProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	var trapInfos []string
	trapComp := New().WithSource("oob.oak", nativeSubsliceOutOfRangeProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			trapInfos = append(trapInfos, d.Message)
		}
	})
	_, _, nativeAbnormal := buildAndRunFrom(t, "native_subslice_oob", trapComp)
	if !strings.Contains(strings.Join(trapInfos, "\n"), "asm unit peek:") {
		t.Errorf("peek was not lowered by the native backend; diagnostics:\n%s", strings.Join(trapInfos, "\n"))
	}
	_, _, cAbnormal := buildAndRunFrom(t, "native_subslice_oob_c", New().WithSource("oob.oak", nativeSubsliceOutOfRangeProgram))
	if !nativeAbnormal || !cAbnormal {
		t.Fatalf("a subslice past the end must trap in both realizations (native abnormal=%v, C abnormal=%v)", nativeAbnormal, cAbnormal)
	}
}
