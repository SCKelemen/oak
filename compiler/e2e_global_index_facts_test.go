package compiler

// Extent facts over a global cursor and over a widened index
// (docs/spec/50-borrowing.md, "A cursor that is a global"): a guard on a
// top-level unsigned scalar proves the owned-array access it bounds, a
// call to a program function between the guard and the access kills the
// fact, and `u32(i)` over a bounded u16 keeps the bound. The wrapping
// offset spelling `c + 3 < 64` proves nothing about `c` and stays checked.

import (
	"strings"
	"testing"
)

const globalIndexFactsProgram = `buf: [64]u8
cur: u32
tbl: [24]u16

put_global: (v: u8): () {
  ok: Bool = cur < u32(64)
  ok ? { buf[cur] = v; cur = cur + u32(1) }
}

put4: (v: u32): () {
  ok: Bool = cur <= u32(60)
  ok ? {
    buf[cur] = u8_trunc_u32(v)
    buf[cur + u32(1)] = u8_trunc_u32(v >> u32(8))
    buf[cur + u32(2)] = u8_trunc_u32(v >> u32(16))
    buf[cur + u32(3)] = u8_trunc_u32(v >> u32(24))
    cur = cur + u32(4)
  }
}

bump: (): () { cur = u32(99) }

put_after_call: (v: u8): () {
  ok: Bool = cur < u32(64)
  ok ? { bump(); buf[cur] = v }
}

wrapping: (c: u32, v: u8): () {
  g: Bool = c + u32(3) < u32(64)
  g ? { buf[c] = v; buf[c + u32(3)] = v }
}

fill16: (): () {
  i: u16 = u16(0)
  while i < u16(24) {
    tbl[u32(i)] = i
    i = i + u16(1)
  }
}

main: (): i32 {
  put_global(u8(1))
  put4(u32(0x04030201))
  fill16()
  cur = u32(70)
  put_global(u8(9))
  i32_bits_u32(u32(buf[0]) + u32(buf[4]) * u32(10) + u32(tbl[23]) * u32(100) + cur)
}
`

func TestE2EGlobalIndexFacts(t *testing.T) {
	code, err := New().WithSource("gi.oak", globalIndexFactsProgram).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	checked := func(body string) int {
		return strings.Count(body, "oak_store(") + strings.Count(body, "oak_index(")
	}
	for _, name := range []string{"put_global", "put4", "fill16"} {
		body := cFunctionBody(t, string(code), "oak_"+name)
		if body == "" {
			t.Fatalf("no C body for %s", name)
		}
		if n := checked(body); n != 0 {
			t.Fatalf("%s: %d checked accesses remain:\n%s", name, n, body)
		}
	}
	if body := cFunctionBody(t, string(code), "oak_put_after_call"); checked(body) != 1 {
		t.Fatalf("put_after_call: the call must kill the fact:\n%s", body)
	}
	if body := cFunctionBody(t, string(code), "oak_wrapping"); checked(body) != 2 {
		t.Fatalf("wrapping: c + 3 < 64 proves nothing about a u32 that may wrap:\n%s", body)
	}
	// 1 + 4*10 + 23*100 + 70 = 2411, 107 modulo 256.
	if _, exit, abnormal := buildAndRunFrom(t, "global_index", New().WithSource("gi.oak", globalIndexFactsProgram)); abnormal || exit != 107 {
		t.Fatalf("program: exit %d abnormal=%v, want 107", exit, abnormal)
	}
}
