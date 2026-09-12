package compiler

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// Buffer custody states (docs/spec/92-ffi.md section 2.8.5): Buffer[T] is
// Buffer[T, Host]; an extern binding that takes a Buffer[T, From] and
// returns a Buffer[T, To] is a custody transition — the buffer crosses as
// pointer and count, the old binding is consumed, the result is the same
// buffer under its new state — and only a Host buffer can be borrowed or
// handed back.

const custodyHelperC = `
#include <stddef.h>
#include <stdint.h>
static float *submitted = 0;
static size_t submitted_len = 0;
void mlrt_submit(float *base, size_t len) { submitted = base; submitted_len = len; }
void mlrt_complete(float *base, size_t len) {
  /* The device "computed" while the buffer was in its custody. */
  if (base == submitted && len == submitted_len) {
    for (size_t i = 0; i < len; i++) base[i] = base[i] * 2.0f;
  }
}
`

const custodyProgram = `
malloc: (n: c.Size): c.Ptr = c.extern("malloc")
free: (p: c.Ptr): () = c.extern("free")
submit: (b: Buffer[f32, Host]): Buffer[f32, Device] = c.extern("mlrt_submit")
complete: (b: Buffer[f32, Device]): Buffer[f32, Host] = c.extern("mlrt_complete")

fill: (s: [*]f32): () {
  i: u32 = 0
  while i < len(s) {
    s[i] = f32_round_u32(i) + 1.0
    i = i + u32(1)
  }
}

total: (v: []f32): f32 {
  acc: f32 = 0.0
  i: u32 = 0
  while i < len(v) {
    acc = acc + v[i]
    i = i + u32(1)
  }
  acc
}

run: (): f32 {
  p: c.Ptr = malloc(c.Size(u32(16)))
  result: f32 = 0.0
  unsafe {
    host: Buffer[f32] = c.own[f32](p, u32(4))
    fill(span(&host))
    device: Buffer[f32, Device] = submit(host)
    back: Buffer[f32] = complete(device)
    result = total(view(&back))
    free(c.disown(back))
  }
  result
}

main: (): i32 {
  // (1 + 2 + 3 + 4) * 2 = 20
  run() == 20.0 ? 42 | 1
}
`

// The transitions run: the device doubles the buffer while it holds it.
func TestE2EBufferCustodyTransitions(t *testing.T) {
	helper := filepath.Join(t.TempDir(), "mlrt.c")
	if err := os.WriteFile(helper, []byte(custodyHelperC), 0o644); err != nil {
		t.Fatal(err)
	}
	_, code, abnormal := buildAndRunFrom(t, "buffer_custody", New().WithSource("buffer_custody.oak", custodyProgram), helper)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	emitted, err := New().WithSource("buffer_custody.oak", custodyProgram).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"extern void mlrt_submit( f32 *b, size_t b_len );",
		"extern void mlrt_complete( f32 *b, size_t b_len );",
	} {
		if !strings.Contains(emitted, want) {
			t.Fatalf("missing %q in the C", want)
		}
	}
}

// Custody is checked statically: a device buffer cannot be borrowed or
// handed back, a moved binding is dead, a transition takes the binding
// itself and initializes a Buffer binding, and the extern's shape is held
// to the transition form.
func TestBufferCustodyRejections(t *testing.T) {
	prelude := `
malloc: (n: c.Size): c.Ptr = c.extern("malloc")
submit: (b: Buffer[f32, Host]): Buffer[f32, Device] = c.extern("mlrt_submit")
complete: (b: Buffer[f32, Device]): Buffer[f32, Host] = c.extern("mlrt_complete")
`
	cases := map[string]struct{ src, want string }{
		"borrow in device custody": {prelude + `
f: (): f32 {
  r: f32 = 0.0
  unsafe {
    b: Buffer[f32] = c.own[f32](malloc(c.Size(u32(16))), u32(4))
    d: Buffer[f32, Device] = submit(b)
    v: []f32 = view(&d)
    r = v[0]
  }
  r
}
main: (): i32 = 0
`, "in Device custody and cannot be borrowed"},
		"disown in device custody": {prelude + `
f: (): () {
  unsafe {
    b: Buffer[f32] = c.own[f32](malloc(c.Size(u32(16))), u32(4))
    d: Buffer[f32, Device] = submit(b)
    p: c.Ptr = c.disown(d)
  }
}
main: (): i32 = 0
`, "in Device custody and cannot be handed back"},
		"use after move": {prelude + `
f: (): u32 {
  n: u32 = 0
  unsafe {
    b: Buffer[f32] = c.own[f32](malloc(c.Size(u32(16))), u32(4))
    d: Buffer[f32, Device] = submit(b)
    n = len(b)
  }
  n
}
main: (): i32 = 0
`, "OAK-B0111"},
		"move while borrowed": {prelude + `
f: (): u32 {
  n: u32 = 0
  unsafe {
    b: Buffer[f32] = c.own[f32](malloc(c.Size(u32(16))), u32(4))
    v: []f32 = view(&b)
    d: Buffer[f32, Device] = submit(b)
    n = len(v)
  }
  n
}
main: (): i32 = 0
`, "cannot change custody while borrow"},
		"wrong state": {prelude + `
f: (): () {
  unsafe {
    b: Buffer[f32] = c.own[f32](malloc(c.Size(u32(16))), u32(4))
    d: Buffer[f32, Host] = complete(b)
  }
}
main: (): i32 = 0
`, "Buffer[f32, Device]"},
		"result not bound": {prelude + `
f: (): u32 {
  n: u32 = 0
  unsafe {
    b: Buffer[f32] = c.own[f32](malloc(c.Size(u32(16))), u32(4))
    n = len(submit(b))
  }
  n
}
main: (): i32 = 0
`, "initializes a Buffer binding"},
		"no buffer return":   {"sync: (b: Buffer[f32, Device]): c.Int = c.extern(\"mlrt_sync\")\nmain: (): i32 = 0\n", "OAK-F0110"},
		"unit return":        {"sync: (b: Buffer[f32, Device]): () = c.extern(\"mlrt_sync\")\nmain: (): i32 = 0\n", "OAK-F0110"},
		"two buffers":        {"pair: (a: Buffer[f32], b: Buffer[f32]): Buffer[f32, Device] = c.extern(\"mlrt_pair\")\nmain: (): i32 = 0\n", "OAK-F0110"},
		"element mismatch":   {"conv: (b: Buffer[f32]): Buffer[u8, Device] = c.extern(\"mlrt_conv\")\nmain: (): i32 = 0\n", "OAK-F0110"},
		"same state":         {"nop: (b: Buffer[f32]): Buffer[f32, Host] = c.extern(\"mlrt_nop\")\nmain: (): i32 = 0\n", "OAK-F0110"},
		"state names a type": {"Device: type = struct { id: u32 }\nsubmit: (b: Buffer[f32, Host]): Buffer[f32, Device] = c.extern(\"mlrt_submit\")\nmain: (): i32 = 0\n", "names a state, not the declared type"},
		"plain function":     {"f: (b: Buffer[f32, Device]): Buffer[f32, Host] = b\nmain: (): i32 = 0\n", "cannot be a parameter"},
	}
	for name, c := range cases {
		_, err := New().WithSource("custody.oak", c.src).EmitC().Get()
		if err == nil {
			t.Fatalf("%s: compiled; want %q", name, c.want)
		}
		if !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: want %q, got %v", name, c.want, err)
		}
	}
}
