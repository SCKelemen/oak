package compiler

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// A Buffer inside a record (docs/spec/92-ffi.md section 2.8.6; the ml
// pilot's follow-up to F5): the record literal moves the buffer binding in
// and the record binding holds the custody — borrowed through the field
// while in Host custody, moved out by a custody transition or c.disown,
// after which the whole record is dead. A custody state with more than a
// name is such a record over the buffer: Submitted carries the device.
const bufferFieldsProgram = `
malloc: (n: c.Size): c.Ptr = c.extern("malloc")
free: (p: c.Ptr): () = c.extern("free")
submit: (b: Buffer[f32, Host]): Buffer[f32, Device] = c.extern("mlrt_submit")
complete: (b: Buffer[f32, Device]): Buffer[f32, Host] = c.extern("mlrt_complete")

Weights: type = struct { data: Buffer[f32], scale: f32 }
Submitted: type = struct { data: Buffer[f32, Device], device: u32 }

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
    w: Weights = Weights { data: host, scale: 2.0 }
    before: f32 = total(view(&w.data)) * w.scale
    count: u32 = len(w.data)
    d: Buffer[f32, Device] = submit(w.data)
    s: Submitted = Submitted { data: d, device: 1 }
    device: u32 = s.device
    back: Buffer[f32] = complete(s.data)
    result = before + total(view(&back)) + f32_round_u32(device) + f32_round_u32(count)
    free(c.disown(back))
  }
  result
}

main: (): i32 {
  run() == 45.0 ? 42 | 1
}
`

func TestE2EBufferFields(t *testing.T) {
	helper := filepath.Join(t.TempDir(), "mlrt.c")
	if err := os.WriteFile(helper, []byte(custodyHelperC), 0o644); err != nil {
		t.Fatal(err)
	}
	// 1+2+3+4 = 10, scaled 20; the device doubles: 20; device 1; count 4.
	_, code, abnormal := buildAndRunFrom(t, "buffer_fields", New().WithSource("buffer_fields.oak", bufferFieldsProgram), helper)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	emitted, err := New().WithSource("buffer_fields.oak", bufferFieldsProgram).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"oak_span_f32 data;",
		"mlrt_submit( ( w.data ).base, (size_t)( w.data ).len )",
		"mlrt_complete( ( s.data ).base, (size_t)( s.data ).len )",
	} {
		if !strings.Contains(emitted, want) {
			t.Fatalf("missing %q in the C:\n%s", want, emitted)
		}
	}
}

// The record carries the custody, so every rule of a Buffer binding holds
// of the record: dead after its buffer moves, borrowed only at Host,
// built from a binding by name, never copied, passed, or reassigned.
func TestBufferFieldsRejections(t *testing.T) {
	prelude := `
malloc: (n: c.Size): c.Ptr = c.extern("malloc")
submit: (b: Buffer[f32, Host]): Buffer[f32, Device] = c.extern("mlrt_submit")
complete: (b: Buffer[f32, Device]): Buffer[f32, Host] = c.extern("mlrt_complete")
Weights: type = struct { data: Buffer[f32], scale: f32 }
Submitted: type = struct { data: Buffer[f32, Device], device: u32 }
own4: (): c.Ptr = malloc(c.Size(u32(16)))
`
	cases := map[string]struct{ src, want string }{
		"record dead after the move": {prelude + `
f: (): u32 {
  n: u32 = 0
  unsafe {
    b: Buffer[f32] = c.own[f32](own4(), u32(4))
    w: Weights = Weights { data: b, scale: 1.0 }
    d: Buffer[f32, Device] = submit(w.data)
    n = len(w.data)
  }
  n
}
main: (): i32 = 0
`, "OAK-B0111"},
		"scalar field dead after the move": {prelude + `
f: (): u32 {
  n: u32 = 0
  unsafe {
    b: Buffer[f32] = c.own[f32](own4(), u32(4))
    d: Buffer[f32, Device] = submit(b)
    s: Submitted = Submitted { data: d, device: 3 }
    back: Buffer[f32] = complete(s.data)
    n = s.device
  }
  n
}
main: (): i32 = 0
`, "OAK-B0111"},
		"buffer dead after moving into the record": {prelude + `
f: (): u32 {
  n: u32 = 0
  unsafe {
    b: Buffer[f32] = c.own[f32](own4(), u32(4))
    w: Weights = Weights { data: b, scale: 1.0 }
    n = len(b)
  }
  n
}
main: (): i32 = 0
`, "OAK-B0111"},
		"move into a record while borrowed": {prelude + `
f: (): u32 {
  n: u32 = 0
  unsafe {
    b: Buffer[f32] = c.own[f32](own4(), u32(4))
    v: []f32 = view(&b)
    w: Weights = Weights { data: b, scale: 1.0 }
    n = len(v)
  }
  n
}
main: (): i32 = 0
`, "cannot move into a record while borrow"},
		"borrow through a device field": {prelude + `
f: (): f32 {
  r: f32 = 0.0
  unsafe {
    b: Buffer[f32] = c.own[f32](own4(), u32(4))
    d: Buffer[f32, Device] = submit(b)
    s: Submitted = Submitted { data: d, device: 3 }
    v: []f32 = view(&s.data)
    r = v[0]
  }
  r
}
main: (): i32 = 0
`, "in Device custody and cannot be borrowed"},
		"field from an expression": {prelude + `
f: (): () {
  unsafe {
    w: Weights = Weights { data: c.own[f32](own4(), u32(4)), scale: 1.0 }
  }
}
main: (): i32 = 0
`, "takes the Buffer binding itself"},
		"record copied": {prelude + `
f: (): () {
  unsafe {
    b: Buffer[f32] = c.own[f32](own4(), u32(4))
    w: Weights = Weights { data: b, scale: 1.0 }
    w2: Weights = w
  }
}
main: (): i32 = 0
`, "cannot be copied"},
		"record passed": {prelude + `
g: (w: Weights): f32 = w.scale
main: (): i32 = 0
`, "cannot be a parameter"},
		"field reassigned": {prelude + `
f: (): () {
  unsafe {
    b: Buffer[f32] = c.own[f32](own4(), u32(4))
    w: Weights = Weights { data: b, scale: 1.0 }
    b2: Buffer[f32] = c.own[f32](own4(), u32(4))
    w.data = b2
  }
}
main: (): i32 = 0
`, "is set once, by the record literal"},
		"literal not bound": {prelude + `
f: (): () {
  unsafe {
    b: Buffer[f32] = c.own[f32](own4(), u32(4))
    Weights { data: b, scale: 1.0 }
  }
}
main: (): i32 = 0
`, "Buffer"},
	}
	for name, c := range cases {
		_, err := New().WithSource("fields.oak", c.src).EmitC().Get()
		if err == nil {
			t.Fatalf("%s: compiled; want %q", name, c.want)
		}
		if !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: want %q, got %v", name, c.want, err)
		}
	}
}
