package compiler

import "testing"

// The 8-bit storage formats cross the boundary as uint8_t carriers
// (docs/spec/92-ffi.md section 2.5.1): a view of eight f8e4m3 and one of
// eight f8e5m2 reach libc write as their bit patterns, one byte each.
func TestE2EBoundarySpanF8Elements(t *testing.T) {
	stdout, code, abnormal := buildAndRunOutput(t, "ffif8spans", `
write: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern("write")

dump_e4m3: (xs: []f8e4m3): () {
  _ = write(c.Int(1), c.span_of(xs))
}

dump_e5m2: (xs: []f8e5m2): () {
  _ = write(c.Int(1), c.span_of(xs))
}

main: (): i32 {
  one: f8e4m3 = f8e4m3_round_f32(1.0)
  a: [8]f8e4m3 = [8]f8e4m3{one, f8e4m3_round_f32(-2.0), f8e4m3_round_f32(448.0), f8e4m3_saturating_f32(1000.0), one, one, one, one}
  dump_e4m3(view(&a))
  b: [8]f8e5m2 = [8]f8e5m2{f8e5m2_round_f32(1.0), f8e5m2_round_f32(57344.0), f8e5m2_round_f32(65536.0), f8e5m2_bits_u8(u8(1)), f8e5m2_round_f32(1.0), f8e5m2_round_f32(1.0), f8e5m2_round_f32(1.0), f8e5m2_round_f32(1.0)}
  dump_e5m2(view(&b))
  0
}
`)
	if abnormal || code != 0 {
		t.Fatalf("exit = (%d, abnormal=%v), want 0", code, abnormal)
	}
	want := string([]byte{0x38, 0xC0, 0x7E, 0x7E, 0x38, 0x38, 0x38, 0x38, 0x3C, 0x7B, 0x7C, 0x01, 0x3C, 0x3C, 0x3C, 0x3C})
	if stdout != want {
		t.Fatalf("stdout = % x, want % x", stdout, want)
	}
}
