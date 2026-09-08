package borrowchecker

import "testing"

func TestSIMDGlobalEffects(t *testing.T) {
	for _, fixture := range []struct {
		name   string
		source string
		reject bool
	}{
		{"read helper", `data: [16]u8
read: (v: []u8): Bool = simd.any_u8x16(simd.load_u8x16(v, u32(0)))
f: (): Bool { v: []u8 = view(&data)
read(v) }`, false},
		{"direct read", `data: [16]u8
f: (): Bool { v: []u8 = view(&data)
simd.any_u8x16(simd.load_u8x16(v, u32(0))) }`, false},
		{"store helper", `data: [16]u8
write: (): () { dst: [*]u8 = span(&data)
simd.store_u8x16(dst, u32(0), simd.splat_u8x16(u8(1))) }
f: (): u32 { v: []u8 = view(&data)
write()
len(v) }`, true},
	} {
		t.Run(fixture.name, func(t *testing.T) {
			bc, program, tc := setupBorrowCheckerForTest(fixture.source)
			if program == nil || len(tc.Errors()) != 0 {
				t.Fatalf("fixture must typecheck: %v", tc.Errors())
			}
			bc.CheckProgram(program, tc.Env())
			if (len(bc.Errors()) != 0) != fixture.reject {
				t.Fatalf("reject=%v errors=%v", fixture.reject, bc.Errors())
			}
		})
	}
}
