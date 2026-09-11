package typechecker

import (
	"strings"
	"testing"
)

// The FFI boundary rules of docs/spec/92-ffi.md: extern signatures are
// c.*-only (OAK-F0101), symbols are C identifiers (OAK-F0102), c.extern is
// definition-only (OAK-F0103), conversions are the exact table rows, and
// the instruction functions are ordinary typed calls.
func TestFFIBoundaryRules(t *testing.T) {
	tests := []struct {
		name       string
		input      string
		hasError   bool
		wantInText string
	}{
		{
			"valid extern binding over c types",
			"putchar: (ch: c.Int): c.Int = c.extern(\"putchar\")",
			false, "",
		},
		{
			"valid nullary extern with unit return",
			"flush: (): () = c.extern(\"fflush_unlocked\")",
			false, "",
		},
		{
			"extern parameter must be a c type",
			"putchar: (ch: i32): c.Int = c.extern(\"putchar\")",
			true, "OAK-F0101",
		},
		// Boundary spans (docs/spec/92-ffi.md section 2.5).
		{
			"span_of stands for a c.Ptr, c.Size pair",
			"write: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern(\"write\")\nemit: (bytes: []u8): () { _ = write(c.Int(1), c.span_of(bytes)) }",
			false, "",
		},
		{
			"span_mut_of over a writable span",
			"fill: (into: c.Ptr, count: c.Size): c.Int = c.extern(\"fill\")\nrun: (buffer: [*]u8): () { _ = fill(c.span_mut_of(buffer)) }",
			false, "",
		},
		{
			"span_of must line up with c.Ptr then c.Size",
			"bad: (data: c.Ptr, fd: c.Int): c.Int = c.extern(\"bad\")\nemit: (bytes: []u8): () { _ = bad(c.span_of(bytes), c.Int(1)) }",
			true, "OAK-F0105",
		},
		{
			"span_of counts as two positions in the arity",
			"write: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern(\"write\")\nemit: (bytes: []u8): () { _ = write(c.Int(1), c.span_of(bytes), c.Size(u32(1))) }",
			true, "expects 3 arguments, got 4",
		},
		{
			"span_of needs a read-only view",
			"write: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern(\"write\")\nemit: (buffer: [*]u8): () { _ = write(c.Int(1), c.span_of(buffer)) }",
			true, "c.span_of takes a read-only view",
		},
		{
			"span element type must cross the boundary",
			"P: type = { x: u32, y: u32 }\nwrite: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern(\"write\")\nemit: (points: []P): () { _ = write(c.Int(1), c.span_of(points)) }",
			true, "OAK-F0104",
		},
		{
			"span of f64 crosses the boundary",
			"write: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern(\"write\")\nemit: (xs: []f64): () { _ = write(c.Int(1), c.span_of(xs)) }",
			false, "",
		},
		{
			"span of f16 storage crosses the boundary as its carrier",
			"write: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern(\"write\")\nemit: (xs: []f16): () { _ = write(c.Int(1), c.span_of(xs)) }",
			false, "",
		},
		{
			"span of a declared struct with float fields crosses the boundary",
			"Point: type = struct { x: f32, y: f32 }\nwrite: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern(\"write\")\nemit: (points: []Point): () { _ = write(c.Int(1), c.span_of(points)) }",
			false, "",
		},
		{
			"span of a nested struct crosses the boundary",
			"Point: type = struct { x: f32, y: f32 }\nSegment: type = struct { from: Point, to: Point, tag: u8, ok: Bool }\nwrite: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern(\"write\")\nemit: (s: []Segment): () { _ = write(c.Int(1), c.span_of(s)) }",
			false, "",
		},
		{
			"span of a struct with a string field is rejected",
			"Named: type = struct { name: string, id: u32 }\nwrite: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern(\"write\")\nemit: (s: []Named): () { _ = write(c.Int(1), c.span_of(s)) }",
			true, "OAK-F0104",
		},
		{
			"span of a struct with a view field is rejected",
			"Holder: type = struct { bytes: []u8, id: u32 }\nwrite: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern(\"write\")\nemit: (s: []Holder): () { _ = write(c.Int(1), c.span_of(s)) }",
			true, "OAK-F0104",
		},
		{
			"span_of is not an expression",
			"emit: (bytes: []u8): c.Ptr { c.span_of(bytes) }",
			true, "OAK-F0103",
		},
		{
			"span_of cannot be passed to Oak code",
			"take: (p: c.Ptr, n: c.Size): () { }\nemit: (bytes: []u8): () { take(c.span_of(bytes)) }",
			true, "OAK-F0103",
		},
		{
			"c.String from a literal",
			"puts: (s: c.String): c.Int = c.extern(\"puts\")\nsay: (): () { _ = puts(c.String(\"hello\")) }",
			false, "",
		},
		{
			"c.String requires a literal",
			"puts: (s: c.String): c.Int = c.extern(\"puts\")\nsay: (text: string): () { _ = puts(c.String(text)) }",
			true, "OAK-F0106",
		},
		{
			"extern return must be a c type or unit",
			"putchar: (ch: c.Int): i32 = c.extern(\"putchar\")",
			true, "OAK-F0101",
		},
		{
			"extern symbol must be a C identifier",
			"boom: (): () = c.extern(\"evil(); //\")",
			true, "OAK-F0102",
		},
		{
			"c.extern is not an expression",
			"fn f() -> i32 { x := c.extern(\"puts\")\n1 }",
			true, "OAK-F0103",
		},
		{
			"extern call before the binding in source order",
			"fn f() -> c.Int = putchar(c.Int(65))\nputchar: (ch: c.Int): c.Int = c.extern(\"putchar\")",
			false, "",
		},
		{
			"exact-width conversion round trip",
			"fn f() -> i32 { n: c.Int32 = c.Int32(41)\ni32(n) + 1 }",
			false, "",
		},
		{
			"untyped literals infer against the conversion operand",
			"fn f() -> c.Int64 = c.Int64(7)",
			false, "",
		},
		{
			"conversion rejects a mismatched typed operand",
			"fn f(x: u32) -> c.Int32 = c.Int32(x)",
			true, "c.Int32 converts i32 values",
		},
		{
			"no inverse for c.Size",
			"fn f(x: c.Size) -> u32 = u32(x)",
			true, "",
		},
		{
			"c types are nominal, not interchangeable",
			"fn f(x: c.Int32) -> c.Int = x",
			true, "",
		},
		{
			"no arithmetic on c types",
			"fn f(x: c.Int, y: c.Int) -> c.Int = x + y",
			true, "",
		},
		{
			"intrinsics type as ordinary functions",
			"fn f(x: u64) -> u64 = arm64.clz64(x)",
			false, "",
		},
		{
			"intrinsic operand width is enforced",
			"fn f(x: u32) -> u64 = arm64.clz64(x)",
			true, "arm64.clz64 expects u64",
		},
		{
			"unknown instruction functions are rejected",
			"fn f(x: u64) -> u64 = arm64.popcount(x)",
			true, "no instruction function",
		},
		{
			"a local named c shadows the library in expression position",
			"fn f() -> i32 { c: i32 = 1\nc + 1 }",
			false, "",
		},
		{
			"simd ops type as ordinary functions",
			"f: (a, b: simd.U8x16): simd.U8x16 = simd.add_u8x16(a, b)",
			false, "",
		},
		{
			"simd vector types are nominal per shape",
			"fn f(a: simd.U8x16, b: simd.U32x4) -> simd.U8x16 = simd.add_u8x16(a, b)",
			true, "simd.add_u8x16 expects simd.U8x16",
		},
		{
			"simd load requires the matching element view",
			"fn f(v: []u32) -> simd.U8x16 = simd.load_u8x16(v, u32(0))",
			true, "",
		},
		{
			"simd store requires a writable span, not a view",
			"fn f(v: []u8, x: simd.U8x16) -> () = simd.store_u8x16(v, u32(0), x)",
			true, "",
		},
		{
			"unknown simd operations are rejected",
			"fn f(a: simd.U8x16) -> simd.U8x16 = simd.shuffle_u8x16(a)",
			true, "no operation",
		},
		{
			"reductions return Bool",
			"f: (a, b: simd.U8x16): Bool = simd.any_u8x16(simd.eq_u8x16(a, b))",
			false, "",
		},
		{
			"vectors cannot cross the extern boundary",
			"boom: (x: simd.U8x16): () = c.extern(\"boom\")",
			true, "OAK-F0101",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			tc := setupTypeChecker(tt.input)
			program := parseProgram(tt.input)
			tc.CheckProgram(program)

			hasError := len(tc.Errors()) > 0
			if hasError != tt.hasError {
				t.Fatalf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
			}
			if tt.wantInText == "" {
				return
			}
			all := strings.Join(tc.Errors(), "\n")
			for _, d := range tc.Diagnostics() {
				all += "\n" + d.Code + " " + d.Message
			}
			if !strings.Contains(all, tt.wantInText) {
				t.Fatalf("diagnostics %q do not mention %q", all, tt.wantInText)
			}
		})
	}
}
