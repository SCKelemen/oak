package borrowchecker

import "testing"

func TestBorrowStorageBoundaries(t *testing.T) {
	for _, fixture := range []struct {
		name   string
		source string
		reject bool
	}{
		{"nominal return", "Wrapped: type = Bytes: []u8\nleak: (v: []u8): Wrapped = .Bytes(v)", true},
		{"generic return", "Box[T]: type = Value: T\nleak: (v: []u8): Box[[]u8] = .Value(v)", true},
		{"generic record payload", "Inner: type = struct { bytes: []u8 }\nBox[T]: type = Value: T\nleak: (v: []u8): Box[Inner] = .Value(Inner { bytes: v })", true},
		{"record initialization", "Wrapped: type = struct { bytes: []u8 }\nf: (v: []u8): u32 { w: Wrapped = Wrapped { bytes: v }\nu32(0) }", true},
		{"uninitialized aggregate", "Wrapped: type = struct { bytes: []u8 }\nf: (): u32 { w: Wrapped\nu32(0) }", true},
		{"field assignment", "Wrapped: type = struct { bytes: []u8 }\nf: (w: Wrapped, v: []u8): u32 { w.bytes = v\nu32(0) }", true},
		{"array assignment", "f: (v: []u8): u32 { values: [2][]u8\nvalues[0] = v\nu32(0) }", true},
		{"outer assignment", "Wrapped: type = struct { bytes: []u8 }\nf: (w: Wrapped): u32 { true ? { data: [4]u8\nv: []u8 = view(&data)\nw = Wrapped { bytes: v } }\nu32(0) }", true},
		{"inline argument", "Wrapped: type = struct { bytes: []u8 }\nsink: (w: Wrapped): u32 = u32(0)\nf: (v: []u8): u32 = sink(Wrapped { bytes: v })", true},
		{"owned ADT", "Box[T]: type = Value: T\nf: (): Box[u32] = .Value(u32(42))", false},
		{"phantom argument", "Marker[T]: type = | Tag\nf: (): Marker[[]u8] = .Tag", false},
		{"ordinary direct borrow", "f: (v: []u8): u32 = len(v)", false},
		{"owned record", "Range: type = struct { start: u32, end: u32 }\nf: (): Range = Range { start: u32(0), end: u32(4) }", false},
	} {
		t.Run(fixture.name, func(t *testing.T) {
			bc, program, tc := setupBorrowCheckerForTest(fixture.source)
			if program == nil {
				t.Fatalf("fixture failed to parse: %s", fixture.source)
			}
			if errors := tc.Errors(); len(errors) != 0 {
				t.Fatalf("fixture must typecheck: %v", errors)
			}
			bc.CheckProgram(program, tc.Env())
			got := countDiagnosticsWithCode(bc, string(CodeBorrowEscape))
			if (got != 0) != fixture.reject {
				t.Fatalf("reject=%v, got %d escape diagnostics: %v", fixture.reject, got, bc.Errors())
			}
			if !fixture.reject && len(bc.Errors()) != 0 {
				t.Fatalf("owned storage must remain valid: %v", bc.Errors())
			}
		})
	}
}
