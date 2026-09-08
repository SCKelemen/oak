package borrowchecker

import "testing"

func TestStringViewProvenance(t *testing.T) {
	for _, fixture := range []struct {
		name   string
		source string
		reject bool
	}{
		{"parameter bridge", "f: (bytes: []u8): u32 { text: string = str_from_utf8(bytes)\nback: []u8 = str_bytes(text)\nlen(back) }", false},
		{"string parameter", "f: (text: string): u32 { back: []u8 = str_bytes(text)\nlen(back) }", false},
		{"literal return", "f: (): string { \"literal\" }", false},
		{"borrowed return", "f: (bytes: []u8): string { text: string = str_from_utf8(bytes)\ntext }", true},
		{"alias return", "f: (text: string): string { alias: string = text\nalias }", true},
		{"owner write", "f: (): u32 { data: [1]u8\nbytes: []u8 = view(&data)\ntext: string = str_from_utf8(bytes)\nback: []u8 = str_bytes(text)\ndata[0] = u8(1)\nlen(back) }", true},
		{"inner view alias", "f: (): u32 { data: [1]u8\nbytes: []u8 = view(&data)\ntrue ? { alias: []u8 = bytes }\ndata[0] = u8(1)\nu32(0) }", true},
		{"borrow released", "f: (): u32 { data: [1]u8\ntrue ? { bytes: []u8 = view(&data)\ntext: string = str_from_utf8(bytes)\nback: []u8 = str_bytes(text) }\ndata[0] = u8(1)\nu32(0) }", false},
		{"outer assignment", "f: (): u32 { out: string = \"\"\ntrue ? { data: [1]u8\nbytes: []u8 = view(&data)\nout = str_from_utf8(bytes) }\nu32(0) }", true},
		{"string aggregate", "Box[T]: type = Value: T\nf: (text: string): u32 { box: Box[string] = .Value(text)\nu32(0) }", true},
		{"span alias suspends parent", "f: (write: [*]u8): u32 { alias: [*]u8 = write\nwrite[0] = u8(1)\nu32(0) }", true},
		{"span alias released", "f: (write: [*]u8): u32 { true ? { alias: [*]u8 = write\nalias[0] = u8(1) }\nwrite[0] = u8(2)\nu32(0) }", false},
	} {
		t.Run(fixture.name, func(t *testing.T) {
			bc, program, tc := setupBorrowCheckerForTest(fixture.source)
			if program == nil {
				t.Fatal("fixture failed to parse")
			}
			if errors := tc.Errors(); len(errors) != 0 {
				t.Fatalf("fixture must typecheck: %v", errors)
			}
			bc.CheckProgram(program, tc.Env())
			if (len(bc.Errors()) != 0) != fixture.reject {
				t.Fatalf("reject=%v, errors=%v", fixture.reject, bc.Errors())
			}
		})
	}
}
