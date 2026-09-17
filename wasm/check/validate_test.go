package check

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"strings"
	"testing"
)

// Test fixtures are assembled here from the binary grammar, not by wasm.Emit.
func testU32(n uint32) []byte {
	var out []byte
	for n >= 128 {
		out = append(out, byte(n&127)|128)
		n >>= 7
	}
	return append(out, byte(n))
}

func fixtureSection(id byte, payload []byte) []byte {
	out := append([]byte{id}, testU32(uint32(len(payload)))...)
	return append(out, payload...)
}

func fixtureModule(types, declarations, exports []byte, bodies ...[]byte) []byte {
	out := []byte{0, 0x61, 0x73, 0x6d, 1, 0, 0, 0}
	out = append(out, fixtureSection(1, types)...)
	out = append(out, fixtureSection(3, declarations)...)
	out = append(out, fixtureSection(7, exports)...)
	code := testU32(uint32(len(bodies)))
	for _, body := range bodies {
		code = append(code, testU32(uint32(len(body)))...)
		code = append(code, body...)
	}
	return append(out, fixtureSection(10, code)...)
}

func scalarFixture(result byte, code ...byte) []byte {
	types := []byte{1, 0x60, 0, 1, result}
	if result == 0 {
		types = []byte{1, 0x60, 0, 0}
	}
	return fixtureModule(types, []byte{1, 0}, []byte{1, 1, 'f', 0, 0}, append([]byte{0}, code...))
}

func controlFixtures() []struct {
	name   string
	result byte
	code   []byte
	valid  bool
} {
	return []struct {
		name   string
		result byte
		code   []byte
		valid  bool
	}{
		{"constant", 0x7f, []byte{0x41, 42, 0x0b}, true},
		{"unit", 0, []byte{0x0b}, true},
		{"wide", 0x7e, []byte{0x42, 0x7f, 0x0b}, true},
		{"i32.div_s", 0x7f, []byte{0x41, 7, 0x41, 3, 0x6d, 0x0b}, true},
		{"i32.div_u", 0x7f, []byte{0x41, 7, 0x41, 3, 0x6e, 0x0b}, true},
		{"i32.rem_s", 0x7f, []byte{0x41, 7, 0x41, 3, 0x6f, 0x0b}, true},
		{"i32.rem_u", 0x7f, []byte{0x41, 7, 0x41, 3, 0x70, 0x0b}, true},
		{"i64.div_s", 0x7e, []byte{0x42, 7, 0x42, 3, 0x7f, 0x0b}, true},
		{"i64.div_u", 0x7e, []byte{0x42, 7, 0x42, 3, 0x80, 0x0b}, true},
		{"i64.rem_s", 0x7e, []byte{0x42, 7, 0x42, 3, 0x81, 0x0b}, true},
		{"i64.rem_u", 0x7e, []byte{0x42, 7, 0x42, 3, 0x82, 0x0b}, true},
		{"polymorphic", 0x7f, []byte{0, 0x6a, 0x0b}, true},
		{"known type still checked", 0x7f, []byte{0, 0x42, 0, 0x6a, 0x0b}, false},
		{"branch to function", 0x7f, []byte{0x41, 9, 0x0c, 0, 0x0b}, true},
		{"branch missing result", 0x7f, []byte{0x0c, 0, 0x0b}, false},
		{"unknown label", 0, []byte{0, 0x0c, 1, 0x0b}, false},
		{"typed block", 0x7f, []byte{2, 0x7f, 0x41, 7, 0x0b, 0x0b}, true},
		{"typed if", 0x7f, []byte{0x41, 1, 4, 0x7f, 0x41, 7, 5, 0x41, 9, 0x0b, 0x0b}, true},
		{"typed if needs else", 0x7f, []byte{0x41, 1, 4, 0x7f, 0x41, 7, 0x0b, 0x0b}, false},
		{"empty if", 0, []byte{0x41, 0, 4, 0x40, 0x0b, 0x0b}, true},
		{"second else", 0, []byte{0x41, 0, 4, 0x40, 5, 5, 0x0b, 0x0b}, false},
		{"unmatched else", 0, []byte{5, 0x0b}, false},
		{"loop label uses inputs", 0x7f, []byte{3, 0x7f, 0x41, 1, 0x0c, 0, 0x0b, 0x0b}, true},
		{"branch conditional keeps result", 0x7f, []byte{2, 0x7f, 0x41, 7, 0x41, 1, 0x0d, 0, 0x0b, 0x0b}, true},
		{"branch conditional needs condition", 0, []byte{0x0d, 0, 0x0b}, false},
		{"block stack isolation", 0x7f, []byte{0x41, 7, 2, 0x40, 0x1a, 0x0b, 0x0b}, false},
		{"inner block not polymorphic", 0, []byte{0, 2, 0x40, 0x1a, 0x0b, 0x0b}, false},
		{"polymorphic known extra", 0, []byte{0, 0x41, 7, 0x0b}, false},
		{"drop bottom", 0, []byte{0, 0x1a, 0x0b}, true},
		{"extra stack", 0, []byte{0x41, 1, 0x0b}, false},
		{"wrong return", 0x7f, []byte{0x42, 1, 0x0f, 0x0b}, false},
		{"return", 0x7f, []byte{0x41, 1, 0x0f, 0x0b}, true},
		{"unknown local unreachable", 0, []byte{0, 0x20, 0, 0x1a, 0x0b}, false},
		{"unknown call unreachable", 0, []byte{0, 0x10, 1, 0x0b}, false},
		{"recursion", 0x7f, []byte{0x10, 0, 0x0b}, true},
		{"nonempty if condition", 0, []byte{0x42, 0, 4, 0x40, 0x0b, 0x0b}, false},
		{"unsupported unreachable opcode", 0, []byte{0, 0xff, 0x0b}, false},
		{"unsupported memory", 0x7f, []byte{0x41, 0, 0x28, 2, 0, 0x0b}, false},
		{"unsupported block index", 0, []byte{2, 0, 0x0b, 0x0b}, false},
		{"missing end", 0x7f, []byte{0x41, 1}, false},
		{"extra end", 0, []byte{0x0b, 0x0b}, false},
	}
}

func TestWasmDivisionOperandValidation(t *testing.T) {
	for _, op := range []byte{0x6d, 0x6e, 0x6f, 0x70, 0x7f, 0x80, 0x81, 0x82} {
		typ, literal, wrong := byte(0x7f), byte(0x41), byte(0x42)
		if op >= 0x7f {
			typ, literal, wrong = 0x7e, 0x42, 0x41
		}
		for _, code := range [][]byte{
			{literal, 7, op, 0x0b},           // missing second operand
			{literal, 7, wrong, 3, op, 0x0b}, // wrong RHS type
			{wrong, 7, literal, 3, op, 0x0b}, // wrong LHS type
			{0x00, wrong, 7, op, 0x0b},       // unreachable still checks known types
		} {
			if _, err := Validate(scalarFixture(typ, code...)); err == nil {
				t.Fatalf("opcode %x accepted %x", op, code)
			}
		}
		if _, err := Validate(scalarFixture(typ, literal, 7, literal, 0, op, 0x0b)); err != nil {
			t.Fatal("a runtime trap is not a structural type error:", err)
		}
	}
}

func TestWasmControlValidation(t *testing.T) {
	for _, tt := range controlFixtures() {
		t.Run(tt.name, func(t *testing.T) {
			data := scalarFixture(tt.result, tt.code...)
			report, err := Validate(data)
			if (err == nil) != tt.valid {
				t.Fatalf("valid=%v: %v", tt.valid, err)
			}
			if err != nil {
				if report.SHA256 != "" {
					t.Fatal("failed validation returned evidence")
				}
				return
			}
			hash := sha256.Sum256(data)
			if report.SHA256 != hex.EncodeToString(hash[:]) || report.Functions != 1 || len(report.Exports) != 1 || report.Instructions == 0 {
				t.Fatalf("bad byte report: %+v", report)
			}
		})
	}
}

func TestWasmBinaryValidation(t *testing.T) {
	base := scalarFixture(0x7f, 0x41, 42, 0x0b)
	for i := range base {
		if _, err := Validate(base[:i]); err == nil {
			t.Fatalf("truncation at %d accepted", i)
		}
	}
	types, decls, exports := []byte{1, 0x60, 0, 1, 0x7f}, []byte{1, 0}, []byte{1, 1, 'f', 0, 0}
	body := []byte{0, 0x41, 42, 0x0b}
	for name, bad := range map[string][]byte{
		"bad version":       append([]byte{0, 0x61, 0x73, 0x6d, 2, 0, 0, 0}, base[8:]...),
		"trailing byte":     append(append([]byte{}, base...), 0),
		"custom section":    append(append([]byte{}, base...), 0, 0),
		"import section":    append(append([]byte{}, base[:8]...), 2, 1, 0),
		"oversized section": append(append([]byte{}, base[:8]...), 1, 0xff, 0xff, 0xff, 0xff, 0x0f),
		"type count":        fixtureModule([]byte{0xff, 0xff, 0xff, 0xff, 0x0f}, decls, exports, body),
		"type index":        fixtureModule(types, []byte{1, 1}, exports, body),
		"duplicate export":  fixtureModule(types, decls, []byte{2, 1, 'f', 0, 0, 1, 'f', 0, 0}, body),
		"export index":      fixtureModule(types, decls, []byte{1, 1, 'f', 0, 1}, body),
		"export kind":       fixtureModule(types, decls, []byte{1, 1, 'f', 2, 0}, body),
		"UTF8":              fixtureModule(types, decls, []byte{1, 1, 0xff, 0, 0}, body),
		"wrong code count":  fixtureModule(types, decls, exports),
		"float type":        scalarFixture(0x7d, 0, 0x0b),
		"multi result":      fixtureModule([]byte{1, 0x60, 0, 2, 0x7f, 0x7f}, decls, exports, body),
		"local run count":   fixtureModule(types, decls, exports, []byte{1, 0xff, 0xff, 0xff, 0xff, 0x0f, 0x7f, 0, 0x0b}),
	} {
		t.Run(name, func(t *testing.T) {
			if _, err := Validate(bad); err == nil {
				t.Fatal("bad module accepted")
			}
		})
	}
	// Mixed parameter order, a forward call and implicit zero-initialized locals.
	good := fixtureModule([]byte{2, 0x60, 0, 1, 0x7e, 0x60, 2, 0x7f, 0x7e, 1, 0x7e}, []byte{2, 0, 1}, exports,
		[]byte{0, 0x41, 7, 0x42, 9, 0x10, 1, 0x0b}, []byte{1, 1, 0x7e, 0x20, 1, 0x22, 2, 0x0b})
	if _, err := Validate(good); err != nil {
		t.Fatal(err)
	}
	// Bytes are not aliased by the report's decoded export name/signature.
	report, _ := Validate(base)
	for i := range base {
		base[i] = 0
	}
	if report.Exports[0].Name != "f" || report.Exports[0].Results[0] != I32 {
		t.Fatal("report aliases caller bytes")
	}
}

func TestWasmValidationLimits(t *testing.T) {
	// A small declaration can request many locals; enforce the module-wide
	// quota before expanding each run, not merely a per-function maximum.
	body := append([]byte{1}, testU32(16400)...)
	body = append(body, 0x7f, 0x0b)
	if _, err := Validate(fixtureModule([]byte{1, 0x60, 0, 0}, []byte{3, 0, 0, 0}, []byte{0}, body, body, body)); err != nil {
		t.Fatal("valid bounded local runs refused", err)
	}
	if _, err := Validate(fixtureModule([]byte{1, 0x60, 0, 0}, []byte{4, 0, 0, 0, 0}, []byte{0}, body, body, body, body)); err == nil || !strings.Contains(err.Error(), "module local count limit") {
		t.Fatal("module-wide local budget not enforced", err)
	}
	for name, data := range map[string][]byte{
		"module":       make([]byte, MaxModuleBytes+1),
		"depth":        scalarFixture(0, append(bytes.Repeat([]byte{2, 0x40}, maxControlDepth), bytes.Repeat([]byte{0x0b}, maxControlDepth+1)...)...),
		"stack":        scalarFixture(0, append(bytes.Repeat([]byte{0x41, 0}, maxStack+1), 0x0b)...),
		"instructions": scalarFixture(0, append(bytes.Repeat([]byte{0x01}, maxInstructions), 0x0b)...),
	} {
		t.Run(name, func(t *testing.T) {
			if _, err := Validate(data); err == nil || (!strings.Contains(err.Error(), "limit") && !strings.Contains(err.Error(), "exceeds")) {
				t.Fatalf("missing limit refusal: %v", err)
			}
		})
	}
}

func TestWasmLEBDecode(t *testing.T) {
	for _, tt := range []struct {
		width  uint
		signed bool
		data   []byte
		want   uint64
		valid  bool
	}{
		{32, false, []byte{0x83, 0}, 3, true},
		{32, false, []byte{0xff, 0xff, 0xff, 0xff, 0x0f}, 4294967295, true},
		{32, false, []byte{0x80, 0x80, 0x80, 0x80, 0x10}, 0, false},
		{32, false, []byte{0x80, 0x80, 0x80, 0x80, 0x80, 0}, 0, false},
		{32, true, []byte{0xfe, 0x7f}, ^uint64(1), true},
		{32, true, []byte{0x80, 0x80, 0x80, 0x80, 0x78}, uint64(0xffffffff80000000), true},
		{32, true, []byte{0xff, 0xff, 0xff, 0xff, 7}, 2147483647, true},
		{32, true, []byte{0x80, 0x80, 0x80, 0x80, 8}, 0, false},
		{32, true, []byte{0xff, 0xff, 0xff, 0xff, 0x77}, 0, false},
		{64, true, []byte{0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0}, 9223372036854775807, true},
		{64, true, []byte{0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x7f}, uint64(1) << 63, true},
		{64, true, []byte{0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 1}, 0, false},
		{64, true, []byte{0x80}, 0, false},
	} {
		r := reader{data: tt.data}
		got := r.integer(tt.width, tt.signed)
		if (r.err == nil) != tt.valid || (tt.valid && got != tt.want) {
			t.Fatalf("%x s=%v/%d: got %x err=%v, want %x valid=%v", tt.data, tt.signed, tt.width, got, r.err, tt.want, tt.valid)
		}
	}
}

func FuzzWasmValidate(f *testing.F) {
	for _, tt := range controlFixtures() {
		f.Add(scalarFixture(tt.result, tt.code...))
	}
	f.Add([]byte{})
	f.Fuzz(func(t *testing.T, data []byte) {
		r, err := Validate(data)
		if err != nil {
			if r.SHA256 != "" {
				t.Fatal("partial evidence on refusal")
			}
			return
		}
		hash := sha256.Sum256(data)
		if r.SHA256 != hex.EncodeToString(hash[:]) {
			t.Fatal("wrong byte identity")
		}
	})
}
