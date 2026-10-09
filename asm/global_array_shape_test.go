package asm

import (
	"fmt"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func printedGlobalArrayType(element string, count int64) string {
	return (&ast.IndexExpression{TypeForm: ast.IndexArrayType, Left: &ast.Identifier{Value: element}, Index: &ast.IntegerLiteral{Value: count}}).String()
}

func TestGlobalArrayShapeCanonicalPrinter(t *testing.T) {
	for _, bits := range []int64{8, 16, 32, 64} {
		for _, sign := range []string{"u", "i"} {
			scalar := fmt.Sprintf("%s%d", sign, bits)
			t.Run(scalar, func(t *testing.T) {
				global := Global{Type: printedGlobalArrayType(scalar, 3), Aggregate: true, Size: 3 * bits / 8}
				elem, count, signed, ok := globalArrayShape(global)
				if !ok || elem != bits/8 || count != 3 || signed != (sign == "i") {
					t.Fatalf("AST.String type %q: got (%d, %d, %v, %v)", global.Type, elem, count, signed, ok)
				}
			})
		}
	}
}

func TestGlobalArrayShapeCompatibilityAndRefusals(t *testing.T) {
	for _, text := range []string{"u16[3]", "(u16[3])", "[3]u16", "([3]u16)"} {
		if elem, count, signed, ok := globalArrayShape(Global{Type: text, Aggregate: true, Size: 6}); !ok || elem != 2 || count != 3 || signed {
			t.Errorf("valid internal type %q: got (%d, %d, %v, %v)", text, elem, count, signed, ok)
		}
	}
	for _, tc := range []struct {
		name, text string
		size       int64
		aggregate  bool
	}{
		{"scalar", "u8", 1, true}, {"record", "Record", 6, true},
		{"record array", "[3]Record", 6, true}, {"nested array", "[3][2]u8", 6, true},
		{"float", "[3]f16", 6, true}, {"bool", "[3]Bool", 3, true},
		{"zero", "[0]u8", 0, true}, {"negative", "[-3]u16", 6, true},
		{"expression", "[1+2]u16", 6, true}, {"span", "[*]u16", 6, true},
		{"view", "[]u16", 6, true}, {"open paren", "(u16[3]", 6, true},
		{"close paren", "u16[3])", 6, true}, {"trailing text", "[3]u16extra", 6, true},
		{"short allocation", "[3]u16", 5, true}, {"long allocation", "[3]u16", 7, true},
		{"negative allocation", "[3]u16", -6, true}, {"not aggregate", "[3]u16", 6, false},
		{"count overflow", "[9223372036854775808]u8", 6, true},
		{"multiplication overflow", "[2305843009213693953]u64", 8, true},
		{"legacy multiplication overflow", "u64[2305843009213693953]", 8, true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			if _, _, _, ok := globalArrayShape(Global{Type: tc.text, Aggregate: tc.aggregate, Size: tc.size}); ok {
				t.Fatalf("accepted malformed or unsupported global %+v", tc)
			}
		})
	}
}

func TestVerifyCanonicalGlobalArraySignedReads(t *testing.T) {
	decl := "read: () -> i64"
	sig, err := parseSignatureWithBody(decl + " = { i64(buf[0]) }")
	if err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		name, instruction string
		want              VerdictKind
	}{
		{"signed byte", "ldrsb x0, [x9]", VerdictProven},
		{"wrong signedness", "ldrb w0, [x9]", VerdictMismatch},
		{"wrong index", "ldrsb x0, [x9, #1]", VerdictMismatch},
	} {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit("global_array.oakasm", decl+" = {\nclobber x9\nadrp x9, buf\nadd x9, x9, :lo12:buf\n"+tc.instruction+"\nret\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			fn := unit.Functions[0]
			fn.Globals = map[string]Global{"buf": {Type: printedGlobalArrayType("i8", 4), Aggregate: true, Size: 4}}
			if findings := Check(fn, sig, nil); len(findings) != 0 {
				t.Fatal(findings)
			}
			got := Verify(fn, sig, sig.Body)
			if got.Kind != tc.want {
				t.Fatalf("got %s: %s; want %s", got.Kind, got.Message, tc.want)
			}
		})
	}
}

func TestVerifyCanonicalGlobalArrayWrites(t *testing.T) {
	decl := "write: (value: u8) -> ()"
	sig, err := parseSignatureWithBody(decl + " = { buf[0] = value }")
	if err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		name, instruction string
		want              VerdictKind
	}{
		{"same element", "strb w0, [x9]", VerdictProven},
		{"wrong index", "strb w0, [x9, #1]", VerdictMismatch},
		{"wrong value", "add w0, w0, #1\nstrb w0, [x9]", VerdictMismatch},
	} {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit("global_array.oakasm", decl+" = {\nbind w0 = value\nclobber x9\nadrp x9, buf\nadd x9, x9, :lo12:buf\n"+tc.instruction+"\nret\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			fn := unit.Functions[0]
			fn.Globals = map[string]Global{"buf": {Type: printedGlobalArrayType("u8", 4), Aggregate: true, Size: 4}}
			if findings := Check(fn, sig, nil); len(findings) != 0 {
				t.Fatal(findings)
			}
			got := Verify(fn, sig, sig.Body)
			if got.Kind != tc.want {
				t.Fatalf("got %s: %s; want %s", got.Kind, got.Message, tc.want)
			}
		})
	}
}
