package typechecker

import (
	"strings"
	"testing"
)

func TestArm64TLBIFunctionTypechecks(t *testing.T) {
	input := "fn f() -> () = arm64.tlbi_vmalls12e1is()"
	tc := setupTypeChecker(input)
	tc.CheckProgram(parseProgram(input))
	if len(tc.Errors()) != 0 {
		t.Fatalf("valid TLBI rejected: %v", tc.Errors())
	}
	if arity, ok := Arm64IntrinsicArity("tlbi_vmalls12e1is"); !ok || arity != 0 {
		t.Fatalf("TLBI arity = %d, ok=%v; want 0,true", arity, ok)
	}
}

func TestArm64TLBIRejectsOperandsAndNearbySpellings(t *testing.T) {
	tests := []struct {
		name  string
		input string
		want  string
	}{
		{"operand", "fn f() -> () = arm64.tlbi_vmalls12e1is(u32(1))", "0 argument"},
		{"generic", "fn f() -> () = arm64.tlbi()", "no instruction function"},
		{"plain local form", "fn f() -> () = arm64.tlbi_vmalls12e1()", "no instruction function"},
		{"missing tlbi prefix", "fn f() -> () = arm64.vmalls12e1is()", "no instruction function"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			tc := setupTypeChecker(test.input)
			tc.CheckProgram(parseProgram(test.input))
			if len(tc.Errors()) == 0 {
				t.Fatal("invalid TLBI unexpectedly typechecked")
			}
			if got := strings.Join(tc.Errors(), "\n"); !strings.Contains(got, test.want) {
				t.Fatalf("diagnostic %q does not contain %q", got, test.want)
			}
		})
	}
}
