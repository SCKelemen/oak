package typechecker

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/semir"
)

func TestArm64BarrierInstructionFunctionsTypecheck(t *testing.T) {
	for _, member := range semir.Arm64BarrierMembers() {
		t.Run(member, func(t *testing.T) {
			input := "fn f() -> () = arm64." + member + "()"
			tc := setupTypeChecker(input)
			program := parseProgram(input)
			tc.CheckProgram(program)
			if len(tc.Errors()) != 0 {
				t.Fatalf("valid barrier %s rejected: %v", member, tc.Errors())
			}
			arity, ok := Arm64IntrinsicArity(member)
			if !ok || arity != 0 {
				t.Fatalf("barrier %s arity = %d, ok=%v; want 0,true", member, arity, ok)
			}
		})
	}
}

func TestArm64BarrierRejectsOperands(t *testing.T) {
	input := "fn f() -> () = arm64.dmb_ish(u32(1))"
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)
	if len(tc.Errors()) == 0 {
		t.Fatal("barrier with runtime operand unexpectedly typechecked")
	}
	all := strings.Join(tc.Errors(), "\n")
	if !strings.Contains(all, "expects 0 arguments") && !strings.Contains(all, "0 argument") {
		t.Fatalf("barrier arity diagnostic is not explicit: %v", tc.Errors())
	}
}

func TestUnknownArm64BarrierStillFailsClosed(t *testing.T) {
	input := "fn f() -> () = arm64.dsb_outer_shareable()"
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)
	if len(tc.Errors()) == 0 {
		t.Fatal("unknown barrier spelling unexpectedly typechecked")
	}
}
