package compiler

import (
	"strings"
	"testing"
)

// The compile pipeline gates on every safety analysis: no C is emitted for
// unsound programs (memory safety, bounded execution), and the strict
// profile enforces zero warnings (docs/spec/85-discipline.md section 7).

func emit(t *testing.T, profile, src string) (string, error) {
	t.Helper()
	comp := New().WithSource("test.oak", src)
	if profile != "" {
		comp = comp.WithProfile(profile)
	}
	return comp.EmitC().Get()
}

func TestPipelineRejectsBorrowViolation(t *testing.T) {
	src := "buf: [16]u8\na: [*]u8 = span(&buf)\nb: [*]u8 = span(&buf)\n"
	_, err := emit(t, "", src)
	if err == nil {
		t.Fatal("overlapping spans in safe code must not compile")
	}
	if !strings.Contains(err.Error(), "OAK-B0106") {
		t.Fatalf("expected OAK-B0106 in error, got: %v", err)
	}
}

func TestPipelineRejectsEscapingView(t *testing.T) {
	src := "fn dangle(buf: [16]u8) -> []u8 { buf[0:8] }\n"
	_, err := emit(t, "", src)
	if err == nil {
		t.Fatal("escaping view must not compile")
	}
	if !strings.Contains(err.Error(), "OAK-B0109") {
		t.Fatalf("expected OAK-B0109 in error, got: %v", err)
	}
}

func TestPipelineRejectsStackRecursion(t *testing.T) {
	src := "fn f(n: i32) -> i32 { 1 + f(n) }\n"
	_, err := emit(t, "", src)
	if err == nil {
		t.Fatal("unbounded stack recursion must not compile")
	}
	if !strings.Contains(err.Error(), "OAK-D0101") {
		t.Fatalf("expected OAK-D0101 in error, got: %v", err)
	}
}

func TestPipelineEmitsCForSoundPrograms(t *testing.T) {
	src := "fn fact(n: i32, acc: i32) -> i32 {\n  n ?\n    | 0 -> acc\n    | _ -> fact(n - 1, acc * n)\n}\n"
	output, err := emit(t, "", src)
	if err != nil {
		t.Fatalf("sound program must compile: %v", err)
	}
	if !strings.Contains(output, "while (1)") {
		t.Fatalf("expected loop-lowered factorial in output:\n%s", output)
	}
}

// Recorded unsafe assumptions pass the default profile and reject in strict.
func TestStrictProfilePromotesWarnings(t *testing.T) {
	src := "buf: [16]u8\nunsafe {\na: [*]u8 = span(&buf)\nb: [*]u8 = span(&buf)\n}\n"
	if _, err := emit(t, "", src); err != nil {
		t.Fatalf("unsafe-admitted overlap must compile in the default profile: %v", err)
	}
	_, err := emit(t, "strict", src)
	if err == nil {
		t.Fatal("strict profile must reject recorded unsafe assumptions")
	}
	if !strings.Contains(err.Error(), "OAK-B0110") {
		t.Fatalf("expected OAK-B0110 in strict rejection, got: %v", err)
	}
}
