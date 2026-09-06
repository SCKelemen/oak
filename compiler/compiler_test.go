package compiler

import (
	"strconv"
	"strings"
	"testing"
)

func TestStageGenericMethodsCanChangeType(t *testing.T) {
	length, err := Value(21).
		Then(func(value int) (string, error) {
			return strconv.Itoa(value * 2), nil
		}).
		Map(func(value string) int {
			return len(value)
		}).
		Get()
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if length != 2 {
		t.Fatalf("expected transformed length 2, got %d", length)
	}
}

func TestStageStopsAtFirstError(t *testing.T) {
	called := false
	_, err := Failure[int](strconv.ErrSyntax).
		Then(func(value int) (string, error) {
			called = true
			return strconv.Itoa(value), nil
		}).
		Get()
	if err == nil {
		t.Fatal("expected error")
	}
	if called {
		t.Fatal("transform ran after failed stage")
	}
}

func TestCompilationFluentEmitC(t *testing.T) {
	const source = `
x: i32 = 5
y: i32 = 10
z: i32 = x + y
`

	generated, err := New().
		WithSource("simple.oak", source).
		WithPackageName("example").
		WithPlatformSizes(64, 64).
		EmitC().
		Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(generated, "Generated C code from Oak") {
		t.Fatalf("expected C backend output, got:\n%s", generated)
	}
}

func TestCompilationWithMethodsDoNotMutateBase(t *testing.T) {
	base := New()
	left := base.WithSource("left.oak", "x: i32 = 1").WithPackageName("left")
	right := base.WithSource("right.oak", "x: i32 = 2").WithPackageName("right")

	if base.Source().Path != "main.oak" || base.Options().PackageName != "main" {
		t.Fatal("base compilation was mutated")
	}
	if left.Source().Path != "left.oak" || left.Options().PackageName != "left" {
		t.Fatal("left compilation has unexpected configuration")
	}
	if right.Source().Path != "right.oak" || right.Options().PackageName != "right" {
		t.Fatal("right compilation has unexpected configuration")
	}
}
