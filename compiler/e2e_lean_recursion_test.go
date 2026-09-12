package compiler

import (
	"strings"
	"testing"
)

// A self-recursive function extracts by structural recursion on the fuel
// (docs/spec/95-extraction.md section 2); mutual recursion still fails
// closed with the cycle named.
func TestLeanExtractionRecursion(t *testing.T) {
	src := `
countdown: (x: u32, acc: u32): u32 = x == u32(0) ? acc | countdown(x - u32(1), acc + x)

sum_to: theorem (n: u8) { countdown(u32(n), u32(0)) == countdown(u32(n), u32(0)) }

main: (): i32 = i32_bits_u32(countdown(u32(4), u32(0)))
`
	text, err := New().WithSource("rec.oak", src).EmitLeanRoots("Oak.Recursion", []string{"sum_to"}).Get()
	if err != nil {
		t.Fatalf("extraction failed: %v", err)
	}
	for _, want := range []string{
		"def countdown (x : UInt32) (acc : UInt32) : Nat → Option (UInt32)",
		"  | 0 => none",
		"  | fuel + 1 => do",
		"countdown (x - (1 : UInt32)) (acc + x) fuel",
	} {
		if !strings.Contains(text, want) {
			t.Errorf("projection lacks %q:\n%s", want, text)
		}
	}
	mutual := `
even: (x: u32): Bool = x == u32(0) ? true | odd(x - u32(1))
odd: (x: u32): Bool = x == u32(0) ? false | even(x - u32(1))
main: (): i32 = 0
`
	if _, err := New().WithSource("mutual.oak", mutual).EmitLeanRoots("Oak.Recursion", []string{"even"}).Get(); err == nil ||
		!strings.Contains(err.Error(), "recursive") {
		t.Fatalf("mutual recursion must fail closed, got %v", err)
	}
}
