package compiler

import (
	"strings"
	"testing"
)

// Package state threads through the extraction (docs/spec/95-extraction.md
// section 3, "Sixth"; the ml pilot's F25): a global some function assigns
// is a parameter of every function that touches it and a result of every
// function that writes it, after the threaded spans; loops thread it as a
// variable; the initializer is NAME_init.
func TestE2ELeanExtractsPackageState(t *testing.T) {
	src := `package main

counter: u32 = 0
table: [4]u32 = [1, 2, 3, 4]
seen: u32

bump: (): () = {
  counter = counter + 1
}

set_at: (i: u32, v: u32): () = {
  table[i] = v
}

peek: (i: u32): u32 = table[i]

drive: (n: u32): u32 = {
  k: u32 = 0
  while k < n {
    bump()
    set_at(k % 4, k)
    k = k + 1
  }
  seen = counter
  counter + peek(0)
}

main: (): i32 = {
  r: u32 = drive(6)
  i32_bits_u32(r + seen)
}
`
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
	// The program runs: 6 bumps, table[0] ends at 4 (k = 4), drive returns 10, seen is 6.
	if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); abnormal || code != 16 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	text, err := New().WithPackageDir(root).EmitLeanRoots("Oak.StateTest", []string{"drive"}).Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"def counter_init : UInt32 := (0 : UInt32)",
		"def table_init : Array UInt32 :=",
		"def seen_init : UInt32 := 0",
		"def bump (counter : UInt32) (fuel : Nat) : Option (Unit × UInt32) := do",
		"def set_at (i : UInt32) (v : UInt32) (table : Array UInt32) (fuel : Nat) : Option (Unit × Array UInt32) := do",
		"def peek (i : UInt32) (table : Array UInt32) (fuel : Nat) : Option (UInt32) := do",
		"def drive (n : UInt32) (counter : UInt32) (table : Array UInt32) (seen : UInt32) (fuel : Nat) : Option (UInt32 × UInt32 × Array UInt32 × UInt32) := do",
		"← bump counter fuel",
		"← set_at (k % (4 : UInt32)) k table fuel",
		"← peek (0 : UInt32) table fuel",
	} {
		if !strings.Contains(text, want) {
			t.Fatalf("missing %q in:\n%s", want, text)
		}
	}
	// The loop helper threads the state it reaches through calls.
	if !strings.Contains(text, "def drive.loop1") || !strings.Contains(text, "(counter : UInt32)") {
		t.Fatalf("the loop threads the state its calls touch:\n%s", text)
	}
	// Package state is never a folded constant.
	if strings.Contains(text, "def counter : UInt32") {
		t.Fatalf("package state must not be rendered as a constant:\n%s", text)
	}
}
