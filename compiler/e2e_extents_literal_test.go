package compiler

import (
	"strings"
	"testing"
)

// Extent facts, fourth increment (docs/spec/50-borrowing.md): literal
// bounds, scaled indices, lower bounds from a loop's exit, subtraction
// under both bounds, and masked indices. These are the accesses the hash
// kernels perform; each proven access reads the owned array directly, and
// each near miss below stays checked.
func TestE2EExtentLiteralBounds(t *testing.T) {
	src := `
TABLE: [256]u32

schedule: (block: [64]u8): u32 {
  w: [64]u32
  i: u32 = 0
  while i < u32(16) {
    w[i] = (u32(block[i * u32(4)]) << u32(24)) | (u32(block[i * u32(4) + u32(1)]) << u32(16)) | (u32(block[i * u32(4) + u32(2)]) << u32(8)) | u32(block[i * u32(4) + u32(3)])
    i = i + u32(1)
  }
  while i < u32(64) {
    w[i] = w[i - u32(16)] + w[i - u32(7)] + w[i - u32(2)]
    i = i + u32(1)
  }
  w[u32(63)]
}

lookup: (x: u32): u32 = TABLE[x & u32(255)]

main: (): i32 {
  block: [64]u8
  block[u32(63)] = u8(3)
  s: u32 = schedule(block)
  t: u32 = lookup(u32(4096))
  i32_bits_u32(s - u32(6345) + t + u32(42))
}
`
	output, err := New().WithSource("extents4.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	// Every access in schedule and lookup is proven: no checked owned-array
	// access remains, and the proven ones read the .v member directly.
	if got := strings.Count(output, "oak_index( "); got != 0 {
		t.Fatalf("expected no checked owned-array reads, found %d:\n%s", got, output)
	}
	if got := strings.Count(output, "oak_store( "); got != 0 {
		t.Fatalf("expected no checked owned-array stores, found %d:\n%s", got, output)
	}
	code, abnormal := buildAndRun(t, "extents4", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}

	// Near misses stay checked: an offset past the literal bound, a scaled
	// index reaching the length, a subtraction below the lower bound, a
	// mask as wide as the table, a body that resets the counter, and a
	// loop with a break (no exit fact).
	over := `
TABLE: [256]u32

misses: (block: [64]u8): u32 {
  w: [64]u32
  i: u32 = 0
  while i < u32(16) {
    w[i] = u32(block[i * u32(4) + u32(4)])
    i = i + u32(1)
  }
  while i < u32(64) {
    w[i] = w[i - u32(17)]
    i = i + u32(1)
  }
  j: u32 = 0
  while j < u32(16) {
    j = u32(0)
    w[j + u32(48)] = u32(1)
    j = j + u32(1)
  }
  k: u32 = 0
  while k < u32(16) {
    k < u32(8) ? { break }
    k = k + u32(1)
  }
  while k < u32(64) {
    w[k] = w[k - u32(16)]
    k = k + u32(1)
  }
  w[u32(63)]
}

wide: (x: u32): u32 = TABLE[x & u32(256)]

main: (): i32 = 0
`
	output, err = New().WithSource("extents4over.oak", over).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	// block[i*4+4], w[i-17], w[k-16] without the exit fact, TABLE[x & 256]:
	// four checked reads; w[j+48] after the reset is a checked store.
	if got := strings.Count(output, "oak_index( "); got != 4 {
		t.Fatalf("expected 4 checked owned-array reads, found %d:\n%s", got, output)
	}
	if got := strings.Count(output, "oak_store( "); got != 1 {
		t.Fatalf("expected 1 checked owned-array store, found %d:\n%s", got, output)
	}
}
