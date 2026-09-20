package compiler

// `break` in a verified loop (docs/spec/94-assembler.md §9 "Loops that
// break"): the machine side reads a body branch to the loop's exit label
// as an iteration that sets a carried one-bit flag, the Oak side lowers
// the loop to the same flag form, and the coupling pairs the two flags.
// The OS page walkers' scans (grant, timer) wrote a done flag by hand for
// want of this; a break proves like the flag did.

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

const nativeBreakProgram = `Regime: type = struct {
  slots: [8]u8
  count: u32
}

find_slot: (slots: [8]u8, want: u8): u32 {
  found: u32 = u32(8)
  i: u32 = u32(0)
  while i < u32(8) {
    hit: Bool = slots[i] == want
    hit ? { found = i; break } | {}
    i = i + u32(1)
  }
  found
}

first_free: (s: [*]Regime, dom: u32): u32 {
  found: u32 = u32(64)
  i: u32 = u32(0)
  while i < s[dom].count {
    free: Bool = s[dom].slots[i & u32(7)] == u8(0)
    free ? { found = i; break } | {}
    i = i + u32(1)
  }
  found
}

claim_first: (s: [*]Regime, dom: u32): u32 {
  found: u32 = u32(64)
  i: u32 = u32(0)
  while i < s[dom].count {
    free: Bool = s[dom].slots[i & u32(7)] == u8(0)
    free ? {
      s[dom].slots[i & u32(7)] = u8(9)
      found = i
      break
    } | {}
    s[dom].slots[i & u32(7)] = u8(2)
    i = i + u32(1)
  }
  found
}

count_pairs: (s: [*]Regime, dom: u32): u32 {
  pairs: u32 = u32(0)
  i: u32 = u32(0)
  while i < u32(8) {
    j: u32 = u32(0)
    while j < s[dom].count {
      same: Bool = s[dom].slots[i] == s[dom].slots[j & u32(7)]
      same ? { pairs = pairs + u32(1); break } | {}
      j = j + u32(1)
    }
    i = i + u32(1)
  }
  pairs
}

main: (): i32 {
  slots: [8]u8
  slots[3] = u8(7)
  regimes: [1]Regime
  s: [*]Regime = span(&regimes)
  s[0].count = u32(6)
  s[0].slots[0] = u8(1)
  s[0].slots[1] = u8(1)
  a: u32 = find_slot(slots, u8(7)) * u32(100) + find_slot(slots, u8(9)) * u32(10) + first_free(s, u32(0))
  b: u32 = claim_first(s, u32(0))
  c: u32 = count_pairs(s, u32(0))
  ok: Bool = a == u32(382) && b == u32(2) && s[0].slots[0] == u8(2) && s[0].slots[2] == u8(9) && c == u32(8)
  ok ? 42 | 1
}
`

// The RV64 lane lowers scalars and plain spans (no array parameters or
// record spans yet): a counted scan over arithmetic and a span search.
const nativeBreakSpanProgram = `first_hit: (n: u32, k: u32): u32 {
  i: u32 = u32(0)
  while i < n {
    hit: Bool = ((i + k) & u32(7)) == u32(3)
    hit ? { break } | {}
    i = i + u32(1)
  }
  i
}

find_in: (v: [*]u32, want: u32): u32 {
  found: u32 = len(v)
  i: u32 = u32(0)
  while i < len(v) {
    hit: Bool = v[i] == want
    hit ? { found = i; break } | {}
    i = i + u32(1)
  }
  found
}

main: (): i32 {
  words: [6]u32
  words[4] = u32(77)
  v: [*]u32 = span(&words)
  ok: Bool = first_hit(u32(20), u32(5)) == u32(6) && first_hit(u32(2), u32(5)) == u32(2) && find_in(v, u32(77)) == u32(4) && find_in(v, u32(5)) == u32(6)
  ok ? 42 | 1
}
`

var breakSpanUnits = []string{"first_hit", "find_in"}

func nativeBreakUnits(t *testing.T, program string, tgt *target.Target) (map[string]*asm.Function, string, Compilation) {
	t.Helper()
	var infos []string
	comp := New().WithSource("brk.oak", program).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	if tgt != nil {
		comp = comp.WithTarget(*tgt)
	}
	model, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v\n%s", err, strings.Join(infos, "\n"))
	}
	units := map[string]*asm.Function{}
	for _, fn := range model.AsmFunctions {
		units[fn.Name] = fn
	}
	return units, strings.Join(infos, "\n"), comp
}

var breakUnits = []string{"find_slot", "first_free", "claim_first", "count_pairs"}

func TestE2ENativeBreakProven(t *testing.T) {
	requireArm64Host(t)
	units, joined, comp := nativeBreakUnits(t, nativeBreakProgram, nil)
	for _, name := range breakUnits {
		if units[name] == nil {
			t.Fatalf("%s was not lowered natively:\n%s", name, joined)
		}
		if !strings.Contains(joined, "asm unit "+name+": proven") {
			t.Fatalf("%s must be proven with its break:\n%s", name, joined)
		}
	}
	// The flag is the coupling's, not the machine's: no register carries it.
	if !strings.Contains(joined, "#brk") {
		t.Fatalf("the break flag must be coupled:\n%s", joined)
	}
	_, code, abnormal := buildAndRunFrom(t, "brk", comp)
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	_, joined, comp = nativeBreakUnits(t, nativeBreakSpanProgram, nil)
	for _, name := range breakSpanUnits {
		if !strings.Contains(joined, "asm unit "+name+": proven") {
			t.Fatalf("%s must be proven with its break:\n%s", name, joined)
		}
	}
	_, code, abnormal = buildAndRunFrom(t, "brk_span", comp)
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
}

func TestE2ENativeRV64BreakProven(t *testing.T) {
	tgt := target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}
	_, joined, _ := nativeBreakUnits(t, nativeBreakSpanProgram, &tgt)
	for _, name := range breakSpanUnits {
		if !strings.Contains(joined, "asm unit "+name+": proven") {
			t.Fatalf("%s must be proven with its break on the RV64 lane:\n%s", name, joined)
		}
	}
}
