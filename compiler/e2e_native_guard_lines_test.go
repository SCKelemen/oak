package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// A refused elision falls back one source line at a time
// (docs/spec/94-assembler.md §9 "Check elision"): in a search that cuts
// its range in thirds the outer loop's probe read is proven and admitted
// by the seam checker off the loop's own exit test, while the inner
// loop's key read at `lo + (hi - lo) / 3` is proven by the typechecker's
// decreasing-bound law through a division the checker has no rule for at
// the seam (its midpoint rule reads the halving shift, §7 "Bounds through
// arithmetic"); the compiler keeps the guard of the key read's line and
// leaves the probe read unguarded, and the verifier still judges the
// body. The C backend's realization is the oracle for the value.
const nativeGuardLinesProgram = `
count_hits: (keys: []u64, probes: []u64): u32 {
  hits: u32 = 0
  p: u32 = 0
  while p < len(probes) {
    target: u64 = probes[p]
    lo: u32 = 0
    hi: u32 = len(keys)
    found: Bool = false
    while lo < hi && !found {
      mid: u32 = lo + (hi - lo) / u32(3)
      k: u64 = keys[mid]
      k == target ? { found = true }
      | k < target ? { lo = mid + u32(1) }
      | { hi = mid }
    }
    found ? { hits = hits + u32(1) }
    p = p + u32(1)
  }
  hits
}

main: (): i32 {
  keys: [8]u64 = [u64(1), u64(3), u64(5), u64(7), u64(9), u64(11), u64(13), u64(15)]
  probes: [5]u64 = [u64(3), u64(4), u64(9), u64(15), u64(16)]
  i32_bits_u32(count_hits(view(&keys), view(&probes))) + 39
}
`

func TestE2ENativeGuardLines(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("guards.oak", nativeGuardLinesProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	// The chain `k == target ? … | k < target ? …` compares once: either
	// the else label's first instruction is the branch reading the
	// guard's flags (docs/spec/94-assembler.md §9 "Condition selection")
	// or the chain is one compare and selects (§9 "If-conversion").
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	reused, selected := false, false
	for _, f := range model.AsmFunctions {
		if f.Name != "count_hits" {
			continue
		}
		for i := 1; i < len(f.Items); i++ {
			if instr, isInstr := f.Items[i].(asm.Instruction); isInstr && (instr.Mnemonic == "csel" || instr.Mnemonic == "csinc") {
				selected = true
			}
			if _, isLabel := f.Items[i-1].(asm.Label); !isLabel {
				continue
			}
			if instr, isInstr := f.Items[i].(asm.Instruction); isInstr && instr.Mnemonic == "b." {
				reused = true
			}
		}
	}
	if !reused && !selected {
		t.Errorf("the key comparison must compare once: the else arm reusing the guard's compare, or the chain selecting")
	}
	_, code, abnormal := buildAndRunFrom(t, "native_guard_lines", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native guard lines: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	// Both reads are proven: `probes[p]` under the loop's test, and
	// `keys[mid]` under the ceiling `hi <= len(keys)` that survives the
	// search loop (docs/spec/94-assembler.md §9, "a ceiling that survives
	// a loop", 2026-09-17). Until then the checker refused the second
	// elision the typechecker had licensed, and this fixture pinned the
	// fallback that keeps that guard and names its line; a guard the
	// checker cannot admit now takes a fixture where it lags the
	// typechecker, and none is at hand.
	if !strings.Contains(joined, "count_hits: 2 element guard(s) elided under the checker's own facts") {
		t.Errorf("both of count_hits's reads must be elided; diagnostics:\n%s", joined)
	}
	if strings.Contains(joined, "count_hits keeps its element guards") {
		t.Errorf("the body must not fall back to every guard; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit count_hits: proven equal to its Oak body") && !strings.Contains(joined, "asm unit count_hits: agrees with its Oak body") {
		t.Errorf("count_hits must keep its verdict; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_guard_lines_c", New().WithSource("guards.oak", nativeGuardLinesProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
