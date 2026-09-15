package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
)

// If-conversion (docs/spec/94-assembler.md §9 "If-conversion";
// nativegen/select.go): a conditional chain over one comparison whose arms
// only assign register-homed integer locals lowers as one compare and a
// select per variable. The shapes are asserted on the lowered
// instructions — no branch to an else label in the converted functions —
// and the values against the C backend: a three-arm chain with an empty
// arm, a signed comparison, two variables in one arm, a variable assigned
// in two arms, two chains whose second arm can never fire.
const nativeSelectProgram = `
clamp_step: (x: i32, lo: i32, hi: i32): i32 {
  y: i32 = x
  x < lo ? { y = lo } | x > hi ? { y = hi } | { }
  y
}

order: (a: u32, b: u32): u32 {
  small: u32 = 0
  big: u32 = 0
  a < b ? {
    small = a
    big = b
  } | {
    small = b
    big = a
  }
  big * u32(1000) + small
}

sign_code: (v: i32): u32 {
  code: u32 = 7
  v == 0 ? { code = 1 } | v < 0 ? { code = 2 } | { code = 3 }
  code
}

dead_arm: (a: u32, b: u32): u32 {
  r: u32 = 0
  a != b ? { r = 5 } | a < b ? { r = 9 } | { r = 1 }
  r
}

pick_if: (a: u32, b: u32): u32 {
  m: u32 = b
  n: u32 = a
  a >= b ? { m = a } | a == b ? { m = 77 } | { n = b }
  m + n
}

count_hits: (keys: []u64, target: u64): u32 {
  lo: u32 = 0
  hi: u32 = len(keys)
  found: Bool = false
  steps: u32 = 0
  while lo < hi && !found {
    mid: u32 = lo + (hi - lo) / u32(2)
    k: u64 = keys[mid]
    k == target ? { found = true }
    | k < target ? { lo = mid + u32(1) }
    | { hi = mid }
    steps = steps + u32(1)
  }
  found ? { steps + u32(100) } | { steps }
}

tally: (v: []u32): u32 {
  hits: u32 = 0
  i: u32 = 0
  while i < len(v) {
    big: Bool = v[i] > u32(100)
    big ? { hits = hits + u32(1) }
    i = i + u32(1)
  }
  hits
}

main: (): i32 {
  keys: [8]u64 = [8]u64{ 1, 2, 3, 5, 8, 13, 21, 34 }
  vals: [4]u32 = [4]u32{ 5, 500, 105, 1 }
  // clamp_step: 5 (inside), -3 -> 0, 12 -> 9; order(4, 9) = 9004; sign_code(0/-5/5) = 1, 2, 3;
  // dead_arm(2, 3) = 5, (4, 4) = 1; pick_if(5, 3) = 5 + 5 (its equal arm never fires), pick_if(2, 6) = 6 + 6;
  // count_hits finds 13 in 3 steps (mid 3 -> 5 -> 5), misses 4 in 3 steps.
  s: i32 = clamp_step(5, 0, 9) + clamp_step(-3, 0, 9) + clamp_step(12, 0, 9)
  t: u32 = order(u32(4), u32(9)) + sign_code(0) + sign_code(-5) * u32(10) + sign_code(5) * u32(100)
  u: u32 = dead_arm(u32(2), u32(3)) + dead_arm(u32(4), u32(4)) * u32(10) + pick_if(u32(5), u32(3)) + pick_if(u32(2), u32(6))
  v: u32 = count_hits(view(&keys), u64(13)) + count_hits(view(&keys), u64(4)) * u32(1000)
  // tally counts the two values above 100.
  w: u32 = tally(view(&vals))
  // (9004 + 1 + 20 + 300) + (5 + 10 + 10 + 12) + (103 + 3000) + 2 = 12467, 179 modulo 256; plus 14 the exit code is 193.
  i32_bits_u32((t + u + v + w) & u32(255)) + s
}
`

func TestE2ENativeIfConversion(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("select.oak", nativeSelectProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	units := map[string]*asm.Function{}
	for _, fn := range model.AsmFunctions {
		units[fn.Name] = fn
	}
	for _, name := range []string{"clamp_step", "order", "sign_code", "dead_arm", "pick_if", "count_hits", "tally"} {
		fn, ok := units[name]
		if !ok {
			t.Fatalf("%s was not lowered natively:\n%s", name, strings.Join(infos, "\n"))
		}
		selects := 0
		for _, item := range fn.Items {
			ins, isIns := item.(asm.Instruction)
			if !isIns {
				continue
			}
			if ins.Mnemonic == "csel" || ins.Mnemonic == "csinc" || ins.Mnemonic == "cinc" {
				selects++
			}
			if ins.Mnemonic == "b." {
				if target, isSym := ins.Operands[0].(asm.Symbol); isSym && strings.HasPrefix(target.Name, "else") {
					t.Errorf("%s branches to an arm the chain should select: b.%s %s", name, ins.Cond, target.Name)
				}
			}
		}
		if selects == 0 {
			t.Errorf("%s must lower its chain as selects", name)
		}
	}
	// count_hits's loop is one block: the header's two exits, the back
	// edge, and no other branch — or, bottom-tested (docs/spec/94-assembler.md
	// §9 "Bottom-tested loops"), the tail's exit and its conditional back
	// edge, the second exit test having become the back edge.
	branches := 0
	for _, ins := range loopBody(units["count_hits"]) {
		if ins.Mnemonic == "b." || ins.Mnemonic == "b" || ins.Mnemonic == "cbz" || ins.Mnemonic == "cbnz" {
			branches++
		}
	}
	if want := 3 - nativegen.RotatedLoops(units["count_hits"]); branches != want {
		t.Errorf("count_hits's loop must hold exactly its exits and the back edge (%d branches), got %d", want, branches)
	}
	// `found = true` is a csinc from wzr, no constant built in the loop;
	// `hits = hits + u32(1)` under a Bool is a cinc after `cmp wB, #0`.
	mnemonics := func(name string) map[string]int {
		counts := map[string]int{}
		for _, ins := range loopBody(units[name]) {
			counts[ins.Mnemonic]++
		}
		return counts
	}
	if counts := mnemonics("count_hits"); counts["csinc"] != 1 || counts["movz"] != 0 {
		t.Errorf("count_hits's flag must be one csinc with no constant in the loop, got %v", counts)
	}
	if counts := mnemonics("tally"); counts["cinc"] != 1 || counts["cbz"]+counts["cbnz"] != 0 {
		t.Errorf("tally's conditional increment must be one cinc with no branch on the Bool, got %v", counts)
	}
	_, code, abnormal := buildAndRunFrom(t, "native_select", comp)
	if abnormal || code != 193 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 193\n%s", code, abnormal, strings.Join(infos, "\n"))
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_select_c", New().WithSource("select.oak", nativeSelectProgram)); abnormal || code != 193 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 193", code, abnormal)
	}
}
