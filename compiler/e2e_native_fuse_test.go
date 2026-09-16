package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
)

// Peephole fusion (machine.Fuse, the `fuse` candidate): the binary
// search's inner loop folds its shift into the add's shifted operand and
// its increment into a csinc — clang's shape for the same loop — and the
// body still agrees with the C backend and earns at least the evidence
// verdict of its plain form.
const nativeFuseProgram = `
search: (keys: []u64, target: u64): u32 {
  lo: u32 = 0
  hi: u32 = len(keys)
  found: Bool = false
  while lo < hi && !found {
    mid: u32 = lo + (hi - lo) / u32(2)
    k: u64 = keys[mid]
    k == target ? { found = true }
    | k < target ? { lo = mid + u32(1) }
    | { hi = mid }
  }
  found ? u32(1) | u32(0)
}

main: (): i32 {
  keys: [9]u64 = [9]u64{ 2, 3, 5, 7, 11, 13, 17, 19, 23 }
  hits: u32 = u32(0)
  t: u64 = u64(0)
  while t < u64(25) {
    hits = hits + search(view(&keys), t)
    t = t + u64(1)
  }
  i32_bits_u32(hits * u32(4) + u32(2))
}
`

func TestE2ENativeFuse(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("fuse.oak", nativeFuseProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v\n%s", err, strings.Join(infos, "\n"))
	}
	joined := strings.Join(infos, "\n")
	var unit *asm.Function
	for _, fn := range model.AsmFunctions {
		if fn.Name == "search" {
			unit = fn
		}
	}
	if unit == nil {
		t.Fatalf("search was not lowered natively:\n%s", joined)
	}
	if n := nativegen.Fused(unit); n < 2 {
		t.Errorf("search must fuse its shift and its increment, fused %d:\n%s\n%s", n, nativegen.Describe(unit), joined)
	}
	shifted, incremented := false, false
	for _, item := range unit.Items {
		ins, ok := item.(asm.Instruction)
		if !ok {
			continue
		}
		if ins.Mnemonic == "add" && len(ins.Operands) == 3 {
			if _, isShifted := ins.Operands[2].(asm.Shifted); isShifted {
				shifted = true
			}
		}
		if ins.Mnemonic == "csinc" && len(ins.Operands) == 4 {
			if r, isReg := ins.Operands[2].(asm.Register); isReg && !r.ZeroRegister() {
				incremented = true
			}
		}
	}
	if !shifted || !incremented {
		t.Errorf("search's loop must carry a shifted add and a csinc (shifted %v, csinc %v):\n%s", shifted, incremented, nativegen.Describe(unit))
	}
	if strings.Contains(joined, "disagrees") {
		t.Fatalf("a mismatch:\n%s", joined)
	}
	_, code, abnormal := buildAndRunFrom(t, "native_fuse", comp)
	if abnormal || code != 9*4+2 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want %d\n%s", code, abnormal, 9*4+2, joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_fuse_c", New().WithSource("fuse.oak", nativeFuseProgram)); abnormal || code != 9*4+2 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want %d", code, abnormal, 9*4+2)
	}
}
