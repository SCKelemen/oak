package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/nativegen"
)

// Consume a span base on its last use, the register-allocation shape blocked
// in the OS stage-2 translate. The selected machine body must keep the
// in-place UMADDL and be proven against the original Oak body.
func TestE2ENativeInPlaceElementAllocation(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_NATIVE_ONLY", "translate")
	const source = `
// The OS pilot's two-level 16 KiB translation shape and record layout.
entries: u32 = u32(2048)
page_size: u64 = u64(16384)
l0_shift: u64 = u64(25)
l0_mask: u64 = u64(127)
l1_shift: u64 = u64(14)
l1_mask: u64 = u64(2047)
ipa_limit: u64 = u64(0x100000000)
desc_valid: u64 = u64(1)
desc_pa_mask: u64 = u64(0x0000FFFFFFFFF000)
Regime: type = struct {
  pages: [49152]u64
  free_stack: [24]u16
  free_count: u16
  high_water: u16
  entry_count: [24]u16
  root: u16
  mapped_pages: u32
  pool_base: u64
  pad: [2033]u64
}
trans_result: u64
cell: (table: u16, idx: u32): u32 { u32(table) * entries + idx }
pa_index: (pool_base: u64, pa: u64): u16 { u16_trunc_u64((pa - pool_base) / page_size) }
translate: (s: [*]Regime, dom: u32, ipa: u64): u8 {
  trans_result = u64(0)
  r: u8 = u8(1)
  oor: Bool = ipa >= ipa_limit
  r = oor ? u8(0) | r
  go: Bool = r == u8(1)
  go ? {
    table: u16 = s[dom].root
    idx0: u64 = (ipa >> l0_shift) & l0_mask
    d0: u64 = s[dom].pages[cell(table, u32_trunc_u64(idx0))]
    inv0: Bool = (d0 & desc_valid) == u64(0)
    r = inv0 ? u8(0) | r
    cont: Bool = r == u8(1)
    cont ? {
      leaf: u16 = pa_index(s[dom].pool_base, d0 & desc_pa_mask)
      idx1: u64 = (ipa >> l1_shift) & l1_mask
      d: u64 = s[dom].pages[cell(leaf, u32_trunc_u64(idx1))]
      inv1: Bool = (d & desc_valid) == u64(0)
      r = inv1 ? u8(0) | r
      fin: Bool = r == u8(1)
      trans_result = fin ? ((d & desc_pa_mask & ^(page_size - u64(1))) | (ipa & (page_size - u64(1)))) | trans_result
    } | { }
  } | { }
  r
}
main: (): i32 {
  regimes: [1]Regime
  regimes[0].pages[0] = u64(16385)
  regimes[0].pages[2048] = u64(32769)
  assert(translate(span(&regimes), u32(0), u64(123)) == u8(1))
  assert(trans_result == u64(32891))
  assert(translate(span(&regimes), u32(0), u64(0x100000000)) == u8(0))
  assert(trans_result == u64(0))
  regimes[0].pages[2048] = u64(0)
  assert(translate(span(&regimes), u32(0), u64(123)) == u8(0))
  regimes[0].pages[0] = u64(0)
  assert(translate(span(&regimes), u32(0), u64(123)) == u8(0))
  42
}
`
	comp := New().WithSource("inplace_element.oak", source).WithNativeBodies().WithNativeAsm()
	comp.options.InlineHelpers = true // the CLI's native pilot configuration
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	verdict := model.NativeVerdicts["translate"]
	if verdict.Kind != asm.VerdictProven {
		t.Fatalf("translate must be proven: %s (%s)", verdict.Kind, verdict.Message)
	}
	var function *asm.Function
	for _, fn := range model.AsmFunctions {
		if fn.Name == "translate" {
			function = fn
		}
	}
	if function == nil {
		t.Fatal("missing native translate")
	}
	// The element address either consumes its base (`umaddl xB, wI, wK,
	// xB`, the admission of docs/spec/94-assembler.md "An element address
	// may consume its inputs") or is folded into the load's register
	// offset (`ldr xD, [xB, wI, uxtw #3]`, the shape the constant
	// materialization of 2026-09-17 leaves): either way no separate
	// address instruction and no copy of the base remain.
	inPlace := false
	for _, item := range function.Items {
		instruction, ok := item.(asm.Instruction)
		if !ok {
			continue
		}
		switch instruction.Mnemonic {
		case "umaddl":
			if len(instruction.Operands) != 4 {
				continue
			}
			dest, isDest := instruction.Operands[0].(asm.Register)
			base, isBase := instruction.Operands[3].(asm.Register)
			inPlace = inPlace || (isDest && isBase && dest.Num == base.Num)
		case "ldr":
			if len(instruction.Operands) == 2 {
				if memory, isMemory := instruction.Operands[1].(asm.Memory); isMemory && memory.Index != nil && memory.Shift == 3 {
					inPlace = true
				}
			}
		}
	}
	if !inPlace {
		t.Fatalf("the element access must consume its base or fold into the load's register offset:\n%s", nativegen.Describe(function))
	}
	_, code, abnormal := buildAndRunFrom(t, "inplace_element", comp)
	if abnormal || code != 42 {
		t.Fatalf("native: exit=(%d, abnormal=%v), want 42", code, abnormal)
	}
	_, code, abnormal = buildAndRunFrom(t, "inplace_element_c", New().WithSource("inplace_element.oak", source))
	if abnormal || code != 42 {
		t.Fatalf("C: exit=(%d, abnormal=%v), want 42", code, abnormal)
	}
}
