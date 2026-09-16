package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/optir"
)

const optIRIdentityProgram = `
state: u32 = u32(0)

touch: (value: u32): u32 {
  state = value
  value
}

next: (): u32 {
  state = state + u32(1)
  state
}

annihilate: (value: u32): u32 = value * u32(0) + u32(42)
subtract_self: (value: i64): i64 = value - value
ones: (value: u8): u8 = value | u8(255)
reflexive_branch: (value: u64): u32 = value <= value ? u32(42) | u32(17)
keep_effect: (value: u32): u32 = touch(value) * u32(0) + u32(42)
distinct_calls: (): Bool = next() == next()

zero_loop: (n: u32): u32 {
  i: u32 = u32(0)
  while i < (n ^ n) {
    state = u32(99)
    i = i + u32(1)
  }
  u32(42)
}

main: (): i32 {
  state = u32(0)
  scalar: Bool = annihilate(u32(4294967295)) == u32(42) && subtract_self(i64(-9223372036854775807) - i64(1)) == i64(0)
  bits: Bool = ones(u8(0)) == u8(255) && ones(u8(128)) == u8(255)
  control: Bool = reflexive_branch(u64(18446744073709551615)) == u32(42) && zero_loop(u32(4294967295)) == u32(42) && state == u32(0)
  effect: Bool = keep_effect(u32(7)) == u32(42) && state == u32(7)
  calls: Bool = !distinct_calls() && state == u32(9)
  scalar && bits && control && effect && calls ? i32(42) | i32(1)
}
`

func TestOptIRConstantIdentitiesReachFinalCandidates(t *testing.T) {
	module, err := New().WithSource("identities.oak", optIRIdentityProgram).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"annihilate", "subtract_self", "ones", "reflexive_branch", "keep_effect", "zero_loop"} {
		function, ok := optIRFunction(module, name)
		if !ok || len(function.SCCPRewrite.RewrittenValues) == 0 {
			t.Fatalf("%s not folded: %+v, refusals %+v", name, function.SCCPRewrite, module.Refusals)
		}
		cfg := function.LoopInvariant
		if function.CheckedMemory.HasMemoryEffects() {
			cfg = function.MemoryCleanup.CFG
		}
		if len(cfg.Blocks) != 1 {
			t.Fatalf("%s retained unnecessary control flow: %+v", name, cfg)
		}
		calls := 0
		for _, operation := range cfg.Blocks[0].Operations {
			switch operation.Code {
			case optir.OpCall:
				calls++
			case optir.OpConstInt:
			default:
				t.Fatalf("%s retained identity arithmetic or dead loop effects: %+v", name, operation)
			}
		}
		wantCalls := 0
		if name == "keep_effect" {
			wantCalls = 1
		}
		if calls != wantCalls {
			t.Fatalf("%s calls = %d, want %d", name, calls, wantCalls)
		}
	}
	distinct, ok := optIRFunction(module, "distinct_calls")
	if !ok {
		t.Fatalf("distinct_calls not projected: %+v", module.Refusals)
	}
	calls, comparisons := 0, 0
	for _, block := range distinct.MemoryCleanup.CFG.Blocks {
		for _, operation := range block.Operations {
			switch operation.Code {
			case optir.OpCall:
				calls++
			case optir.OpEqual:
				comparisons++
			}
		}
	}
	if calls != 2 || comparisons != 1 {
		t.Fatalf("two evaluations of the same callee were conflated: calls=%d comparisons=%d", calls, comparisons)
	}
}
